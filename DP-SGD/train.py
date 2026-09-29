#!/usr/bin/env python3
"""Train a small CIFAR-10 model with threshold or personalized DP-SGD."""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import random
import time
from pathlib import Path

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F
from opacus import GradSampleModule
from opacus.data_loader import DPDataLoader
from opacus.validators import ModuleValidator
from torch.utils.data import DataLoader, Dataset, Subset
from torchvision import datasets, models, transforms

from privacy import PROFILE_NAMES, make_profile
from sampled_privacy import (
    SampledMechanism,
    calibrate_sampled_mechanism,
)


CIFAR_MEAN = (0.4914, 0.4822, 0.4465)
CIFAR_STD = (0.2470, 0.2435, 0.2616)


class IndexedPrivateDataset(Dataset):
    def __init__(self, dataset: Dataset, epsilons: np.ndarray):
        if len(dataset) != len(epsilons):
            raise ValueError("dataset and privacy profile have different lengths")
        self.dataset = dataset
        self.epsilons = epsilons

    def __len__(self) -> int:
        return len(self.dataset)

    def __getitem__(self, index: int):
        image, target = self.dataset[index]
        return (
            image,
            torch.as_tensor(target, dtype=torch.long),
            torch.tensor(self.epsilons[index], dtype=torch.float64),
        )


class SmallCifarCNN(nn.Module):
    """Compact GroupNorm CNN; no batch-dependent normalization."""

    def __init__(self) -> None:
        super().__init__()
        self.features = nn.Sequential(
            nn.Conv2d(3, 64, 3, padding=1, bias=False),
            nn.GroupNorm(8, 64),
            nn.ReLU(inplace=False),
            nn.Conv2d(64, 64, 3, padding=1, bias=False),
            nn.GroupNorm(8, 64),
            nn.ReLU(inplace=False),
            nn.MaxPool2d(2),
            nn.Conv2d(64, 128, 3, padding=1, bias=False),
            nn.GroupNorm(16, 128),
            nn.ReLU(inplace=False),
            nn.Conv2d(128, 128, 3, padding=1, bias=False),
            nn.GroupNorm(16, 128),
            nn.ReLU(inplace=False),
            nn.MaxPool2d(2),
            nn.Conv2d(128, 256, 3, padding=1, bias=False),
            nn.GroupNorm(32, 256),
            nn.ReLU(inplace=False),
            nn.AdaptiveAvgPool2d(1),
        )
        self.classifier = nn.Linear(256, 10)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.classifier(self.features(x).flatten(1))


def replace_batch_norm(module: nn.Module) -> nn.Module:
    for name, child in list(module.named_children()):
        if isinstance(child, nn.BatchNorm2d):
            groups = min(32, child.num_features)
            while child.num_features % groups:
                groups -= 1
            setattr(module, name, nn.GroupNorm(groups, child.num_features))
        else:
            replace_batch_norm(child)
    return module


def make_model(name: str) -> nn.Module:
    if name == "smallcnn":
        model = SmallCifarCNN()
    elif name == "resnet18":
        model = models.resnet18(weights=None, num_classes=10)
        model.conv1 = nn.Conv2d(3, 64, 3, stride=1, padding=1, bias=False)
        model.maxpool = nn.Identity()
        model = replace_batch_norm(model)
    else:
        raise ValueError(f"unknown model {name}")
    errors = ModuleValidator.validate(model, strict=False)
    if errors:
        raise RuntimeError(f"model is not compatible with per-sample gradients: {errors}")
    return model


def seed_everything(seed: int) -> None:
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)


def make_datasets(args: argparse.Namespace):
    eval_transform = transforms.Compose(
        [transforms.ToTensor(), transforms.Normalize(CIFAR_MEAN, CIFAR_STD)]
    )
    if args.augmentation:
        train_transform = transforms.Compose(
            [
                transforms.RandomCrop(32, padding=4),
                transforms.RandomHorizontalFlip(),
                transforms.ToTensor(),
                transforms.Normalize(CIFAR_MEAN, CIFAR_STD),
            ]
        )
    else:
        train_transform = eval_transform
    full_train_aug = datasets.CIFAR10(args.data_dir, train=True, download=False, transform=train_transform)
    full_train_eval = datasets.CIFAR10(args.data_dir, train=True, download=False, transform=eval_transform)
    test = datasets.CIFAR10(args.data_dir, train=False, download=False, transform=eval_transform)

    generator = np.random.default_rng(args.split_seed)
    permutation = generator.permutation(len(full_train_aug))
    if not 0 <= args.validation_size < len(permutation):
        raise ValueError("validation-size must be between 0 and 49,999")
    validation_indices = permutation[: args.validation_size]
    train_indices = permutation[args.validation_size :]

    training_subset = Subset(full_train_aug, train_indices.tolist())
    training_evaluation = Subset(full_train_eval, train_indices.tolist())
    eps = make_profile(
        args.profile,
        len(training_subset),
        seed=args.profile_seed,
        private_epsilon=args.private_epsilon,
        epsilon_1=args.epsilon_1, epsilon_2=args.epsilon_2,
        group_1_fraction=args.group_1_fraction,
    )
    eps = eps * args.epsilon_scale
    private_train = IndexedPrivateDataset(training_subset, eps)
    validation = (
        Subset(full_train_eval, validation_indices.tolist())
        if args.validation_size
        else None
    )
    return private_train, training_evaluation, validation, test, eps


@torch.no_grad()
def accuracy(model: nn.Module, loader: DataLoader, device: torch.device) -> float:
    model.eval()
    correct = total = 0
    for images, targets in loader:
        images = images.to(device, non_blocking=True)
        targets = targets.to(device, non_blocking=True)
        correct += int((model(images).argmax(1) == targets).sum())
        total += targets.numel()
    model.train()
    return correct / total


def clipped_weighted_step(
    model: GradSampleModule,
    optimizer: torch.optim.Optimizer,
    images: torch.Tensor,
    targets: torch.Tensor,
    epsilon: np.ndarray,
    mechanism: SampledMechanism,
    args: argparse.Namespace,
    device: torch.device,
    noise_generator: torch.Generator | None = None,
) -> tuple[float, float, int, np.ndarray, dict[str, float]]:
    # The same fixed public weights used during accounting, including the
    # automatically optimized RDP weights. No recalibration inside a batch.
    positions = np.searchsorted(mechanism.budget_levels, epsilon)
    batch_weights = mechanism.level_weights[positions]
    coefficients = batch_weights / mechanism.expected_weight_mass
    global_coefficients = mechanism.raw_weights / mechanism.raw_weights.sum()
    mechanism_stats = {
        "effective_sample_size": mechanism.effective_sample_size,
        "max_coefficient": float(np.max(global_coefficients)),
        "observed_weight_mass_ratio": float(
            batch_weights.sum() / mechanism.expected_weight_mass
        ),
        "max_privacy_utilization": mechanism.max_privacy_utilization,
    }
    # Zero-weight records cannot affect the update. Sampling remains uniform;
    # only their unnecessary per-example backward passes are omitted.
    active_indices = np.flatnonzero(batch_weights > 0)
    images = images[torch.as_tensor(active_indices, device=images.device)]
    targets = targets[torch.as_tensor(active_indices, device=targets.device)]
    coefficients = coefficients[active_indices]
    parameters = [parameter for parameter in model.parameters() if parameter.requires_grad]
    accumulated = [torch.zeros_like(parameter) for parameter in parameters]
    weighted_loss = 0.0
    preclip_norms = []

    for start in range(0, len(images), args.microbatch_size):
        stop = min(start + args.microbatch_size, len(images))
        micro_images = images[start:stop].to(device, non_blocking=True)
        micro_targets = targets[start:stop].to(device, non_blocking=True)
        model.zero_grad(set_to_none=True)
        logits = model(micro_images)
        losses = F.cross_entropy(logits, micro_targets, reduction="none")
        losses.sum().backward()
        squared_norm = torch.zeros(stop - start, device=device)
        for parameter in parameters:
            grad_sample = parameter.grad_sample
            if isinstance(grad_sample, list):
                grad_sample = torch.cat(grad_sample, dim=0)
            squared_norm.add_(grad_sample.flatten(1).pow(2).sum(1))
        norm = squared_norm.sqrt()
        clip = (args.clip_norm / (norm + 1e-12)).clamp(max=1.0)
        coeff = torch.as_tensor(
            coefficients[start:stop], device=device, dtype=clip.dtype
        )
        weighted_loss += float((losses.detach() * coeff).sum())
        if args.log_preclip_stats:
            active = coeff > 0
            preclip_norms.append(norm[active].detach().cpu().numpy())
        scale = coeff * clip
        for destination, parameter in zip(accumulated, parameters):
            grad_sample = parameter.grad_sample
            if isinstance(grad_sample, list):
                grad_sample = torch.cat(grad_sample, dim=0)
            shape = (len(scale),) + (1,) * (grad_sample.ndim - 1)
            destination.add_((grad_sample * scale.view(shape)).sum(0))

    model.zero_grad(set_to_none=True)
    for parameter, gradient in zip(parameters, accumulated):
        noise_std = (
            args.clip_norm
            * mechanism.noise_multiplier
            / mechanism.expected_weight_mass
        )
        if noise_std:
            noise = torch.randn(gradient.shape, dtype=gradient.dtype,
                                device=gradient.device, generator=noise_generator)
            gradient.add_(noise, alpha=noise_std)
        parameter.grad = gradient
    optimizer.step()
    norms = (
        np.concatenate(preclip_norms)
        if preclip_norms
        else np.empty(0, dtype=np.float32)
    )
    return (
        weighted_loss, noise_std, int(np.count_nonzero(batch_weights)), norms,
        mechanism_stats,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=PROFILE_NAMES, required=True)
    parser.add_argument("--epsilon-1", type=float, default=1., help="first budget for --profile two_level")
    parser.add_argument("--epsilon-2", type=float, default=.1, help="second budget for --profile two_level")
    parser.add_argument("--group-1-fraction", type=float, default=.2,
                        help="first group share for --profile two_level; total dataset size stays fixed")
    parser.add_argument(
        "--method", choices=("nonprivate", "threshold", "personalized"), required=True
    )
    parser.add_argument(
        "--parameter-epsilon",
        type=float,
        default=None,
        help="threshold t or cap tau on the epsilon scale; required except for nonprivate",
    )
    parser.add_argument("--private-epsilon", type=float, default=1.0,
                        help="epsilon for the 40k private records in public_private")
    parser.add_argument("--epsilon-scale", type=float, default=1.0,
                        help="multiply all finite budgets; public records stay public")
    parser.add_argument("--auto-weights", action="store_true",
                        help="optimize the sampled MSE upper bound using public metadata only")
    parser.add_argument("--delta", type=float, default=1e-5)
    parser.add_argument("--clip-norm", type=float, default=1.0)
    parser.add_argument(
        "--log-preclip-stats",
        action="store_true",
        help="log active-record gradient-norm quantiles; diagnostic output is not DP",
    )
    parser.add_argument("--epochs", type=int, default=30)
    parser.add_argument(
        "--privacy-epochs",
        type=int,
        default=None,
        help="composition horizon used for noise; defaults to --epochs",
    )
    parser.add_argument("--lr", type=float, default=0.3)
    parser.add_argument("--momentum", type=float, default=0.9)
    parser.add_argument("--weight-decay", type=float, default=5e-4)
    parser.add_argument("--logical-batch-size", type=int, default=5000)
    parser.add_argument("--microbatch-size", type=int, default=64)
    parser.add_argument(
        "--model", choices=("smallcnn", "resnet18"), default="smallcnn"
    )
    parser.add_argument(
        "--augmentation",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="random crop/flip training augmentation",
    )
    parser.add_argument("--validation-size", type=int, default=0)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--split-seed", type=int, default=2025)
    parser.add_argument("--profile-seed", type=int, default=2026)
    parser.add_argument(
        "--test-every-epoch",
        action="store_true",
        help="evaluate the CIFAR-10 test set every epoch; use only after tuning",
    )
    parser.add_argument("--num-workers", type=int, default=8)
    parser.add_argument(
        "--data-dir",
        type=Path,
        default=Path(os.environ.get("CIFAR10_DIR", "data")),
        help="directory containing cifar-10-batches-py; defaults to CIFAR10_DIR or data",
    )
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--device", default="cuda")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.method != "nonprivate" and args.parameter_epsilon is None and not args.auto_weights:
        raise ValueError("--parameter-epsilon is required for private mechanisms")
    if args.privacy_epochs is None:
        args.privacy_epochs = args.epochs
    if args.privacy_epochs < args.epochs:
        raise ValueError("privacy-epochs cannot be smaller than epochs actually run")
    if args.epsilon_scale <= 0 or not math.isfinite(args.epsilon_scale):
        raise ValueError("epsilon-scale must be finite and positive")
    if args.clip_norm <= 0 or args.epochs <= 0 or args.logical_batch_size <= 0 or args.microbatch_size <= 0:
        raise ValueError("clip norm, epochs and batch sizes must be positive")
    if args.validation_size and args.test_every_epoch:
        raise ValueError("do not evaluate the test set during validation tuning")
    if args.microbatch_size > args.logical_batch_size:
        raise ValueError("microbatch-size cannot exceed logical-batch-size")
    if args.device == "cuda" and not torch.cuda.is_available():
        raise RuntimeError("CUDA was requested but is unavailable")
    args.output.mkdir(parents=True, exist_ok=True)
    if (args.output / "epochs.csv").exists():
        raise FileExistsError(f"refusing to overwrite existing run: {args.output}")
    seed_everything(args.seed)
    device = torch.device(args.device)
    training, training_evaluation, validation, test, profile = make_datasets(args)
    if args.logical_batch_size > len(training):
        raise ValueError("logical-batch-size cannot exceed the training set")
    if len(training) % args.logical_batch_size:
        raise ValueError(
            "training records must be divisible by logical-batch-size so the "
            "Poisson sampler has an exact number of steps per epoch"
        )
    sample_rate = args.logical_batch_size / len(training)
    steps_per_epoch = len(training) // args.logical_batch_size
    base_model = make_model(args.model)
    trainable_parameters = sum(p.numel() for p in base_model.parameters() if p.requires_grad)
    mechanism = calibrate_sampled_mechanism(
        profile,
        args.method,
        args.parameter_epsilon,
        args.delta,
        sample_rate,
        args.privacy_epochs * steps_per_epoch,
        optimize=args.auto_weights,
        dimension=trainable_parameters,
    )
    noise_generator = torch.Generator(device=device).manual_seed(args.seed + 1_000_003)
    train_loader = DPDataLoader(
        training,
        sample_rate=sample_rate,
        num_workers=args.num_workers,
        pin_memory=device.type == "cuda",
        persistent_workers=args.num_workers > 0,
        generator=torch.Generator().manual_seed(args.seed),
    )
    if len(train_loader) != steps_per_epoch:
        raise RuntimeError("sampler step count differs from privacy composition")
    evaluation_workers = min(2, args.num_workers)
    train_eval_loader = DataLoader(
        training_evaluation,
        batch_size=512,
        shuffle=False,
        num_workers=evaluation_workers,
        pin_memory=device.type == "cuda",
        persistent_workers=evaluation_workers > 0,
    )
    validation_loader = (
        DataLoader(
            validation,
            batch_size=512,
            shuffle=False,
            num_workers=evaluation_workers,
            pin_memory=device.type == "cuda",
            persistent_workers=evaluation_workers > 0,
        )
        if validation is not None
        else None
    )
    evaluate_test = args.test_every_epoch or validation is None
    test_loader = (
        DataLoader(
            test,
            batch_size=512,
            shuffle=False,
            num_workers=evaluation_workers,
            pin_memory=device.type == "cuda",
            persistent_workers=evaluation_workers > 0,
        )
        if evaluate_test
        else None
    )
    evaluation_name = "validation" if validation_loader is not None else "test"

    model = GradSampleModule(base_model, batch_first=True, loss_reduction="sum").to(device)
    trainable_parameters = sum(
        parameter.numel() for parameter in model.parameters() if parameter.requires_grad
    )
    optimizer = torch.optim.SGD(
        model.parameters(), lr=args.lr, momentum=args.momentum, weight_decay=args.weight_decay
    )
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(
        optimizer, T_max=args.privacy_epochs
    )
    log_path = args.output / "epochs.csv"
    started = time.time()
    best_accuracy = -1.0
    final_accuracy = -1.0
    final_train_accuracy = -1.0
    final_validation_accuracy = None
    final_test_accuracy = None

    with log_path.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=(
                "epoch", "lr", "loss", "accuracy", "train_accuracy",
                "validation_accuracy", "test_accuracy", "mean_noise_std", "mean_retained",
                "preclip_norm_count", "preclip_norm_mean", "preclip_norm_p10",
                "preclip_norm_p25", "preclip_norm_p50", "preclip_norm_p75",
                "preclip_norm_p90", "preclip_norm_p95", "preclip_norm_p99",
                "preclip_norm_max", "clipped_fraction", "clipped_second_moment_v_upper",
                "mean_effective_sample_size", "max_coefficient",
                "mean_observed_weight_mass_ratio", "max_privacy_utilization",
                "mean_noise_l2_to_clip_upper",
            ),
        )
        writer.writeheader()
        for epoch in range(args.epochs):
            epoch_lr = optimizer.param_groups[0]["lr"]
            losses, noises, retained, epoch_norms, mechanism_stats = [], [], [], [], []
            for images, targets, epsilon in train_loader:
                loss, noise, kept, preclip_norms, batch_stats = clipped_weighted_step(
                    model,
                    optimizer,
                    images,
                    targets,
                    epsilon.numpy(),
                    mechanism,
                    args,
                    device,
                    noise_generator,
                )
                losses.append(loss)
                noises.append(noise)
                retained.append(kept)
                mechanism_stats.append(batch_stats)
                if len(preclip_norms):
                    epoch_norms.append(preclip_norms)
            final_train_accuracy = accuracy(model, train_eval_loader, device)
            final_validation_accuracy = (
                accuracy(model, validation_loader, device)
                if validation_loader is not None
                else None
            )
            final_test_accuracy = (
                accuracy(model, test_loader, device)
                if test_loader is not None
                else None
            )
            final_accuracy = (
                final_validation_accuracy
                if final_validation_accuracy is not None
                else final_test_accuracy
            )
            best_accuracy = max(best_accuracy, final_accuracy)
            row = {
                "epoch": epoch + 1,
                "lr": epoch_lr,
                "loss": float(np.mean(losses)) if args.log_preclip_stats else "",
                "accuracy": final_accuracy,
                "train_accuracy": final_train_accuracy,
                "validation_accuracy": (
                    final_validation_accuracy
                    if final_validation_accuracy is not None
                    else ""
                ),
                "test_accuracy": (
                    final_test_accuracy if final_test_accuracy is not None else ""
                ),
                "mean_noise_std": float(np.mean(noises)),
                "mean_retained": float(np.mean(retained)),
                "mean_effective_sample_size": float(
                    np.mean([item["effective_sample_size"] for item in mechanism_stats])
                ),
                "max_coefficient": float(
                    np.max([item["max_coefficient"] for item in mechanism_stats])
                ),
                "mean_observed_weight_mass_ratio": float(
                    np.mean(
                        [item["observed_weight_mass_ratio"] for item in mechanism_stats]
                    )
                ),
                "max_privacy_utilization": float(
                    np.max([item["max_privacy_utilization"] for item in mechanism_stats])
                ),
                "mean_noise_l2_to_clip_upper": float(
                    np.mean(noises) * math.sqrt(trainable_parameters) / args.clip_norm
                ),
            }
            if epoch_norms:
                norms = np.concatenate(epoch_norms)
                quantiles = np.quantile(norms, [0.10, 0.25, 0.50, 0.75, 0.90, 0.95, 0.99])
                row.update(
                    {
                        "preclip_norm_count": len(norms),
                        "preclip_norm_mean": float(norms.mean()),
                        "preclip_norm_p10": float(quantiles[0]),
                        "preclip_norm_p25": float(quantiles[1]),
                        "preclip_norm_p50": float(quantiles[2]),
                        "preclip_norm_p75": float(quantiles[3]),
                        "preclip_norm_p90": float(quantiles[4]),
                        "preclip_norm_p95": float(quantiles[5]),
                        "preclip_norm_p99": float(quantiles[6]),
                        "preclip_norm_max": float(norms.max()),
                        "clipped_fraction": float(np.mean(norms > args.clip_norm)),
                        "clipped_second_moment_v_upper": float(
                            np.mean(np.minimum(norms, args.clip_norm) ** 2)
                        ),
                    }
                )
            else:
                row.update(
                    {name: "" for name in writer.fieldnames if name.startswith("preclip_")}
                )
                row["clipped_fraction"] = ""
                row["clipped_second_moment_v_upper"] = ""
            writer.writerow(row)
            handle.flush()
            print(json.dumps(row), flush=True)
            scheduler.step()

    serializable_args = dict(vars(args))
    if (
        serializable_args["parameter_epsilon"] is not None
        and math.isinf(serializable_args["parameter_epsilon"])
    ):
        serializable_args["parameter_epsilon"] = "inf"
    summary = {
        **serializable_args,
        "data_dir": str(args.data_dir),
        "output": str(args.output),
        "evaluation_split": evaluation_name,
        "training_records": len(training),
        "trainable_parameters": trainable_parameters,
        "sample_rate": sample_rate,
        "steps_per_epoch": steps_per_epoch,
        "implementation_version": "sampled-v2",
        "accounted_steps": args.privacy_epochs * steps_per_epoch,
        "executed_steps": args.epochs * steps_per_epoch,
        "weight_selection": mechanism.selection,
        "privacy_audit": mechanism.audit,
        "max_privacy_utilization": mechanism.max_privacy_utilization,
        "noise_multiplier_on_weighted_sum": mechanism.noise_multiplier,
        "expected_weight_mass": mechanism.expected_weight_mass,
        "profile_counts": {
            "public": int(np.isposinf(profile).sum()),
            **{
                str(value): int((profile == value).sum())
                for value in np.unique(profile[np.isfinite(profile)])
            },
        },
        "best_accuracy": best_accuracy,
        "final_accuracy": final_accuracy,
        "final_train_accuracy": final_train_accuracy,
        "final_validation_accuracy": final_validation_accuracy,
        "final_test_accuracy": final_test_accuracy,
        "elapsed_seconds": time.time() - started,
        "diagnostics_statement": (
            "Training accuracy and pre-clipping gradient statistics are non-private "
            "research diagnostics and are not covered by the model's DP guarantee."
        ),
        "privacy_statement": (
            "No differential-privacy guarantee: this is a non-private clipped-gradient control."
            if args.method == "nonprivate"
            else (
                f"Each included record is (epsilon shown in profile, delta={args.delta})-DP "
                "under add/remove (zero-out) adjacency with a fixed public roster, budgets, "
                "weights, sampling rate, denominator and noise calibration. Uniform Poisson "
                "sampling uses Opacus RDP with a log-space extension for large integer orders. "
                "This is a per-run training guarantee; tuning and private-data diagnostics "
                "are not covered. It is not a replacement-adjacency guarantee."
            )
        ),
    }
    with (args.output / "summary.json").open("w") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True, allow_nan=False)


if __name__ == "__main__":
    main()
