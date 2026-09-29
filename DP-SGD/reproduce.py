#!/usr/bin/env python3
"""Reproduce the six DP-SGD figures, from exports or fresh training."""
import argparse
import csv
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

import experiment as exp
import paper_figures as paper
import sensitivity_sweep as sweep

HERE = Path(__file__).resolve().parent


def read_csv(path):
    with path.open() as handle:
        return list(csv.DictReader(handle))


def figures(data, output):
    output.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.size": 10, "axes.labelsize": 11,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "axes.spines.top": False, "axes.spines.right": False})
    paper.learning_figures(data / "paper", output)
    paper.appendix_figures(output)
    # Keep the original sensitivity plotting defaults independent of prior plots.
    plt.rcdefaults()
    protocol = json.loads((data / "sensitivity" / "protocol.json").read_text())
    table = [{k: v if k in ("scenario", "ci95_within_1pp") else float(v)
              for k, v in row.items()}
             for row in read_csv(data / "sensitivity" / "plots" / "comparison.csv")]
    sweep.plot_figures(protocol, table, output)
    names = {
        "cifar10_train_accuracy_three_privacy_profiles": "cifar10_train",
        "cifar10_test_accuracy_three_privacy_profiles": "cifar10_test",
        "appendix_mse_ratio_vary_epsilon2": "mse_ratio_vary_epsilon2",
        "appendix_mse_ratio_vary_group_sizes": "mse_ratio_vary_group_sizes",
        "empirical_sweep_epsilon2_combined": "empirical_sweep_epsilon2",
        "empirical_sweep_group_sizes_combined": "empirical_sweep_group_sizes",
    }
    for old, new in names.items():
        for suffix in ("pdf", "png", "csv"):
            path = output / f"{old}.{suffix}"
            if path.exists():
                path.replace(output / f"{new}.{suffix}")
    print(f"Six figures: {output}")


def prepare(root, cifar, selected_path=None):
    if not (cifar / "cifar-10-batches-py" / "data_batch_1").is_file():
        raise FileNotFoundError(f"Expected CIFAR-10 at {cifar}/cifar-10-batches-py")
    root.mkdir(parents=True, exist_ok=False)
    selected = json.loads((selected_path or HERE / "data" / "paper" / "selected.json").read_text())
    selected = {name: selected[name] for name, _, _ in paper.MAIN}
    exp.save(root / "paper" / "selected.json", selected)
    main = [exp.make_run(root, "final", name,
             (r["batch"], r["epochs"], r["lr"]), seed, method)
            for name, r in selected.items() for seed in exp.FINAL_SEEDS for method in exp.METHODS]
    points, sweeps = sweep.design()
    sensitivity_root = root / "sensitivity"
    protocol = json.loads((HERE / "data" / "sensitivity" / "protocol.json").read_text())
    exp.save(sensitivity_root / "protocol.json", protocol)
    shutil.copyfile(HERE / "data" / "sensitivity" / "theory.csv", sensitivity_root / "theory.csv")
    sensitivity = sweep.manifest(sensitivity_root, points)
    for run in main + sensitivity:
        run["data_dir"] = str(cifar)
    exp.save(root / "paper" / "manifest.json", main)
    exp.save(sensitivity_root / "manifest.json", sensitivity)
    exp.write_jobs(root / "train.txt", [exp.command(run) for run in main + sensitivity])
    exp.write_jobs(root / "finish.txt", [shlex.join([
        "python", "reproduce.py", "finish", "--root", str(root)])])
    return main + sensitivity


def finish(root):
    runs = json.loads((root / "paper" / "manifest.json").read_text())
    actual = [(r["scenario"], r["method"], r["seed"]) for r in runs]
    expected = {(n, m, s) for n, _, _ in paper.MAIN
                for m in exp.METHODS for s in exp.FINAL_SEEDS}
    if len(actual) != len(expected) or set(actual) != expected:
        raise ValueError("Incomplete or duplicate main-figure runs")
    records = {key: exp.check_run(run) for key, run in zip(actual, runs)}
    curves, comparison = [], []
    for name, _, _ in paper.MAIN:
        final = {}
        for method in exp.METHODS:
            epochs = [records[(name, method, seed)][1] for seed in exp.FINAL_SEEDS]
            for metric in ("train_accuracy", "test_accuracy"):
                values = np.array([[100*float(row[metric]) for row in rows] for rows in epochs])
                mean, half = sweep.mean_ci(values)
                curves.extend(dict(scenario=name, method=method, split=metric,
                    epoch=i, mean_pct=float(m), ci95_halfwidth_pp=float(h))
                    for i, (m, h) in enumerate(zip(mean, half), 1))
                if metric == "test_accuracy":
                    final[method] = float(mean[-1])
        comparison.append(dict(scenario=name, threshold_test_pct=final["threshold"],
                               personalized_test_pct=final["personalized"]))
    sweep.write_csv(root / "paper" / "learning_curves.csv", curves)
    sweep.write_csv(root / "paper" / "final_comparison.csv", comparison)
    sweep.plot(root / "sensitivity")
    figures(root, root / "figures")
    exp.save(root / "DONE.json", {"completed_runs": 160, "figures": str(root / "figures")})


def select(root):
    runs = json.loads((root / "manifest.json").read_text())
    expected = {(name, b, e, lr, m, s) for name, grid in exp.GRIDS.items()
                for b, e, lr in grid for m in exp.METHODS for s in exp.TUNE_SEEDS}
    actual = [(r["scenario"], r["logical_batch_size"], r["epochs"], r["lr"],
               r["method"], r["seed"]) for r in runs]
    if len(actual) != len(expected) or set(actual) != expected:
        raise ValueError("Incomplete or duplicate validation manifest")
    selected, candidates = {}, []
    records = {key: exp.check_run(r)[0] for key, r in zip(actual, runs)}
    for name, grid in exp.GRIDS.items():
        for b, e, lr in sorted(grid):
            means = {m: float(np.mean([records[(name,b,e,lr,m,s)]["final_validation_accuracy"]
                                      for s in exp.TUNE_SEEDS])) for m in exp.METHODS}
            score = float(np.mean(list(means.values())))
            if not np.isfinite(score):
                raise ValueError("Nonfinite validation score")
            row = dict(scenario=name, batch=b, epochs=e, lr=lr,
                       selection_score=score, **means)
            candidates.append(row)
            if name not in selected or score > selected[name]["selection_score"]:
                selected[name] = row
    exp.save(root / "candidates.json", candidates)
    exp.save(root / "selected.json", selected)
    print(f"Validation-selected recipes: {root / 'selected.json'}")


def validate(root, cifar, parallel, submit):
    if not (cifar / "cifar-10-batches-py/data_batch_1").is_file():
        raise FileNotFoundError("CIFAR-10 Python dataset is missing")
    root.mkdir(parents=True, exist_ok=False)
    runs = [exp.make_run(root, "tune", name, recipe, seed, method)
            for name, grid in exp.GRIDS.items() for recipe in grid
            for seed in exp.TUNE_SEEDS for method in exp.METHODS]
    for run in runs:
        run["data_dir"] = str(cifar)
    exp.save(root / "manifest.json", runs)
    exp.write_jobs(root / "train.txt", [exp.command(r) for r in runs])
    exp.write_jobs(root / "select.txt", [shlex.join([
        "python", "reproduce.py", "select", "--root", str(root)])])
    if submit:
        training = exp.submit(root / "train.txt", len(runs), parallel)
        selection = exp.submit(root / "select.txt", 1, 1, training)
        exp.save(root / "jobs.json", dict(training=training, selection=selection))
    else:
        for run in runs:
            argv = shlex.split(exp.command(run))
            subprocess.run([sys.executable, *argv[1:]], check=True)
        select(root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=("plot", "train", "submit", "prepare", "finish",
                                          "validate", "validate-submit", "select"), nargs="?", default="plot")
    parser.add_argument("--root", type=Path, default=HERE / "runs")
    parser.add_argument("--data", type=Path, default=HERE / "data")
    parser.add_argument("--output", type=Path, default=HERE / "figures")
    parser.add_argument("--cifar", type=Path, default=Path(os.environ.get("CIFAR10_DIR", "data")))
    parser.add_argument("--parallel", type=int, default=32)
    parser.add_argument("--selected", type=Path, help="validation selected.json for main learning curves")
    args = parser.parse_args()
    if args.parallel < 1:
        parser.error("--parallel must be positive")
    root, data, output, cifar = [p.resolve() for p in (args.root, args.data, args.output, args.cifar)]
    selected_path = args.selected.resolve() if args.selected else None
    os.chdir(HERE)
    if args.stage == "plot":
        figures(data, output)
    elif args.stage == "finish":
        finish(root)
    elif args.stage == "select":
        select(root)
    elif args.stage in ("validate", "validate-submit"):
        validate(root, cifar, args.parallel, args.stage == "validate-submit")
    else:
        runs = prepare(root, cifar, selected_path)
        if args.stage == "submit":
            training = exp.submit(root / "train.txt", len(runs), args.parallel)
            plotting = exp.submit(root / "finish.txt", 1, 1, training)
            exp.save(root / "jobs.json", dict(training=training, plotting=plotting))
        elif args.stage == "train":
            for run in runs:
                argv = shlex.split(exp.command(run))
                subprocess.run([sys.executable, *argv[1:]], check=True)
            finish(root)
        print(f"{len(runs)} runs; outputs: {root}")


if __name__ == "__main__":
    main()
