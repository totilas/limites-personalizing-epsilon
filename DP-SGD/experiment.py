from __future__ import annotations

import csv

import json

import os

import shlex

import subprocess

from pathlib import Path

VERSION = "sampled-v2"

METHODS = ("threshold", "personalized")

FINAL_SEEDS = (100, 101, 102, 103, 104)
TUNE_SEEDS = (0, 1, 2)

# (logical batch size, epochs, initial learning rate).
LOW = [(5000, 30, .00625), (5000, 30, .01875),
       (1000, 30, .001875), (1000, 30, .00625), (1000, 30, .01875)]
HIGH = [(5000, 30, .01875), (1000, 60, .00625),
        (1000, 60, .01875), (1000, 60, .04375)]
PUBLIC = [(1000, 60, .01875), (1000, 60, .04375), (1000, 90, .04375)]

SCENARIOS = {
    "eps1_eps01": ("eps1_eps01", 1.),
    "eps1_eps001": ("eps1_eps001", 1.),
    "eps4_eps1": ("eps4_eps1", 1.),
    "eps8_eps1": ("eps8_eps1", 1.),
    "eps8_eps4": ("eps8_eps4", 1.),
    "public_private": ("public_private", 1.),
    "survey": ("survey", 1.),
    "survey_x8": ("survey", 8.),
}

GRIDS = {name: PUBLIC if name == "public_private" else
         LOW if name in ("eps1_eps01", "eps1_eps001", "survey") else HIGH
         for name in SCENARIOS}

def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")

def make_run(root, stage, scenario, recipe, seed, method):
    profile, scale = SCENARIOS[scenario]
    batch, epochs, lr = recipe
    recipe_id = f"b{batch}_e{epochs}_lr{lr:g}"
    output = root / stage / scenario / recipe_id / method / f"seed{seed}"
    return dict(scenario=scenario, profile=profile, epsilon_scale=scale,
                logical_batch_size=batch, epochs=epochs, lr=lr, seed=seed,
                method=method, validation_size=5000 if stage == "tune" else 0,
                clip_norm=16., auto_weights=True, model="smallcnn", delta=1e-5,
                profile_seed=2026, split_seed=2025, microbatch_size=64,
                augmentation=True, momentum=.9, weight_decay=.0005,
                output=str(output))

def command(run):
    argv = ["python", "-u", "train.py", "--auto-weights", "--log-preclip-stats"]
    for key, value in run.items():
        if key in ("scenario", "auto_weights", "augmentation"):
            continue
        argv += ["--" + key.replace("_", "-"), str(value)]
    return shlex.join(argv)

def write_jobs(path, commands):
    path.write_text("\n".join(commands) + "\n")

def submit(job_file, count, parallel, dependency=None):
    args = ["sbatch", "--parsable", "--array", f"1-{count}%{parallel}",
            "--time=03:00:00"]
    if dependency:
        args += ["--dependency", "afterok:" + dependency]
    args += ["slurm/array.slurm", str(job_file)]
    # A submission inside srun must not inherit a mask tied to its parent's CPUs.
    child_env = {key: value for key, value in os.environ.items()
                 if key != "SLURM_CPU_BIND" and not key.startswith("SLURM_CPU_BIND_")}
    result = subprocess.check_output(args, text=True, env=child_env).strip().split(";")[0]
    if not result.isdigit():
        raise RuntimeError(f"unrecognized sbatch response: {result}")
    print(f"Submitted {count} tasks: {result}", flush=True)
    return result

def check_run(run):
    directory = Path(run["output"])
    summary = json.loads((directory / "summary.json").read_text())
    if summary.get("implementation_version") != VERSION:
        raise ValueError(f"wrong implementation: {directory}")
    for key, value in run.items():
        if key != "scenario" and summary.get(key) != value:
            raise ValueError(f"configuration mismatch for {key}: {directory}")
    n = 50000 - run["validation_size"]
    steps = n // run["logical_batch_size"] * run["epochs"]
    if summary.get("executed_steps") != steps or summary.get("accounted_steps") != steps:
        raise ValueError(f"wrong execution/privacy horizon: {directory}")
    if summary["max_privacy_utilization"] > 1 + 1e-8:
        raise ValueError(f"privacy budget exceeded: {directory}")
    with (directory / "epochs.csv").open() as handle:
        rows = list(csv.DictReader(handle))
    if [int(row["epoch"]) for row in rows] != list(range(1, run["epochs"] + 1)):
        raise ValueError(f"missing epochs: {directory}")
    split = "validation_accuracy" if run["validation_size"] else "test_accuracy"
    if any(not row.get(split) or not row.get("train_accuracy") for row in rows):
        raise ValueError(f"missing learning curves: {directory}")
    if run["validation_size"] and any(row.get("test_accuracy") for row in rows):
        raise ValueError(f"test set evaluated during tuning: {directory}")
    return summary, rows
