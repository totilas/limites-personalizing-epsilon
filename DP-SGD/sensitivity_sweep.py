from __future__ import annotations

import argparse

import csv

import json

import shlex

from pathlib import Path

import numpy as np

from scipy.stats import t

from experiment import METHODS, check_run, command, make_run, save, submit, write_jobs

from mse_theory import paper_ratio, sampled_ratio

N, DIMENSION = 50000, 558538

SEEDS = (200, 201, 202, 203, 204)

RECIPE = (1000, 30, .00625)

EPSILON_2 = (.01, .03, .1, .3, 1., 3., 10.)

GROUP_1_COUNTS = (1000, 2500, 5000, 10000, 20000, 35000, 45000)

def design():
    points, sweeps = {}, {}
    for axis, pairs in (("epsilon2", [(e, 10000) for e in EPSILON_2]),
                        ("group_sizes", [(.1, n) for n in GROUP_1_COUNTS])):
        sweeps[axis] = []
        for epsilon, n1 in pairs:
            key = f"e2_{epsilon:g}_n1_{n1}"
            points[key] = dict(epsilon_1=1., epsilon_2=epsilon, n_1=n1, n_2=N-n1)
            sweeps[axis].append(key)
    return points, sweeps

def manifest(root, points):
    runs = []
    for key, point in points.items():
        for seed in SEEDS:
            for method in METHODS:
                run = make_run(root, "final", "eps1_eps01", RECIPE, seed, method)
                run.update(scenario=key, profile="two_level", epsilon_1=point["epsilon_1"],
                           epsilon_2=point["epsilon_2"], group_1_fraction=point["n_1"]/N,
                           output=str(root / "runs" / key / method / f"seed{seed}"))
                runs.append(run)
    return runs

def write_csv(path, rows):
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

def theory(points):
    batch, epochs, _ = RECIPE
    common = dict(steps=epochs*(N//batch), dimension=DIMENSION, delta=1e-5)
    rows = []
    for key, point in points.items():
        eps, counts = [point["epsilon_1"], point["epsilon_2"]], [point["n_1"], point["n_2"]]
        paper = paper_ratio(eps, counts, **common)
        sampled = sampled_ratio(eps, counts, sample_rate=batch/N, **common)
        rows.append(dict(scenario=key, **point, paper_zcdp_ratio=paper["ratio"],
                         sampled_rdp_ratio=sampled["ratio"]))
    return rows

def mean_ci(values):
    a = np.asarray(values, dtype=float)
    if len(a) < 2 or not np.all(np.isfinite(a)):
        raise ValueError("at least two finite seed results are required")
    return a.mean(axis=0), t.ppf(.975, len(a)-1)*a.std(axis=0, ddof=1)/np.sqrt(len(a))

def plot(root):
    protocol = json.loads((root / "protocol.json").read_text())
    runs = json.loads((root / "manifest.json").read_text())
    expected = {(key, method, seed) for key in protocol["points"]
                for method in METHODS for seed in protocol["seeds"]}
    actual = [(r["scenario"], r["method"], r["seed"]) for r in runs]
    if len(actual) != len(expected) or set(actual) != expected:
        raise ValueError("incomplete or duplicate run manifest")
    with (root / "theory.csv").open() as handle:
        theoretical = {r["scenario"]: r for r in csv.DictReader(handle)}
    records = {key: check_run(run) for key, run in zip(actual, runs)}
    out = root / "plots"
    out.mkdir(exist_ok=True)
    table, curves, seed_rows = [], [], []
    for key in protocol["points"]:
        result = dict(theoretical[key])
        final, bounds = {}, {}
        for method in METHODS:
            summaries, epochs = zip(*(records[(key, method, seed)] for seed in protocol["seeds"]))
            if any(s["trainable_parameters"] != protocol["dimension"] for s in summaries):
                raise ValueError("model dimension differs from theoretical calculation")
            bounds[method] = np.array([s["weight_selection"]["mse_bound_over_C2"] for s in summaries])
            for metric in ("train_accuracy", "test_accuracy"):
                values = np.array([[100*float(r[metric]) for r in rows] for rows in epochs])
                mean, half = mean_ci(values)
                for epoch, (m, h) in enumerate(zip(mean, half), 1):
                    curves.append(dict(scenario=key, method=method, split=metric, epoch=epoch,
                                       mean_pct=float(m), ci95_halfwidth_pp=float(h)))
                if metric == "test_accuracy":
                    final[method] = values[:, -1]
                    result[method + "_test_pct"] = float(mean[-1])
                    result[method + "_ci95_halfwidth_pp"] = float(half[-1])
            for seed, summary in zip(protocol["seeds"], summaries):
                seed_rows.append(dict(scenario=key, method=method, seed=seed,
                    train_accuracy_pct=100*summary["final_train_accuracy"],
                    test_accuracy_pct=100*summary["final_test_accuracy"],
                    elapsed_seconds=summary["elapsed_seconds"],
                    mse_bound_over_C2=summary["weight_selection"]["mse_bound_over_C2"]))
        ratio = bounds["threshold"]/bounds["personalized"]
        if not np.allclose(ratio, float(result["sampled_rdp_ratio"]), rtol=1e-7, atol=1e-9):
            raise ValueError(f"theory and training mechanisms disagree: {key}")
        mean, half = mean_ci(final["personalized"]-final["threshold"])
        result.update(paired_difference_pp=float(mean), ci95_halfwidth_pp=float(half),
                      ci95_within_1pp=bool(abs(mean)+half < 1))
        table.append(result)
    write_csv(out / "comparison.csv", table)
    write_csv(out / "learning_curves.csv", curves)
    write_csv(out / "per_seed.csv", seed_rows)
    plot_figures(protocol, table, out)
    save(root / "DONE.json", dict(completed_runs=len(runs), plots=str(out)))
    print(f"Plots and data: {out}")

def plot_figures(protocol, table, out):
    """Render exported results without changing data or requiring training files."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    lookup = {r["scenario"]: r for r in table}
    plt.rcParams.update({"font.size": 10, "pdf.fonttype": 42,
                         "axes.spines.top": False, "axes.spines.right": False})
    for sweep, keys in protocol["sweeps"].items():
        rows = [lookup[k] for k in keys]
        x = [float(r["epsilon_2"]) if sweep == "epsilon2" else 100*int(r["n_1"])/N for r in rows]
        figure, axes = plt.subplots(2, 1, figsize=(7.2, 5.3), sharex=True)
        for method, color in zip(METHODS, (plt.get_cmap("viridis")(.12), plt.get_cmap("viridis")(.65))):
            axes[0].errorbar(x, [r[method+"_test_pct"] for r in rows],
                yerr=[r[method+"_ci95_halfwidth_pp"] for r in rows], color=color,
                marker="o", ms=4, capsize=3, label=method.capitalize())
        axes[0].set_ylabel("Final test accuracy (%)")
        axes[0].legend(fontsize=9)
        axes[1].axhline(0, color=".4", lw=.7)
        gain_color = plt.get_cmap("viridis")(.35)
        ratio_color = plt.get_cmap("viridis")(.70)
        axes[1].errorbar(x, [r["paired_difference_pp"] for r in rows],
            yerr=[r["ci95_halfwidth_pp"] for r in rows], color=gain_color,
            marker="o", ms=4, capsize=3, label="Empirical gain")
        axes[1].set_ylabel("Personalized − threshold\n(percentage points)")
        axes[1].tick_params(axis="y", colors=gain_color)
        axes[1].yaxis.label.set_color(gain_color)
        ratio_axis = axes[1].twinx()
        ratio_axis.spines["right"].set_visible(True)
        ratio_axis.plot(x, [float(r["sampled_rdp_ratio"]) for r in rows], "s--",
                        color=ratio_color, ms=4, label="Sampled-RDP bound ratio")
        ratio_axis.set_ylabel("MSE-bound ratio\nthreshold / personalized", color=ratio_color)
        ratio_axis.tick_params(axis="y", colors=ratio_color)
        # Align the two curves' extrema by an affine change of right-axis limits.
        # Use empirical means, not error-bar endpoints; retain all error bars.
        # This is a visual normalization, not a quantitative agreement claim.
        gains = [float(r["paired_difference_pp"]) for r in rows]
        ratios = [float(r["sampled_rdp_ratio"]) for r in rows]
        gain_min, gain_max = min(gains), max(gains)
        ratio_min, ratio_max = min(ratios), max(ratios)
        if gain_max > gain_min and ratio_max > ratio_min:
            scale = (ratio_max - ratio_min) / (gain_max - gain_min)
            ratio_axis.set_ylim(*(ratio_min + (limit - gain_min) * scale
                                  for limit in axes[1].get_ylim()))
        handles, labels = axes[1].get_legend_handles_labels()
        rh, rl = ratio_axis.get_legend_handles_labels()
        axes[1].legend(handles + rh, labels + rl, fontsize=8, loc="lower left",
                       bbox_to_anchor=(0, 1.02), ncol=3, borderaxespad=0)
        if sweep == "epsilon2":
            axes[1].set_xscale("log")
            axes[1].set_xlabel(r"Privacy budget $\varepsilon_2$ ($\varepsilon_1=1$; groups 10k/40k)")
        else:
            axes[1].set_xlabel(r"Group 1 share (%) ($\varepsilon_1=1,\ \varepsilon_2=0.1$; $N=50{,}000$)")
        for axis in axes:
            axis.grid(alpha=.18)
        figure.tight_layout()
        for suffix in ("pdf", "png"):
            figure.savefig(out / f"empirical_sweep_{sweep}_combined.{suffix}", dpi=200, bbox_inches="tight")
        plt.close(figure)

