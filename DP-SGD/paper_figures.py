from __future__ import annotations

import csv

import json

from pathlib import Path

import matplotlib

import matplotlib.pyplot as plt

from matplotlib.lines import Line2D

import numpy as np

from mse_theory import paper_ratio

N, DIMENSION, DELTA = 50000, 558538, 1e-5

MAIN = (("eps1_eps001", r"$\varepsilon=(1,\,0.01)$", "-"),
        ("eps8_eps4", r"$\varepsilon=(8,\,4)$", "--"),
        ("survey_x8", "Jorgensen et al.", "-."))

METHODS = ("threshold", "personalized")

COLORS = dict(zip(METHODS, (plt.get_cmap("viridis")(.12), plt.get_cmap("viridis")(.65))))

def write_csv(path, rows):
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

def save_figure(figure, output, name):
    figure.savefig(output / (name + ".pdf"), bbox_inches="tight")
    figure.savefig(output / (name + ".png"), dpi=220, bbox_inches="tight")
    plt.close(figure)

def learning_figures(data, output):
    with (data / "learning_curves.csv").open() as handle:
        rows = list(csv.DictReader(handle))
    selected = json.loads((data / "selected.json").read_text())
    with (data / "final_comparison.csv").open() as handle:
        final = {r["scenario"]: r for r in csv.DictReader(handle)}
    for split in ("train", "test"):
        figure, axis = plt.subplots(figsize=(6.4, 4.1))
        for scenario, _, style in MAIN:
            for method in METHODS:
                curve = sorted((r for r in rows if r["scenario"] == scenario and
                    r["method"] == method and r["split"] == split + "_accuracy"),
                    key=lambda r: int(r["epoch"]))
                x = np.array([int(r["epoch"]) for r in curve])
                if not np.array_equal(x, np.arange(1, selected[scenario]["epochs"] + 1)):
                    raise ValueError(f"missing or duplicate epochs: {scenario}/{method}/{split}")
                mean = np.array([float(r["mean_pct"]) for r in curve])
                ci = np.array([float(r["ci95_halfwidth_pp"]) for r in curve])
                if not np.all(np.isfinite(mean)) or not np.all(np.isfinite(ci)) or np.any(ci < 0):
                    raise ValueError("invalid mean or confidence interval")
                if split == "test" and not np.isclose(mean[-1], float(final[scenario][method + "_test_pct"]), atol=1e-9, rtol=0):
                    raise ValueError(f"final comparison disagrees with curve: {scenario}/{method}")
                axis.plot(x, mean, color=COLORS[method], linestyle=style, linewidth=1.8)
                axis.fill_between(x, mean-ci, mean+ci, color=COLORS[method], alpha=.12, linewidth=0)
        axis.set(xlabel="Epoch", ylabel=f"{split.capitalize()} accuracy (%)", xlim=(0, 60), ylim=(10, 65))
        axis.grid(alpha=.18, linewidth=.6)
        method_legend = axis.legend(handles=[Line2D([0], [0], color=COLORS[m], lw=2, label=m.capitalize())
            for m in METHODS], loc="lower right", frameon=True, fontsize=9)
        axis.add_artist(method_legend)
        axis.legend(handles=[Line2D([0], [0], color=".2", lw=1.8, linestyle=s, label=label)
            for _, label, s in MAIN], loc="upper left", frameon=True, fontsize=9)
        figure.tight_layout()
        save_figure(figure, output, f"cifar10_{split}_accuracy_three_privacy_profiles")

def appendix_figures(output):
    # Fixed total-budget composition and variance bound; these are analytic
    # oracle curves, not additional CIFAR-10 training runs.
    steps = 1500
    common = dict(steps=steps, dimension=DIMENSION, delta=DELTA)
    eps2 = np.unique(np.r_[np.geomspace(.01, 10., 401), .1, 1.])
    epsilon_rows = [dict(epsilon_1=1., epsilon_2=float(e), n_1=10000, n_2=40000,
                        ratio=paper_ratio([1., e], [10000, 40000], **common)["ratio"]) for e in eps2]
    counts = np.unique(np.rint(np.r_[np.linspace(100, 49900, 501), 10000]).astype(int))
    count_rows = [dict(epsilon_1=1., epsilon_2=.1, n_1=int(n), n_2=N-int(n),
                      ratio=paper_ratio([1., .1], [n, N-n], **common)["ratio"]) for n in counts]
    for rows, x, x_label, name, label, logscale in (
        (epsilon_rows, eps2, r"Privacy budget $\varepsilon_2$", "appendix_mse_ratio_vary_epsilon2",
         r"$\varepsilon_1=1,\quad n_1=10{,}000,\quad n_2=40{,}000$", True),
        (count_rows, 100*counts/N, r"Group 1 share $n_1/(n_1+n_2)$ (%)", "appendix_mse_ratio_vary_group_sizes",
         r"$\varepsilon_1=1,\quad\varepsilon_2=0.1,\quad n_1+n_2=50{,}000$", False)):
        figure, axis = plt.subplots(figsize=(6.4, 3.7))
        axis.plot(x, [r["ratio"] for r in rows], color=plt.get_cmap("viridis")(.35), lw=2, label=label)
        axis.axhline(1., color=".5", lw=.8, linestyle=":")
        if logscale:
            axis.set_xscale("log")
        axis.set(xlabel=x_label, ylabel=r"MSE-bound ratio $R_{\rm thr}/R_{\rm pers}$")
        axis.set_ylim(.95, 4.15)
        axis.legend(loc="upper right", fontsize=9)
        axis.grid(alpha=.18, linewidth=.6)
        figure.tight_layout()
        save_figure(figure, output, name)
        write_csv(output / (name + ".csv"), rows)
