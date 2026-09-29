
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from pathlib import Path
from matplotlib import cm

plt.rcParams.update({
    "font.size": 16,
    "axes.labelsize": 18,
    "xtick.labelsize": 14,
    "ytick.labelsize": 14,
    "legend.fontsize": 15,
})

def mse_affine_two_levels_closed_form(eps1, eps2, n1, n2):
    R = 1 + 8 / (n1 * eps1**2)
    if eps2 <= R * eps1:
        return (n1 * eps1**2 + n2 * eps2**2 + 8) / (
            4 * (n1 * eps1 + n2 * eps2)**2
        )
    return R / (4 * (n1 + n2 * R))


def mse_threshold_two_levels(eps1, eps2, n1, n2):
    n = n1 + n2
    mse_all = 1 / (4 * n) + 2 / ((n * eps1)**2)
    mse_group2 = 1 / (4 * n2) + 2 / ((n2 * eps2)**2)
    return min(mse_all, mse_group2)


def gain_two_levels(eps_ratio, n_ratio, scale, n2=1000):
    eps2 = np.sqrt(scale / n2)
    print("eps2", eps2)
    eps1 = eps_ratio * eps2
    n1 = max(int(round(n_ratio * n2)), 1)
    mse_thr = mse_threshold_two_levels(eps1, eps2, n1, n2)
    mse_aff = mse_affine_two_levels_closed_form(eps1, eps2, n1, n2)
    return mse_thr / mse_aff


def compute_gain_grid_two_levels(eps_ratios, n_ratios, scale, n2=1000):
    G = np.zeros((len(n_ratios), len(eps_ratios)))
    for i, nr in enumerate(n_ratios):
        for j, er in enumerate(eps_ratios):
            G[i, j] = gain_two_levels(er, nr, scale=scale, n2=n2)
    return G


def mse_threshold_public_private(eps1, n1, n2):
    n = n1 + n2
    mse_all = 1 / (4 * n) + 2 / ((n * eps1)**2)
    mse_public = 1 / (4 * n2)
    return min(mse_all, mse_public)


def mse_affine_public_private(eps1, n1, n2):
    mse_priv = 1 / (4 * n1) + 2 / ((n1 * eps1)**2)
    mse_pub = 1 / (4 * n2)
    return mse_priv * mse_pub / (mse_priv + mse_pub)


def gain_public_private(eps1, n_ratio, n2=1000):
    n1 = max(int(round(n_ratio * n2)), 1)
    mse_thr = mse_threshold_public_private(eps1, n1, n2)
    mse_aff = mse_affine_public_private(eps1, n1, n2)
    return mse_thr / mse_aff


def compute_gain_grid_public_private(eps1_values, n_ratios, n2=1000):
    G = np.zeros((len(n_ratios), len(eps1_values)))
    for i, nr in enumerate(n_ratios):
        for j, eps1 in enumerate(eps1_values):
            G[i, j] = gain_public_private(eps1, nr, n2=n2)
    return G





def plot_heatmap_two_levels(eps_ratios, n_ratios, G, outpath):
    plt.figure(figsize=(7, 6))

    im = plt.pcolormesh(
        eps_ratios,
        n_ratios,
        G,
        shading="auto",
        cmap="viridis",
    )

    levels = [1.05, 1.1, 1.25, 1.5, 2.0, 3.0, 4.0]
    cs = plt.contour(
        eps_ratios,
        n_ratios,
        G,
        levels=levels,
        colors="white",
        linewidths=1.2,
    )
    plt.clabel(cs, inline=True, fontsize=12, fmt=lambda x: x)

    plt.xscale("log")
    plt.yscale("log")
    plt.xlabel(r"$\varepsilon_1 / \varepsilon_2$")
    plt.ylabel(r"$n_1 / n_2$")
    cbar = plt.colorbar(im)
    cbar.set_label("Gain")
    plt.tight_layout()
    plt.savefig(outpath, bbox_inches="tight")
    plt.close()


def plot_heatmap_public_private(eps1_values, n_ratios, G, outpath):
    plt.figure(figsize=(7, 6))

    im = plt.pcolormesh(
        eps1_values,
        n_ratios,
        G,
        shading="auto",
        cmap="viridis",
    )
    levels_all = np.linspace(1.01, 2.0, 5)
    levels = [1.15, 1.35]
    cs = plt.contour(
        eps1_values,
        n_ratios,
        G,
        levels=levels_all,
        colors="white",
        linewidths=1.2,
    )
    plt.clabel(cs, levels=[1.2575],  fontsize=12, fmt="%.2f")

    plt.xscale("log")
    plt.yscale("log")
    plt.xlabel(r"$\varepsilon_1$")
    plt.ylabel(r"$n_1 / n_2$")
    cbar = plt.colorbar(im)
    cbar.set_label("Gain")
    plt.tight_layout()
    plt.savefig(outpath, bbox_inches="tight")
    plt.close()


def plot_slices_fixed_n_ratio_two_levels(eps_ratios, n_ratios, G, fixed_n_ratios, outpath):
    plt.figure(figsize=(5, 5))
    cmap = cm.get_cmap("viridis", len(fixed_n_ratios))

    for k, target in enumerate(fixed_n_ratios):
        idx = np.argmin(np.abs(n_ratios - target))
        plt.plot(
            eps_ratios,
            G[idx, :],
            label=rf"$n_1/n_2 = {target}$",
            color=cmap(k),
            linewidth=2,
        )

    plt.xscale("log")
    plt.xlabel(r"$\varepsilon_1 / \varepsilon_2$")
    plt.ylabel("Gain")
    plt.legend()
    plt.tight_layout()
    plt.savefig(outpath, bbox_inches="tight")
    plt.close()


def plot_slices_fixed_eps_ratio_two_levels(eps_ratios, n_ratios, G, fixed_eps_ratios, outpath):
    plt.figure(figsize=(5, 5))
    cmap = cm.get_cmap("viridis", len(fixed_eps_ratios))

    for k, target in enumerate(fixed_eps_ratios):
        idx = np.argmin(np.abs(eps_ratios - target))
        plt.plot(
            n_ratios,
            G[:, idx],
            label=rf"$\varepsilon_1/\varepsilon_2 = {target}$",
            color=cmap(k),
            linewidth=2,
        )

    plt.xscale("log")
    plt.xlabel(r"$n_1 / n_2$")
    plt.ylabel("Gain")
    plt.legend()
    plt.tight_layout()
    plt.savefig(outpath, bbox_inches="tight")
    plt.close()


def plot_slices_fixed_n_ratio_public_private(eps1_values, n_ratios, G, fixed_n_ratios, outpath):
    plt.figure(figsize=(5, 5))
    colors = plt.cm.viridis(np.linspace(0.1, 0.9, len(fixed_n_ratios)))

    for color, target in zip(colors, fixed_n_ratios):
        idx = np.argmin(np.abs(n_ratios - target))
        plt.plot(
            eps1_values,
            G[idx, :],
            label=rf"$n_1/n_2 = {target}$",
            color=color,
            linewidth=2,
        )

    plt.xscale("log")
    plt.xlabel(r"$\varepsilon_1$")
    plt.ylabel("Gain")
    plt.legend()
    plt.tight_layout()
    plt.savefig(outpath, bbox_inches="tight")
    plt.close()


def plot_slices_fixed_eps1_public_private(eps1_values, n_ratios, G, fixed_eps1_values, outpath):
    plt.figure(figsize=(5, 5))
    colors = plt.cm.viridis(np.linspace(0.1, 0.9, len(fixed_eps1_values)))

    for color, target in zip(colors, fixed_eps1_values):
        idx = np.argmin(np.abs(eps1_values - target))
        plt.plot(
            n_ratios,
            G[:, idx],
            label=rf"$\varepsilon_1= {target}$",
            color=color,
            linewidth=2,
        )

    plt.xscale("log")
    plt.xlabel(r"$n_1 / n_2$")
    plt.ylabel("Gain")
    plt.legend()
    plt.tight_layout()
    plt.savefig(outpath, bbox_inches="tight")
    plt.close()


def main():
    # Public-private scenario
    eps1_values = np.geomspace(1e-3, 10, 300)
    n_ratios_public = np.geomspace(1e-3, 1e4, 300)
    G_public = compute_gain_grid_public_private(eps1_values, n_ratios_public, n2=1000)

    plot_heatmap_public_private(
        eps1_values,
        n_ratios_public,
        G_public,
        "public_private_gain_heatmap.pdf",
    )

    plot_slices_fixed_n_ratio_public_private(
        eps1_values,
        n_ratios_public,
        G_public,
        fixed_n_ratios=[0.01, 0.1, 1, 10, 100, 1000],
        outpath="public_private_gain_slices_fixed_n_ratio.pdf",
    )

    plot_slices_fixed_eps1_public_private(
        eps1_values,
        n_ratios_public,
        G_public,
        fixed_eps1_values=[0.001, 0.01, 0.05, 0.1, 0.25, 0.5],
        outpath="public_private_gain_slices_fixed_eps1.pdf",
    )

    # Two-level finite epsilon scenarios
    eps_ratios = np.geomspace(1e-4, 1 - 1e-6, 320)
    n_ratios = np.geomspace(1e-3, 1e4, 340)

    scale = 0.01
    G = compute_gain_grid_two_levels(eps_ratios, n_ratios, scale=scale, n2=1000)

    plot_heatmap_two_levels(
        eps_ratios,
        n_ratios,
        G,
        "two_finite_gain_heatmap_scale_0p01.pdf",
    )

    plot_slices_fixed_n_ratio_two_levels(
        eps_ratios,
        n_ratios,
        G,
        fixed_n_ratios=[0.01, 0.1, 1, 10, 100, 1000],
        outpath="two_finite_gain_slices_fixed_n_ratio_scale_0p01.pdf",
    )

    plot_slices_fixed_eps_ratio_two_levels(
        eps_ratios,
        n_ratios,
        G,
        fixed_eps_ratios=[0.001, 0.01, 0.05, 0.1, 0.25, 0.5],
        outpath="two_finite_gain_slices_fixed_eps_ratio_scale_0p01.pdf",
    )

    scale = 1.0
    G = compute_gain_grid_two_levels(eps_ratios, n_ratios, scale=scale, n2=1000)

    plot_heatmap_two_levels(
        eps_ratios,
        n_ratios,
        G,
        "two_finite_gain_heatmap_scale_1.pdf",
    )

    plot_slices_fixed_n_ratio_two_levels(
        eps_ratios,
        n_ratios,
        G,
        fixed_n_ratios=[0.01, 0.1, 1, 10, 100, 1000],
        outpath="two_finite_gain_slices_fixed_n_ratio_scale_1.pdf",
    )

    plot_slices_fixed_eps_ratio_two_levels(
        eps_ratios,
        n_ratios,
        G,
        fixed_eps_ratios=[0.001, 0.01, 0.05, 0.1, 0.25, 0.5],
        outpath="two_finite_gain_slices_fixed_eps_ratio_scale_1.pdf",
    )


if __name__ == "__main__":
    main()
