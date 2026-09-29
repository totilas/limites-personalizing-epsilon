"""Threshold/personalized ratios for the paper oracle and the training proxy.

Ratios depend on the noise/variance balance, not just the privacy profile.
The paper calculation uses replacement-adjacency zCDP with V/C² supplied by
the caller. The sampled calculation uses the training bound S<=C² and RDP.
Neither quantity is a measured gradient MSE or a ratio of accuracy errors.
"""
from __future__ import annotations

import numpy as np

from optimal_weights import optimal_capped_weights
from privacy import epsilon_to_u


def compare_resources(resources, counts, penalty):
    """Optimize sum(w²)+penalty*max(w/u)² over thresholds and all weights."""
    u, n = np.asarray(resources, dtype=float), np.asarray(counts, dtype=float)
    if np.any(~np.isfinite(n)) or np.any(n <= 0):
        raise ValueError("counts must be finite and positive")
    weights, cap = optimal_capped_weights(u, n, penalty)
    finite = np.isfinite(u)

    def risk(a):
        sensitivity = float(np.max(a[finite]/u[finite], initial=0.))
        return float((np.sum(n*a*a) + penalty*sensitivity**2)/np.sum(n*a)**2)

    thresholds = [(risk((u >= t).astype(float)), float(t)) for t in np.unique(u)]
    threshold_risk, threshold = min(thresholds)
    personalized_risk = risk(weights)
    return dict(threshold_risk=threshold_risk, personalized_risk=personalized_risk,
                ratio=threshold_risk/personalized_risk,
                threshold_resource=threshold, cap_resource=cap)


def paper_ratio(epsilons, counts, *, steps, dimension, delta=1e-5, variance_over_c2=1.):
    """Paper's Gaussian replacement oracle, equally composed over T releases.

    Total epsilon is converted to rho, with per-release u=sqrt(rho/T).
    Risks returned are divided by V; ratio is unaffected. V=C² gives a
    conservative variance-bound comparison, not the unknown exact oracle MSE.
    There is NO subsampling amplification in this paper formula.
    """
    if steps <= 0 or dimension <= 0 or not 0 < variance_over_c2 <= 1:
        raise ValueError("positive steps/dimension and 0<V/C²<=1 required")
    u = epsilon_to_u(np.asarray(epsilons, dtype=float), delta)/np.sqrt(steps)
    return compare_resources(u, counts, 2.*dimension/variance_over_c2)


def sampled_ratio(epsilons, counts, *, steps, dimension, sample_rate, delta=1e-5):
    """Same S<=C² sampled-RDP bound optimized by --auto-weights in train.py."""
    from sampled_privacy import _required_noise_multiplier
    eps = np.asarray(epsilons, dtype=float)
    z = np.array([0. if np.isinf(e) else _required_noise_multiplier(
        float(e), delta, sample_rate, steps) for e in eps])
    u = np.divide(1., z, out=np.full_like(z, np.inf), where=z > 0)
    return compare_resources(u, counts, dimension/sample_rate)
