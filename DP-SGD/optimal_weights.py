"""Closed-form weights for a public, conservative sampled-gradient MSE proxy.

No data, gradients, or validation scores enter this calculation. With normalized
weights w, inclusion probability q, and ||clipped gradient|| <= C, the iid
population-oracle risk is bounded by
    C²/q * sum(w²) + d*C²/q² * max(w_i * required_sigma_i)².
This is a population proxy, NOT a guarantee for adaptive CNN optimization.
"""
from __future__ import annotations

import numpy as np


def optimal_capped_weights(resources, counts, noise_penalty):
    """Minimize [sum(n*a²) + penalty*max(a/u)²] / sum(n*a)².

For each interval of caps, the stationary point is
tau=(sum_saturated n*u² + penalty)/sum_saturated n*u.
Public u=inf entries are never saturated. Counts avoid expanding to N records.
The cap is on reciprocal-noise resources, not the epsilon scale.
"""
    u, n = np.asarray(resources, dtype=float), np.asarray(counts, dtype=float)
    if u.ndim != 1 or u.shape != n.shape or not len(u):
        raise ValueError("resources and counts must be nonempty 1D arrays")
    if np.any(np.isnan(u)) or np.any(u <= 0) or np.any(n <= 0) or noise_penalty <= 0:
        raise ValueError("positive resources, counts and noise penalty required")
    finite = np.isfinite(u)
    if not finite.any():
        return np.ones_like(u), float("inf")
    levels = np.unique(u[finite])
    candidates = list(levels)
    for k, low in enumerate(levels):
        active = finite & (u <= low)
        stationary = (np.sum(n[active] * u[active]**2) + noise_penalty) / np.sum(n[active] * u[active])
        high = levels[k + 1] if k + 1 < len(levels) else float("inf")
        if stationary <= high:
            candidates.append(max(low, stationary))
    def risk(cap):
        a = np.minimum(u, cap)
        return (np.sum(n*a*a) + noise_penalty) / np.sum(n*a)**2
    cap = min(candidates, key=risk)
    # Common rescaling changes neither the normalized gradient nor its noise.
    a = np.minimum(u, cap)
    return a / a.max(), float(cap)
