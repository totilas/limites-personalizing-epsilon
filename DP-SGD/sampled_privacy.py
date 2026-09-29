"""Uniform-Poisson accounting for fixed heterogeneous gradient weights."""

from __future__ import annotations

import math
from dataclasses import dataclass
from functools import lru_cache

import numpy as np
from opacus.accountants import RDPAccountant
from opacus.accountants.analysis import rdp
from scipy.special import gammaln, logsumexp

from privacy import ThresholdRisk, epsilon_to_u
from optimal_weights import optimal_capped_weights


def _rdp_orders(epsilon: float, delta: float) -> list[float]:
    """Return an RDP-order grid large enough for small epsilon budgets.

    Opacus' default grid ends at order 63.  Independently of the noise level,
    that grid cannot certify very small epsilon values when delta is small.
    The useful order is approximately 2*log(1/delta)/epsilon; we extend to
    twice that estimate and use a geometric grid to keep calibration cheap.
    Every order still gives a valid (conservative) RDP bound.
    """
    orders = list(RDPAccountant.DEFAULT_ALPHAS)
    required_max = max(63, math.ceil(4.0 * math.log(1.0 / delta) / epsilon) + 1)
    order = 64
    while order < required_max:
        orders.append(float(order))
        order = max(order + 1, math.ceil(order * 1.25))
    orders.append(float(required_max))
    return sorted(set(orders))


@dataclass(frozen=True)
class SampledMechanism:
    raw_weights: np.ndarray
    noise_multiplier: float
    expected_weight_mass: float
    sample_rate: float
    steps: int
    retained: int
    effective_sample_size: float
    max_privacy_utilization: float
    budget_levels: np.ndarray
    level_weights: np.ndarray
    audit: list[dict]
    selection: dict


def raw_weights(
    epsilon: np.ndarray,
    method: str,
    parameter_epsilon: float | None,
    delta: float,
) -> np.ndarray:
    eps = np.asarray(epsilon, dtype=np.float64)
    if method == "nonprivate":
        return np.ones_like(eps)
    if parameter_epsilon is None:
        raise ValueError("parameter_epsilon is required for private mechanisms")
    if method == "threshold":
        if math.isinf(parameter_epsilon):
            return np.isposinf(eps).astype(np.float64)
        if parameter_epsilon <= 0:
            raise ValueError("threshold epsilon must be positive")
        return (eps >= parameter_epsilon).astype(np.float64)
    if method == "personalized":
        if not math.isfinite(parameter_epsilon) or parameter_epsilon <= 0:
            raise ValueError("the personalized cap epsilon must be finite and positive")
        cap = float(epsilon_to_u(parameter_epsilon, delta))
        return np.minimum(epsilon_to_u(eps, delta), cap)
    raise ValueError("unknown method")


@lru_cache(maxsize=None)
def _required_noise_multiplier(
    epsilon: float, delta: float, sample_rate: float, steps: int
) -> float:
    # Return the feasible side of a relative-accuracy binary search.
    low, high = 0.0, 1.0
    while _achieved_epsilon(high, sample_rate, steps, delta, epsilon) > epsilon:
        high *= 2
        if high > 1e8:
            raise ValueError("could not bracket a finite noise multiplier")
    while high - low > 1e-5 * high:
        mid = (low + high) / 2
        if _achieved_epsilon(mid, sample_rate, steps, delta, epsilon) <= epsilon:
            high = mid
        else:
            low = mid
    return high


def _achieved_epsilon(
    noise_multiplier: float,
    sample_rate: float,
    steps: int,
    delta: float,
    target_epsilon: float,
) -> float:
    if steps == 0:
        return 0.0
    alphas = _rdp_orders(target_epsilon, delta)
    basic = [a for a in alphas if a <= 512]
    values = list(rdp.compute_rdp(q=sample_rate, noise_multiplier=noise_multiplier,
                                 steps=steps, orders=basic))
    # Opacus 1.5.4 evaluates binomial coefficients before taking logs. For
    # integer alpha >~1024 this overflows. Same formula, entirely in log space.
    for alpha in alphas[len(basic):]:
        if sample_rate == 1:
            value = alpha / (2 * noise_multiplier**2)
        else:
            k = np.arange(int(alpha) + 1, dtype=float)
            terms = (gammaln(alpha + 1) - gammaln(k + 1) - gammaln(alpha - k + 1)
                     + k*np.log(sample_rate) + (alpha-k)*np.log1p(-sample_rate)
                     + (k*k-k)/(2*noise_multiplier**2))
            value = max(0.0, float(logsumexp(terms)) / (alpha - 1))
        values.append(steps * value)
    return float(rdp.get_privacy_spent(orders=alphas, rdp=values, delta=delta)[0])


def calibrate_sampled_mechanism(
    epsilon: np.ndarray,
    method: str,
    parameter_epsilon: float | None,
    delta: float,
    sample_rate: float,
    steps: int,
    *,
    optimize: bool = False,
    dimension: int | None = None,
) -> SampledMechanism:
    """Calibrate one common sum-noise multiplier for fixed record weights.

    The accounting uses the add/remove neighboring relation of the standard
    Poisson-sampled Gaussian mechanism. A record with raw gradient multiplier
    ``a_i`` sees effective noise multiplier ``sigma / a_i``. The released noisy
    weighted sum is divided by its public expected mass only after noising.
    """
    if not 0 < sample_rate <= 1:
        raise ValueError("sample_rate must lie in (0, 1]")
    if steps <= 0:
        raise ValueError("steps must be positive")
    if not 0 < delta < 1:
        raise ValueError("delta must lie in (0, 1)")
    eps = np.asarray(epsilon, dtype=np.float64)
    if eps.ndim != 1 or not len(eps) or np.any(np.isnan(eps)) or np.any(eps <= 0):
        raise ValueError("budgets must be positive finite values or +infinity")
    levels, inverse, counts = np.unique(eps, return_inverse=True, return_counts=True)
    selection = {"weight_rule": "legacy_zcdp_cap" if method == "personalized" else method}
    if optimize:
        if method not in ("threshold", "personalized") or dimension is None or dimension <= 0:
            raise ValueError("automatic weights require a private method and positive dimension")
        required = np.array([0.0 if np.isinf(e) else _required_noise_multiplier(
            float(e), delta, sample_rate, steps) for e in levels])
        penalty = dimension / sample_rate
        if method == "threshold":
            candidates = []
            for e in levels:
                keep = levels >= e
                mass = float(counts[keep].sum())
                sigma = float(required[keep].max())
                score = 1.0 / mass + penalty * (sigma/mass)**2
                candidates.append((score, float(e)))
            _, threshold = min(candidates)
            group_weights = (levels >= threshold).astype(float)
            selection["threshold_epsilon"] = "inf" if math.isinf(threshold) else threshold
            selection["threshold_candidates"] = [
                {"epsilon": "inf" if math.isinf(e) else e, "mse_bound_over_C2": score/sample_rate}
                for score, e in candidates]
        else:
            resources = np.divide(1.0, required, out=np.full_like(required, np.inf), where=required > 0)
            group_weights, cap = optimal_capped_weights(resources, counts, penalty)
            selection["cap_reciprocal_noise"] = "inf" if math.isinf(cap) else cap
        weights = group_weights[inverse]
        selection["weight_rule"] = "sampled_rdp_mse_bound_optimum"
        total = float(weights.sum())
        sigma_bound = float(np.max(group_weights * required))
        selection["mse_bound_over_C2"] = float(
            np.sum(weights**2)/(sample_rate*total**2)
            + dimension*(sigma_bound/(sample_rate*total))**2)
    else:
        weights = raw_weights(eps, method, parameter_epsilon, delta)
    total_weight = float(weights.sum())
    if total_weight == 0:
        raise ValueError("the mechanism retains no records")

    active_private = (weights > 0) & np.isfinite(eps)
    audit = []
    if method == "nonprivate":
        sigma = 0.0
        max_utilization = 0.0
    elif not np.any(active_private):
        sigma = 0.0
        max_utilization = 0.0
    else:
        pairs = np.unique(
            np.column_stack((eps[active_private], weights[active_private])), axis=0
        )
        sigma = max(
            float(weight)
            * _required_noise_multiplier(
                float(target_epsilon), delta, sample_rate, steps
            )
            for target_epsilon, weight in pairs
        )
        utilizations = []
        for target_epsilon, weight in pairs:
            achieved = _achieved_epsilon(
                sigma / float(weight),
                sample_rate,
                steps,
                delta,
                float(target_epsilon),
            )
            utilizations.append(achieved / float(target_epsilon))
            audit.append({"target_epsilon": float(target_epsilon), "raw_weight": float(weight),
                          "effective_noise_multiplier": sigma / float(weight),
                          "achieved_epsilon": achieved, "steps": steps, "delta": delta})
        max_utilization = max(utilizations)
        if not np.isfinite(max_utilization) or max_utilization > 1 + 1e-8:
            raise RuntimeError("calibrated mechanism exceeds a requested privacy budget")

    normalized = weights / total_weight
    return SampledMechanism(
        raw_weights=weights,
        noise_multiplier=sigma,
        expected_weight_mass=sample_rate * total_weight,
        sample_rate=sample_rate,
        steps=steps,
        retained=int(np.count_nonzero(weights)),
        effective_sample_size=float(1.0 / np.sum(normalized**2)),
        max_privacy_utilization=float(max_utilization),
        budget_levels=levels,
        level_weights=np.array([weights[np.flatnonzero(eps == level)[0]] for level in levels]),
        audit=audit,
        selection=selection,
    )


def rank_sampled_thresholds(
    epsilon: np.ndarray,
    delta: float,
    sample_rate: float,
    steps: int,
    clip_norm: float,
    dimension: int,
    gradient_variance: float,
) -> list[ThresholdRisk]:
    """Rank actual profile thresholds under the sampled-RDP mechanism."""
    eps = np.asarray(epsilon, dtype=np.float64)
    candidates = [float(value) for value in np.unique(eps[np.isfinite(eps)])]
    if np.isposinf(eps).any():
        candidates.append(float("inf"))
    risks = []
    for threshold in candidates:
        mechanism = calibrate_sampled_mechanism(
            eps, "threshold", threshold, delta, sample_rate, steps
        )
        normalized_noise = (
            clip_norm
            * mechanism.noise_multiplier
            / mechanism.expected_weight_mass
        )
        risks.append(
            ThresholdRisk(
                epsilon=threshold,
                retained=mechanism.retained,
                # Conservative population-oracle proxy: the argument must
                # bound the SECOND MOMENT of clipped gradients (C² is safe).
                sampling_risk=gradient_variance / (sample_rate * mechanism.retained),
                privacy_risk=dimension * normalized_noise**2,
            )
        )
    return sorted(risks, key=lambda item: item.total_risk)
