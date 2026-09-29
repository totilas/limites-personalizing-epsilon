"""Privacy profiles and calibration for heterogeneous zCDP-SGD."""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np


PROFILE_NAMES = (
    "public_private",
    "uniform_eps1",
    "uniform_eps4",
    "uniform_eps8",
    "eps1_eps01",
    "eps1_eps001",
    "eps4_eps1",
    "eps8_eps1",
    "eps8_eps4",
    "survey",
    "two_level",
)


def epsilon_to_u(epsilon: np.ndarray | float, delta: float) -> np.ndarray:
    """Find u=sqrt(rho) sufficient to meet a target (epsilon, delta).

    This inverts rho+2*sqrt(rho*log(1/delta))=epsilon; it does NOT
    assert that an arbitrary (epsilon, delta)-DP mechanism is rho-zCDP.

    Public records are represented by epsilon=+infinity and map to u=+infinity.
    """
    eps = np.asarray(epsilon, dtype=np.float64)
    if not 0.0 < delta < 1.0:
        raise ValueError("delta must lie in (0, 1)")
    log_delta = math.log(1.0 / delta)
    with np.errstate(invalid="ignore"):
        u = np.sqrt(log_delta + eps) - math.sqrt(log_delta)
    return np.where(np.isposinf(eps), np.inf, u)


def u_to_epsilon(u: np.ndarray | float, delta: float) -> np.ndarray:
    """Convert u=sqrt(rho) back to the sufficient (epsilon, delta) bound."""
    values = np.asarray(u, dtype=np.float64)
    log_delta = math.log(1.0 / delta)
    return values**2 + 2.0 * values * math.sqrt(log_delta)


def _scaled_counts(n: int, proportions: list[float]) -> list[int]:
    expected = np.asarray(proportions, dtype=np.float64) * n
    counts = np.floor(expected).astype(int)
    order = np.argsort(-(expected - counts), kind="stable")
    for index in order[: n - int(counts.sum())]:
        counts[index] += 1
    return counts.tolist()


def make_profile(
    name: str,
    n: int,
    seed: int,
    private_epsilon: float = 1.0,
    *, epsilon_1: float = 1.0, epsilon_2: float = 0.1,
    group_1_fraction: float = 0.2,
) -> np.ndarray:
    """Create a shuffled, data-independent epsilon assignment.

    Counts are exact for n=50,000 and proportionally scaled for tuning subsets.
    """
    if name not in PROFILE_NAMES:
        raise ValueError(f"unknown profile {name!r}; choose from {PROFILE_NAMES}")
    if n <= 0:
        raise ValueError("n must be positive")
    rng = np.random.default_rng(seed)

    if name == "two_level":
        if not all(math.isfinite(e) and e > 0 for e in (epsilon_1, epsilon_2)):
            raise ValueError("two-level epsilons must be finite and positive")
        if not 0 < group_1_fraction < 1:
            raise ValueError("group-1-fraction must lie strictly between zero and one")
        n1, n2 = _scaled_counts(n, [group_1_fraction, 1-group_1_fraction])
        if min(n1, n2) == 0:
            raise ValueError("two-level profile requires at least one record per group")
        eps = np.concatenate([np.full(n1, epsilon_1), np.full(n2, epsilon_2)])
    elif name == "public_private":
        n_public, n_private = _scaled_counts(n, [0.2, 0.8])
        eps = np.concatenate(
            [np.full(n_public, np.inf), np.full(n_private, private_epsilon)]
        )
    elif name.startswith("uniform_eps"):
        value = float(name.removeprefix("uniform_eps"))
        eps = np.full(n, value, dtype=np.float64)
    elif name == "eps1_eps01":
        n_high, n_low = _scaled_counts(n, [0.2, 0.8])
        eps = np.concatenate([np.full(n_high, 1.0), np.full(n_low, 0.1)])
    elif name == "eps1_eps001":
        n_high, n_low = _scaled_counts(n, [0.2, 0.8])
        eps = np.concatenate([np.full(n_high, 1.0), np.full(n_low, 0.01)])
    elif name == "eps4_eps1":
        n_high, n_low = _scaled_counts(n, [0.2, 0.8])
        eps = np.concatenate([np.full(n_high, 4.0), np.full(n_low, 1.0)])
    elif name == "eps8_eps1":
        n_high, n_low = _scaled_counts(n, [0.2, 0.8])
        eps = np.concatenate([np.full(n_high, 8.0), np.full(n_low, 1.0)])
    elif name == "eps8_eps4":
        n_high, n_low = _scaled_counts(n, [0.2, 0.8])
        eps = np.concatenate([np.full(n_high, 8.0), np.full(n_low, 4.0)])
    else:
        # Jorgensen, Yu & Cormode (ICDE 2015): f_C=.54, f_M=.37, f_L=.09.
        n_conservative, n_moderate, n_liberal = _scaled_counts(
            n, [0.54, 0.37, 0.09]
        )
        conservative = np.round(rng.uniform(0.01, 0.20, n_conservative), 2)
        moderate = np.round(rng.uniform(0.20, 1.00, n_moderate), 2)
        eps = np.concatenate(
            [conservative, moderate, np.ones(n_liberal, dtype=np.float64)]
        )

    return eps[rng.permutation(n)]


@dataclass(frozen=True)
class BatchMechanism:
    raw_weights: np.ndarray
    noise_std: float
    retained: int


@dataclass(frozen=True)
class ThresholdRisk:
    epsilon: float
    retained: int
    sampling_risk: float
    privacy_risk: float

    @property
    def total_risk(self) -> float:
        return self.sampling_risk + self.privacy_risk


def rank_feasible_thresholds(
    epsilon: np.ndarray,
    delta: float,
    epochs: int,
    clip_norm: float,
    dimension: int,
    gradient_variance: float,
) -> list[ThresholdRisk]:
    """Rank thresholds from the profile using the paper's oracle-MSE formula.

    Only values actually assigned to records are considered. If public records
    exist, +infinity is also a feasible threshold and has zero privacy noise.
    The supplied privacy requirements are total budgets, so composition over
    ``epochs`` multiplies the one-release privacy term by ``epochs``.
    """
    eps = np.asarray(epsilon, dtype=np.float64)
    if epochs <= 0 or clip_norm <= 0 or dimension <= 0:
        raise ValueError("epochs, clip_norm, and dimension must be positive")
    if gradient_variance < 0:
        raise ValueError("gradient_variance must be nonnegative")
    candidates = [float(value) for value in np.unique(eps[np.isfinite(eps)])]
    if np.isposinf(eps).any():
        candidates.append(float("inf"))

    risks = []
    for threshold in candidates:
        retained = int(np.count_nonzero(eps >= threshold))
        if retained == 0:
            continue
        sampling = gradient_variance / retained
        if math.isinf(threshold):
            privacy = 0.0
        else:
            u_total = float(epsilon_to_u(threshold, delta))
            privacy = (
                2.0
                * dimension
                * clip_norm**2
                * epochs
                / (u_total**2 * retained**2)
            )
        risks.append(ThresholdRisk(threshold, retained, sampling, privacy))
    return sorted(risks, key=lambda item: item.total_risk)


def batch_mechanism(
    epsilon: np.ndarray,
    method: str,
    parameter_epsilon: float,
    delta: float,
    epochs: int,
    clip_norm: float,
) -> BatchMechanism:
    """Return unnormalized weights and Gaussian std for one logical batch.

    A record occurs in one logical batch per epoch. Giving each occurrence
    rho_i / epochs composes to its requested total rho_i after all epochs.
    """
    if epochs <= 0 or clip_norm <= 0:
        raise ValueError("epochs and clip_norm must be positive")
    eps = np.asarray(epsilon, dtype=np.float64)
    u_total = epsilon_to_u(eps, delta)

    if method == "nonprivate":
        raw = np.ones_like(eps)
        ratio = 0.0
    elif method == "threshold":
        if math.isinf(parameter_epsilon):
            raw = np.isposinf(eps).astype(np.float64)
            ratio = 0.0
        else:
            if parameter_epsilon <= 0:
                raise ValueError("threshold epsilon must be positive")
            raw = (eps >= parameter_epsilon).astype(np.float64)
            threshold_u_step = float(epsilon_to_u(parameter_epsilon, delta)) / math.sqrt(
                epochs
            )
            retained = int(raw.sum())
            ratio = 0.0 if retained == 0 else 1.0 / (retained * threshold_u_step)
    elif method == "personalized":
        if not math.isfinite(parameter_epsilon) or parameter_epsilon <= 0:
            raise ValueError("the personalized cap epsilon must be finite and positive")
        cap_u = float(epsilon_to_u(parameter_epsilon, delta))
        raw = np.minimum(u_total, cap_u)
        denominator = float(raw.sum())
        if denominator == 0.0:
            ratio = 0.0
        else:
            coefficients = raw / denominator
            private = np.isfinite(u_total)
            u_step = u_total[private] / math.sqrt(epochs)
            ratio = float(np.max(coefficients[private] / u_step, initial=0.0))
    else:
        raise ValueError("method must be 'nonprivate', 'threshold', or 'personalized'")

    retained = int(np.count_nonzero(raw))
    noise_std = math.sqrt(2.0) * clip_norm * ratio
    return BatchMechanism(raw_weights=raw, noise_std=noise_std, retained=retained)


def achieved_epsilons(noise_std: float, coefficients: np.ndarray, clip_norm: float, delta: float) -> np.ndarray:
    """Audit per-record epsilon for one Gaussian release (no composition)."""
    coefficients = np.asarray(coefficients, dtype=np.float64)
    if noise_std == 0.0:
        return np.where(coefficients == 0.0, 0.0, np.inf)
    u = math.sqrt(2.0) * clip_norm * coefficients / noise_std
    return u_to_epsilon(u, delta)
