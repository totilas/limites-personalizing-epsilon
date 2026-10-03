# Lean formalization — *Limits of Personalizing Differential Privacy Budgets*

**Disclaimer.** The correctness of the paper rests on its written proofs, read and
checked in the usual way. This Lean development is a complement to them, not a
replacement: an independent machine check of the statements, and a step towards
systematizing this body of knowledge in Lean.

**Scope.** It covers most of the formal claims of the paper: every theorem,
proposition, corollary and lemma, and the mathematical content of the remarks,
including the privacy guarantees, the mean-squared errors, and convergence in
expectation. It compiles against Mathlib v4.33.0 with no `sorry`, and the main
theorems use only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). Not covered:
- the cited Shamir–Zhang theorem;
- the `O(n log n)` running time for computing the optimal cap;
- the link between the risk formula and actual mechanisms when some records are
  public. The public-data bounds themselves are proved on the risk formulas.

```bash
lake exe cache get   # download precompiled Mathlib (once)
lake build
```

## Files

Main theorems are stated for the infima `persRisk` (𝓡_pers) and `thrRisk` (𝓡_thr),
for arbitrary constants `A, B > 0`. Mean estimation is `A = 1/4, B = 2`; the
DP-SGD gradient oracle is `A = V, B = 2dC²`. Numbers below refer to the paper's
PDF. (Docstrings inside the `.lean` files cite the LaTeX labels instead.)

### `Risks.lean` — the two risks

| Paper | Lean |
|---|---|
| Definition 7 (personalized and threshold risks) | `persRisk`, `thrRisk` (with `persObj`, `thrObj`, `Feasible`, `nThr`) |

### `Privacy/Defs.lean`, `OneStep.lean` — privacy definitions

| Paper | Lean |
|---|---|
| Definition 1 (approximate DP), Definition 4 (heterogeneous DP) | `ApproxDP`, `HetDP`, `NeighborAt` |
| Definition 3 (arbitrary personalized DP) and the folklore result after it (Section II) | `ArbitraryPersonalizedDP`, `ArbitraryPersonalizedDP.approxDP` |
| Lemma 5 (per-record preprocessing) | `HetDP.comp_preprocess` |
| Remark 1 (single gradient release is heterogeneous mean estimation) | `oneStepMinimaxRisk_le_meanEstMinimaxRisk`, `oneStepMinimaxRisk_linear`, `sSup_oneStepMinimaxRisk` |

### `Laplace.lean`, `MeanEstimation.lean` — mean estimation mechanisms

| Paper | Lean |
|---|---|
| Laplace distribution (not in Mathlib) | `laplace`, `variance_id_laplace` |
| Definition 2 (Laplace mechanism, "is (ε,0)-DP") | `laplaceMech_approxDP` |
| Section III-B: the affine estimator is DP iff `η ≥ maxᵢ wᵢ/εᵢ` | `affineMech_hetDP_iff` |
| Definition 5 (DR-MSE); its value for affine estimators | `drMSE_affineMech` |
| Lemma 1, first equality of Eq. (1) | `sInf_affRiskSet` |
| Definition 6 (unique-threshold estimator), Eq. (2) | `thrMech_hetDP`, `drMSE_thrMech`, `sInf_thrRiskSet` |
| Proof of Theorem 3 (Appendix E), the case P = δ₀ | `mse_thrMech_dirac_zero` |

### `Characterization.lean` — exact formulas and examples

| Paper | Lean |
|---|---|
| Lemma 2, Part 1 (capped weights) | `capped_weights`, `capped_feasible` |
| Lemma 1, second equality of Eq. (1) | `threshold_characterization` |
| Lemma 3 (Appendix D) | `threshold_vs_affine` |
| Public-private risks (proof of Theorem 1) | `public_thrRisk_eq`, `public_persRisk_eq` |
| Tightness of Theorem 1 and the ≈1.95 example (after Theorem 1) | `public_factor_two_tight`, `public_example` |
| Example 1 (computed in Appendix C) | `two_level_example` |
| Section VI-A: an optimal threshold can be taken at a budget level | `thrRisk_eq_min_levels` |
| Section VI-A and Appendix F-B: closed form of the optimal cap | `cap_objective_ge_stationary`, `cap_objective_antitone`, `cap_objective_monotone`, `cap_objective_hasDerivAt` |

### `PublicPrivate.lean` — Section IV

| Paper | Lean |
|---|---|
| Theorem 1 | `public_data_factor_two` |
| Proposition 3 (Appendix E) | `direct_factor_two` |

### `GeneralCase.lean` — Section V

| Paper | Lean |
|---|---|
| Lemma 2, Part 2 (exact rescaling) | `rescaling_pers`, `rescaling_thr` |
| Theorem 2 | `upper_bound` |
| Proposition 5 (Appendix E); the `H_n²` bound | `direct_factor_m_sq`; `direct_factor_harmonic` |
| Corollary 1, Proposition 4 (Appendix E) | `two_level_factor_four`, `direct_factor_four` |
| Theorem 3 | `LowerBound.lower_bound`, `LowerBound.lower_bound_log` |

### `Renyi.lean`, `GaussianOracle.lean` — the DP-SGD gradient oracle

| Paper | Lean |
|---|---|
| Rényi divergence, zCDP, Gaussian mechanism | `renyiDiv`, `HetZCDP`, `renyiDiv_gaussNoise`, `gaussMech_zCDP` |
| Proposition 1, Eqs. (9)–(10) (privacy, MSE) | `affineRelease_hetZCDP_iff`, `affineMSE_eq`, `affineMSE_le` |
| Definition 8, Eq. (11) | `persOracleMSE_eq` |
| Eq. (12) (threshold oracle) | `thrRelease_hetZCDP`, `thrMSE_eq`, `thrOracleMSE_eq` |
| Remark after Lemma 5: preprocessing preserves zCDP | `hetZCDP_preprocess` |

### `DPSGD.lean` — Section VI

| Paper | Lean |
|---|---|
| Theorem 4 | `gradient_personalization_gap` |
| Lemma 4 (bias attenuation) | `bias_attenuation_eq`, `bias_attenuation_le` |
| Lemma 6 (budget rescaling) | `budget_scaling_pers`, `budget_scaling_thr` |
| Remark 3 (additional iterations at a fixed total budget) | `extra_iterations_le` |
| Proposition 6, Claim 2 | `composition_ratio`, `composition_ratio_public` |

### `Convergence.lean` — convergence in expectation

| Paper | Lean |
|---|---|
| Proposition 2 | `quadratic_unit_step_expectation`, `quadratic_general`, `quadratic_ratio`, `quadratic_ratio_tendsto` |
| Theorem 5 | `noise_ball_expectation`, `noise_ball_slow_expectation`, `noise_ball_limsup`, `ball_comparison` |
| Step 1 of the proof of Theorem 5 (Appendix F-F) | `coercivity`, `gradient_step_contraction` |
| Remark 5 (non-constant step sizes) | `varying_steps_bound`, `varying_steps_ratio` |
| Proposition 6, Claim 3 | `quadratic_sq_dist_tendsto`, `isotropic_radius_ratio` |
| Remark 4 (non-smooth strongly convex objectives) | `nonsmooth_second_moment`, `nonsmooth_ratio` |
