import LimitesProofs.PublicPrivate
import LimitesProofs.GeneralCase

/-!
# Section `sec:learning-formal`: personalized DP-SGD

* `gradient_personalization_gap` — Thm. `thm:gradient-personalization-gap`: the
  bounds of `PublicPrivate` and `GeneralCase` at `A = V(θ)`, `B = 2dC²`.
* `bias_attenuation_eq`, `bias_attenuation_le` — Lemma `lem:bias`.
* `quadratic_recursion`, `quadratic_unit_step` — Prop. `prop:quadratic-propagation`
  (Eqs. `eq:quadratic-general` and `eq:quadratic-explicit-convergence`).
* `noise_ball`, `noise_ball_slow` — Thm. `thm:ball-comparison`, Claims 1 and 2.
* `budget_scaling_pers`, `budget_scaling_thr` — Lemma `lem:budget-scaling`.
* `extra_iterations_le` — Remark `rem:fixed-total-budget`.
* `composition_ratio`, `composition_ratio_public` — Prop. `prop:ball-comparison-detailed`, Claim 2.
* `ball_radius_ratio` — Prop. `prop:ball-comparison-detailed`, Claims 2–3.

The convergence statements are about the recursions satisfied by
`xₜ = E‖θₜ − θ*‖²`.  Not formalized: Prop. `prop:affine-gradient-formal` (zCDP
guarantee and noise moments), Remark `rem:one-step-equivalence`, the contraction
step (Step 1 of the proof of Thm. `thm:ball-comparison`), and the
conditional-expectation steps that produce the recursions.
-/

open Finset

namespace Limites

/-! ## Thm. `thm:gradient-personalization-gap` -/

/-- **Thm. `thm:gradient-personalization-gap`.**  With `A = V(θ)` and `B = 2dC²`:
(1) one finite level plus public gradients gives `r_g ≤ 2`; (2) `m` distinct finite
levels give `r_g ≤ min{(1 + log₂ n)², m²}`, hence `≤ 4` for two levels; (3) the
equal-revenue profile with budgets `2^{-(i-1)} √(2dC²/(8V))` has `r_g ≥ m²/5`. -/
theorem gradient_personalization_gap (V d C : ℝ) (hV : 0 < V) (hd : 0 < d) (hC : 0 < C) :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (pub : Finset ι) (u : ι → ℝ) (ε₁ : ℝ),
        0 < ε₁ → pub.Nonempty → pubᶜ.Nonempty → (∀ i ∉ pub, u i = ε₁) →
        thrRisk pub u V (2 * d * C ^ 2) ≤ 2 * persRisk pub u V (2 * d * C ^ 2)) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (u : ι → ℝ), (∀ i, 0 < u i) →
        thrRisk ∅ u V (2 * d * C ^ 2) ≤
          min ((1 + Real.logb 2 (Fintype.card ι)) ^ 2) ((#(univ.image u) : ℝ) ^ 2)
            * persRisk ∅ u V (2 * d * C ^ 2)) ∧
    (∀ m : ℕ, 0 < m →
        (m : ℝ) ^ 2 / 5 * persRisk ∅ (LowerBound.budget m V (2 * d * C ^ 2)) V (2 * d * C ^ 2)
          ≤ thrRisk ∅ (LowerBound.budget m V (2 * d * C ^ 2)) V (2 * d * C ^ 2)) := by
  have hB : 0 < 2 * d * C ^ 2 := by positivity
  exact ⟨fun pub u ε₁ hε₁ hpub hpriv hu =>
      public_data_factor_two pub u ε₁ V _ hε₁ hV hB hpub hpriv hu,
    fun u hu => upper_bound u hu hV hB,
    fun m hm => LowerBound.lower_bound m hm hV hB⟩

/-! ## Lemma `lem:bias` (bias attenuation) -/

/-- `(b₀ + c x)/(b₀ + c y) = 1 + (x/y - 1)/(1 + b₀/(c y))`. -/
theorem bias_attenuation_eq (b₀ c x y : ℝ) (hb₀ : 0 ≤ b₀) (hc : 0 < c) (hy : 0 < y) :
    (b₀ + c * x) / (b₀ + c * y) = 1 + (x / y - 1) / (1 + b₀ / (c * y)) := by
  have hcy : 0 < c * y := by positivity
  have hden : 0 < b₀ + c * y := by positivity
  field_simp
  ring

/-- The total-risk ratio is at most the reduced-risk ratio `x/y`. -/
theorem bias_attenuation_le (b₀ c x y : ℝ) (hb₀ : 0 ≤ b₀) (hc : 0 < c) (hy : 0 < y)
    (hxy : y ≤ x) :
    (b₀ + c * x) / (b₀ + c * y) ≤ x / y := by
  rw [div_le_div_iff₀ (by positivity) hy]
  nlinarith [mul_nonneg hb₀ (sub_nonneg.mpr hxy)]

/-! ## Prop. `prop:quadratic-propagation` -/

/-- Closed form of the recursion `x_{t+1} = a² xₜ + c` (Eq. `eq:quadratic-general`,
with `a² = (1 − ημ)²` and `c = η² 𝒱`): for `a² ≠ 1`,
`x_T = a^{2T} x₀ + c (1 − a^{2T})/(1 − a²)`. -/
theorem quadratic_recursion (a2 c : ℝ) (ha : a2 ≠ 1) (x : ℕ → ℝ)
    (h : ∀ t, x (t + 1) = a2 * x t + c) (T : ℕ) :
    x T = a2 ^ T * x 0 + c * (1 - a2 ^ T) / (1 - a2) := by
  have h1 : (1:ℝ) - a2 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  induction T with
  | zero => simp
  | succ T ih =>
    rw [h T, ih, pow_succ]
    field_simp
    ring

/-- Eq. `eq:quadratic-explicit-convergence`: at step size `η = 1/μ`, the excess
risk `(μ/2) x_T` equals `𝒱/(2μ)` for every `T ≥ 1`. -/
theorem quadratic_unit_step (μ V : ℝ) (hμ : μ ≠ 0) (x : ℕ → ℝ)
    (h : ∀ t, x (t + 1) = (1 - 1 / μ * μ) ^ 2 * x t + (1 / μ) ^ 2 * V)
    (T : ℕ) (hT : 1 ≤ T) :
    μ / 2 * x T = V / (2 * μ) := by
  obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le' hT
  rw [h T, one_div_mul_cancel hμ, sub_self]
  field_simp
  ring

/-! ## Thm. `thm:ball-comparison` -/

/-- If `x_{t+1} ≤ κ xₜ + c` with `0 ≤ κ < 1` and `c ≥ 0`, then
`x_T ≤ κ^T x₀ + c/(1−κ)`. -/
theorem ball_recursion (κ c : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hc : 0 ≤ c)
    (x : ℕ → ℝ) (h : ∀ t, x (t + 1) ≤ κ * x t + c) (T : ℕ) :
    x T ≤ κ ^ T * x 0 + c / (1 - κ) := by
  have h1κ : (0:ℝ) < 1 - κ := by linarith
  induction T with
  | zero =>
    have : (0:ℝ) ≤ c / (1 - κ) := by positivity
    simp only [pow_zero, one_mul]
    linarith
  | succ T ih =>
    have hfold : κ * (c / (1 - κ)) + c = c / (1 - κ) := by
      field_simp
      ring
    calc x (T + 1) ≤ κ * x T + c := h T
      _ ≤ κ * (κ ^ T * x 0 + c / (1 - κ)) + c := by
          nlinarith [mul_le_mul_of_nonneg_left ih hκ0]
      _ = κ ^ (T + 1) * x 0 + c / (1 - κ) := by
          rw [pow_succ]; linear_combination hfold

/-- **Claim 1 (smaller ball at equal speed), Eq. `eq:noise-ball`.**  From the
recursion `x_{t+1} ≤ (1 − ημ) xₜ + η² 𝒱` with `0 < ημ ≤ 1`,
`x_T ≤ (1 − ημ)^T x₀ + η𝒱/μ`. -/
theorem noise_ball (η μ V : ℝ) (hη : 0 < η) (hμ : 0 < μ) (hημ : η * μ ≤ 1) (hV : 0 ≤ V)
    (x : ℕ → ℝ) (h : ∀ t, x (t + 1) ≤ (1 - η * μ) * x t + η ^ 2 * V) (T : ℕ) :
    x T ≤ (1 - η * μ) ^ T * x 0 + η * V / μ := by
  have hb := ball_recursion (1 - η * μ) (η ^ 2 * V) (by linarith)
    (by nlinarith [mul_pos hη hμ]) (by positivity) x h T
  have hval : η ^ 2 * V / (1 - (1 - η * μ)) = η * V / μ := by
    rw [sub_sub_cancel]
    field_simp
  rwa [hval] at hb

/-- Radius-for-rate trade-off: the threshold ball radius at step `η/r` equals the
personalized ball radius at step `η`, when `𝒱_thr = r 𝒱_pers`. -/
theorem step_size_tradeoff (η μ Vthr Vpers r : ℝ) (hr : 0 < r)
    (hV : Vthr = r * Vpers) :
    (η / r) * Vthr / μ = η * Vpers / μ := by
  rw [hV]
  field_simp

/-- **Claim 2 (equal ball at slower speed).**  With step size `η/r`, where
`𝒱_thr = r 𝒱_pers` and `r ≥ 1`, the threshold recursion gives
`x_T ≤ (1 − ημ/r)^T x₀ + η𝒱_pers/μ`. -/
theorem noise_ball_slow (η μ Vthr Vpers r : ℝ) (hη : 0 < η) (hμ : 0 < μ)
    (hημ : η * μ ≤ 1) (hr : 1 ≤ r) (hVpers : 0 ≤ Vpers) (hV : Vthr = r * Vpers)
    (x : ℕ → ℝ) (h : ∀ t, x (t + 1) ≤ (1 - η / r * μ) * x t + (η / r) ^ 2 * Vthr)
    (T : ℕ) :
    x T ≤ (1 - η * μ / r) ^ T * x 0 + η * Vpers / μ := by
  have hr0 : 0 < r := by linarith
  have hstep : η / r * μ ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hr0]
    linarith
  have hb := noise_ball (η / r) μ Vthr (div_pos hη hr0) hμ hstep
    (by rw [hV]; positivity) x h T
  rwa [step_size_tradeoff η μ Vthr Vpers r hr0 hV, div_mul_eq_mul_div] at hb

/-! ## Lemma `lem:budget-scaling` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Lemma `lem:budget-scaling`** (personalized risk):
`𝓡_pers(c u; A, B) = 𝓡_pers(u; A, B/c²)`. -/
theorem budget_scaling_pers (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) {c : ℝ} (hc : 0 < c) :
    persRisk pub (fun i => c * u i) A B = persRisk pub u A (B / c ^ 2) := by
  simpa using persRisk_scale pub u A B hc one_pos

/-- **Lemma `lem:budget-scaling`** (threshold risk):
`𝓡_thr(c u; A, B) = 𝓡_thr(u; A, B/c²)`. -/
theorem budget_scaling_thr (pub : Finset ι) (u : ι → ℝ) (A B : ℝ) {c : ℝ} (hc : 0 < c) :
    thrRisk pub (fun i => c * u i) A B = thrRisk pub u A (B / c ^ 2) := by
  simpa using thrRisk_scale pub u A B hc one_pos

/-- **Prop. `prop:ball-comparison-detailed`, Claim 2.**  Under a composition schedule
the round-`t` budgets are `√αₜ · u`; the per-release ratio bounds hold at every round:
`𝓡_thr(√α u) ≤ min{(1 + log₂ n)², m²} 𝓡_pers(√α u)` (hence `≤ 4` for two levels). -/
theorem composition_ratio [Nonempty ι] (u : ι → ℝ) (hu : ∀ i, 0 < u i) {A B α : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hα : 0 < α) :
    thrRisk ∅ (fun i => Real.sqrt α * u i) A B
      ≤ min ((1 + Real.logb 2 (Fintype.card ι)) ^ 2) ((#(univ.image u) : ℝ) ^ 2)
        * persRisk ∅ (fun i => Real.sqrt α * u i) A B := by
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  rw [budget_scaling_thr _ _ _ _ hs, budget_scaling_pers _ _ _ _ hs]
  exact upper_bound u hu hA (by positivity)

/-- **Prop. `prop:ball-comparison-detailed`, Claim 2**, public data: with one finite
level and public records, `𝓡_thr(√α u) ≤ 2 𝓡_pers(√α u)` at every round. -/
theorem composition_ratio_public (pub : Finset ι) (u : ι → ℝ) (ε₁ : ℝ) {A B α : ℝ}
    (hε₁ : 0 < ε₁) (hA : 0 < A) (hB : 0 < B) (hα : 0 < α)
    (hpub : pub.Nonempty) (hpriv : pubᶜ.Nonempty) (hu : ∀ i ∉ pub, u i = ε₁) :
    thrRisk pub (fun i => Real.sqrt α * u i) A B
      ≤ 2 * persRisk pub (fun i => Real.sqrt α * u i) A B := by
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  rw [budget_scaling_thr _ _ _ _ hs, budget_scaling_pers _ _ _ _ hs]
  exact public_data_factor_two pub u ε₁ A _ hε₁ hA (by positivity) hpub hpriv hu

/-- **Remark `rem:fixed-total-budget`.**  Running the threshold method for `r T`
steps at step size `η/r` (so the noise constant becomes `r B`) can only improve
its guaranteed radius: `(1/r) 𝓡_thr(u; V, r B) ≤ 𝓡_thr(u; V, B)` for `r ≥ 1`. -/
theorem extra_iterations_le (pub : Finset ι) (u : ι → ℝ) {V B r : ℝ} (hV : 0 < V)
    (hB : 0 < B) (hr : 1 ≤ r) (hne : ∃ t, 0 < t ∧ 0 < nThr pub u t) :
    thrRisk pub u V (r * B) / r ≤ thrRisk pub u V B := by
  have hr0 : 0 < r := by linarith
  have hscale := thrRisk_scale pub u (V / r) B one_pos hr0
  simp only [one_mul, one_pow, div_one] at hscale
  have hVr : r * (V / r) = V := by field_simp
  rw [hVr] at hscale
  have hfun : (fun i => u i) = u := rfl
  rw [hfun] at hscale
  rw [hscale, mul_div_cancel_left₀ _ hr0.ne']
  apply le_thrRisk hne
  intro t ht hN
  refine (thrRisk_le (by positivity) hB.le ht hN).trans ?_
  unfold thrObj
  have hNpos : (0:ℝ) < nThr pub u t := Nat.cast_pos.mpr hN
  have : V / r / (nThr pub u t : ℝ) ≤ V / (nThr pub u t : ℝ) :=
    div_le_div_of_nonneg_right (div_le_self hV.le hr) hNpos.le
  linarith

/-! ## Prop. `prop:ball-comparison-detailed` -/

/-- **Claims 2–3.**  At a common step size, the squared radii `η𝒱/μ` are
proportional to the oracle MSEs, so their ratio is exactly `r_g`. -/
theorem ball_radius_ratio (η μ Vthr Vpers r : ℝ) (hη : 0 < η) (hμ : 0 < μ)
    (hVpers : 0 < Vpers) (hr : Vthr = r * Vpers) :
    (η * Vthr / μ) / (η * Vpers / μ) = r := by
  rw [hr]
  field_simp

end Limites
