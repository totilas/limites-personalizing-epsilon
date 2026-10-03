import Mathlib
import LimitesProofs.DPSGD

/-!
# Section `sec:convergence-balls`: convergence of personalized DP-SGD to noise balls

Stochastic (genuine-expectation) versions of the convergence results, for a real Hilbert space
`E`, a probability space `(Ω, P)` and sub-σ-algebras `ℱ t` (in the paper, `ℱ t = σ(θ_t)`).
An oracle run `θ_{t+1} = θ_t − η_t g̃_t` is bundled in `SGDRun`; its conditional unbiasedness and
conditional MSE are stated with Mathlib's conditional expectation `P[· | ℱ t]`.

* `coercivity`, `gradient_step_contraction` — Step 1 of the proof of Thm. `thm:ball-comparison`
  (Eq. `eq:coercivity` and the `(1 − ημ)`-contraction), via `strongConvex_smooth_cocoercive`
  (Nesterov / Baillon–Haddad co-coercivity), `strongConvex_first_order`, `descent_lemma`.
* `SGDRun.step_identity`, `smooth_recursion` — Step 2 of the proof of Thm. `thm:ball-comparison`
  (no cross term; `x_{t+1} ≤ (1 − ημ) x_t + η² 𝒱`).
* `noise_ball_expectation` — Thm. `thm:ball-comparison`, Claim 1 (Eq. `eq:noise-ball`).
* `noise_ball_limsup` — `limsup_T E‖θ_T − θ*‖² ≤ η𝒱/μ` (proof of Thm. `thm:ball-comparison`).
* `noise_ball_slow_expectation` — Thm. `thm:ball-comparison`, Claim 2.
* `ball_comparison` — Thm. `thm:ball-comparison` for the threshold/personalized pair.
* `varying_steps_bound`, `varying_steps_ratio` — Remark `rem:varying-step-sizes`.
* `quadratic_general` — Prop. `prop:quadratic-propagation`, Eq. `eq:quadratic-general`
  (via `quadratic_sq_dist`).
* `quadratic_unit_step_expectation` — Eq. `eq:quadratic-explicit-convergence`.
* `quadratic_ratio`, `quadratic_ratio_tendsto`, `quadratic_ratio_unit_step` — the excess-risk
  ratio `1 + (r_g − 1)/(1 + β_g) ≤ r_g`, its limit `r_g`, and its value `r_g` at `η = 1/μ`.
* `isotropic_limit_eq` — the isotropic limit `η²𝒱/(1 − a²) = η𝒱/(μ(2 − ημ))` (proof of
  Thm. `thm:ball-comparison`, Step 2).
* `quadratic_sq_dist_tendsto`, `isotropic_radius_ratio` — Prop. `prop:ball-comparison-detailed`,
  Claim 3.
* `nonsmooth_second_moment`, `nonsmooth_ratio`, `nonsmooth_guarantee_ratio` — Remark
  "Non-smooth strongly convex objectives" (the Shamir–Zhang bound itself is cited, not
  formalized).

Measurability/integrability side conditions left implicit in the paper (all in `SGDRun`):
`ℱ t` is a sub-σ-algebra, `θ_t` is `ℱ_t`-strongly measurable, and `‖g̃_t − ∇F(θ_t)‖²` is
integrable (without it the conditional MSE hypothesis would be vacuous). No filtration
(monotonicity of `ℱ`) is needed.
-/

open InnerProductSpace Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Limites.Convergence


/-! ## Convex-analysis toolkit -/

omit [CompleteSpace E] in
/-- Co-coercivity (Baillon–Haddad, multiplied form), abstractly: if `h` lies above its
linearizations `h x + ⟪H x, z − x⟫` and below `h x + ⟪H x, z − x⟫ + L'/2 ‖z − x‖²`
(`L' ≥ 0`), then `‖H x − H y‖² ≤ L' ⟪H x − H y, x − y⟫`. -/
theorem cocoercive_of_bounds (h : E → ℝ) (H : E → E) {L' : ℝ} (hL' : 0 ≤ L')
    (hlow : ∀ x z, h x + inner ℝ (H x) (z - x) ≤ h z)
    (hup : ∀ x z, h z ≤ h x + inner ℝ (H x) (z - x) + L' / 2 * ‖z - x‖ ^ 2) (x y : E) :
    ‖H x - H y‖ ^ 2 ≤ L' * inner ℝ (H x - H y) (x - y) := by
  have aux : ∀ x y : E, ∀ s : ℝ, s * ‖H y - H x‖ ^ 2 - L' / 2 * s ^ 2 * ‖H y - H x‖ ^ 2
      ≤ h y - h x - inner ℝ (H x) (y - x) := by
    intro x y s
    set d := H y - H x
    have h1 := hlow x (y - s • d)
    have h2 := hup y (y - s • d)
    have e1 : y - s • d - x = (y - x) - s • d := by abel
    have e2 : y - s • d - y = -(s • d) := by abel
    rw [e1, inner_sub_right, inner_smul_right] at h1
    rw [e2, inner_neg_right, inner_smul_right, norm_neg, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs] at h2
    have e3 : inner ℝ (H y) d - inner ℝ (H x) d = ‖d‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have e4 : s * inner ℝ (H y) d - s * inner ℝ (H x) d = s * ‖d‖ ^ 2 := by rw [← e3]; ring
    nlinarith
  have hsym : ‖H y - H x‖ = ‖H x - H y‖ := norm_sub_rev _ _
  have hB : inner ℝ (H x - H y) (x - y) = - inner ℝ (H x) (y - x) - inner ℝ (H y) (x - y) := by
    have : x - y = -(y - x) := by abel
    rw [inner_sub_left, this, inner_neg_right]
  rcases hL'.lt_or_eq with hpos | hzero
  · have a1 := aux x y (1 / L')
    have a2 := aux y x (1 / L')
    rw [hsym] at a1
    have key : (1 / L') * ‖H x - H y‖ ^ 2 ≤ inner ℝ (H x - H y) (x - y) := by
      have : 1 / L' * ‖H x - H y‖ ^ 2 - L' / 2 * (1 / L') ^ 2 * ‖H x - H y‖ ^ 2
          = (1 / L' * ‖H x - H y‖ ^ 2) / 2 := by field_simp; ring
      rw [hB]; nlinarith
    have := mul_le_mul_of_nonneg_left key hL'
    rwa [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] at this
  · subst hzero
    by_contra hcon
    push Not at hcon
    have hd : 0 < ‖H x - H y‖ ^ 2 := by nlinarith [inner ℝ (H x - H y) (x - y)]
    set B := inner ℝ (H x - H y) (x - y)
    have a1 := aux x y ((B + 1) / (2 * ‖H x - H y‖ ^ 2))
    have a2 := aux y x ((B + 1) / (2 * ‖H x - H y‖ ^ 2))
    rw [hsym] at a1
    have hn : ‖H x - H y‖ ^ 2 ≠ 0 := hd.ne'
    have : (B + 1) / (2 * ‖H x - H y‖ ^ 2) * ‖H x - H y‖ ^ 2 = (B + 1) / 2 := by
      rw [div_mul_eq_mul_div, mul_comm 2, ← div_div, mul_div_cancel_right₀ _ hn]
    simp only [zero_div, zero_mul, sub_zero] at a1 a2
    rw [this] at a1 a2
    linarith



/-- Derivative of `F` along the line `s ↦ x + s d`. -/
theorem hasDerivAt_line {F : E → ℝ} (hF : Differentiable ℝ F) (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • d)) (inner ℝ (gradient F (x + t • d)) d) t := by
  have hg : HasFDerivAt F (toDual ℝ E (gradient F (x + t • d))) (x + t • d) :=
    (hF _).hasGradientAt.hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have := hg.comp_hasDerivAt t hl
  rw [toDual_apply_apply] at this
  exact this

/-- First-order characterization of strong convexity:
`F z ≥ F x + ⟪∇F x, z − x⟫ + μ/2 ‖z − x‖²`. -/
theorem strongConvex_first_order {F : E → ℝ} {μ : ℝ} (hconv : StrongConvexOn univ μ F)
    (hF : Differentiable ℝ F) (x z : E) :
    F x + inner ℝ (gradient F x) (z - x) + μ / 2 * ‖z - x‖ ^ 2 ≤ F z := by
  set d := z - x
  have hD := hasDerivAt_line hF x d 0
  simp only [zero_smul, add_zero] at hD
  have hlim := (hasDerivAt_iff_tendsto_slope.mp hD).mono_left
    (nhdsWithin_mono _ (fun t (ht : 0 < t) => ne_of_gt ht))
  have hlim2 : Tendsto
      (fun t => slope (fun s : ℝ => F (x + s • d)) 0 t + (1 - t) * (μ / 2 * ‖d‖ ^ 2))
      (𝓝[>] 0) (𝓝 (inner ℝ (gradient F x) d + (1 - 0) * (μ / 2 * ‖d‖ ^ 2))) := by
    refine hlim.add (Tendsto.mul ?_ tendsto_const_nhds)
    exact ((continuous_const.sub continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ),
      slope (fun s : ℝ => F (x + s • d)) 0 t + (1 - t) * (μ / 2 * ‖d‖ ^ 2) ≤ F z - F x := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have key := hconv.2 (mem_univ x) (mem_univ z) (show 0 ≤ 1 - t by linarith) ht0.le
      (by ring)
    have hpt : (1 - t) • x + t • z = x + t • d := by
      simp only [d, smul_sub, sub_smul, one_smul]; abel
    rw [hpt, smul_eq_mul, smul_eq_mul, norm_sub_rev] at key
    simp only [slope_def_field, zero_smul, add_zero, sub_zero]
    rw [div_add' _ _ _ ht0.ne', div_le_iff₀ ht0]
    nlinarith
  have := le_of_tendsto hlim2 hev
  simp only [sub_zero, one_mul] at this
  linarith

/-- Descent lemma: an `L`-Lipschitz gradient gives
`F z ≤ F x + ⟪∇F x, z − x⟫ + L/2 ‖z − x‖²`. -/
theorem descent_lemma {F : E → ℝ} {L : ℝ} (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖) (x z : E) :
    F z ≤ F x + inner ℝ (gradient F x) (z - x) + L / 2 * ‖z - x‖ ^ 2 := by
  set d := z - x
  let ψ : ℝ → ℝ := fun t => t * inner ℝ (gradient F x) d + L / 2 * t ^ 2 * ‖d‖ ^ 2
    - F (x + t • d)
  have hψ : ∀ t, HasDerivAt ψ (inner ℝ (gradient F x) d + L * t * ‖d‖ ^ 2
      - inner ℝ (gradient F (x + t • d)) d) t := by
    intro t
    have h1 := ((hasDerivAt_id t).mul_const (inner ℝ (gradient F x) d))
    have h2 := (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
    have h3 := hasDerivAt_line hF x d t
    refine ((h1.add h2).sub h3).congr_deriv ?_
    simp only [id, one_mul, Nat.cast_ofNat, mul_one]
    ring
  have hmono : MonotoneOn ψ (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t _ => (hψ t).continuousAt.continuousWithinAt)
      (fun t _ => (hψ t).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have hb : inner ℝ (gradient F (x + t • d) - gradient F x) d ≤ L * t * ‖d‖ ^ 2 := by
      calc _ ≤ ‖gradient F (x + t • d) - gradient F x‖ * ‖d‖ := real_inner_le_norm _ _
        _ ≤ (L * ‖x + t • d - x‖) * ‖d‖ := by gcongr; exact hsmooth _ _
        _ = L * t * ‖d‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]; ring
    rw [inner_sub_left] at hb
    linarith
  have := hmono (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [ψ, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_smul, add_zero, one_mul, one_pow, mul_one, one_smul, d] at this
  rw [add_sub_cancel] at this
  linarith

/-- The gradient vanishes at a (global) minimizer. -/
theorem gradient_eq_zero_of_min {F : E → ℝ} (hF : Differentiable ℝ F) {θstar : E}
    (hmin : ∀ θ, F θstar ≤ F θ) : gradient F θstar = 0 := by
  have h := IsLocalMin.hasFDerivAt_eq_zero (Filter.Eventually.of_forall hmin)
    (hF θstar).hasGradientAt.hasFDerivAt
  have h2 : fderiv ℝ F θstar = 0 := by simpa using h
  simp [gradient, h2]


/-! ## Step 1 of the proof of Thm. `thm:ball-comparison` -/

section Deterministic

variable {F : E → ℝ} {μ L : ℝ}

/-- Nesterov's inequality for `μ`-strongly convex, `L`-smooth functions:
`‖∇F x − ∇F y‖² + μL‖x − y‖² ≤ (μ + L)⟪∇F x − ∇F y, x − y⟫`. -/
theorem strongConvex_smooth_cocoercive (hμL : μ ≤ L) (hconv : StrongConvexOn univ μ F)
    (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖gradient F x - gradient F y‖ ^ 2 + μ * L * ‖x - y‖ ^ 2
      ≤ (μ + L) * inner ℝ (gradient F x - gradient F y) (x - y) := by
  set h : E → ℝ := fun z => F z - μ / 2 * ‖z‖ ^ 2
  set H : E → E := fun z => gradient F z - μ • z
  have hsq : ∀ x z : E, ‖z‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (z - x) + ‖z - x‖ ^ 2 := by
    intro x z
    rw [← norm_add_sq_real, add_sub_cancel]
  have hHi : ∀ x z : E, inner ℝ (H x) (z - x)
      = inner ℝ (gradient F x) (z - x) - μ * inner ℝ x (z - x) := by
    intro x z
    simp only [H, inner_sub_left, real_inner_smul_left]
  have hlow : ∀ x z, h x + inner ℝ (H x) (z - x) ≤ h z := by
    intro x z
    have h1 := strongConvex_first_order hconv hF x z
    simp only [h, hHi]
    rw [hsq x z]
    linarith
  have hup : ∀ x z, h z ≤ h x + inner ℝ (H x) (z - x) + (L - μ) / 2 * ‖z - x‖ ^ 2 := by
    intro x z
    have h1 := descent_lemma hF hsmooth x z
    simp only [h, hHi]
    rw [hsq x z]
    linarith
  have key := cocoercive_of_bounds h H (sub_nonneg.mpr hμL) hlow hup x y
  have hdiff : H x - H y = (gradient F x - gradient F y) - μ • (x - y) := by
    simp only [H, smul_sub]; abel
  rw [hdiff] at key
  set u := gradient F x - gradient F y
  set d := x - y
  simp only [norm_sub_sq_real, inner_sub_left, inner_smul_left, inner_smul_right, norm_smul,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial] at key
  nlinarith

/-- **Step 1 of the proof of Thm. `thm:ball-comparison`, Eq. `eq:coercivity`.**  For `F`
`μ`-strongly convex (`StrongConvexOn univ μ F`) and `L`-smooth (differentiable with
`L`-Lipschitz gradient), `0 < μ ≤ L`, and `θ*` a minimizer of `F`:
`⟪∇F θ, θ − θ*⟫ ≥ μL/(μ+L) ‖θ − θ*‖² + 1/(μ+L) ‖∇F θ‖²`. -/
theorem coercivity (hμ : 0 < μ) (hμL : μ ≤ L) (hconv : StrongConvexOn univ μ F)
    (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    {θstar : E} (hmin : ∀ θ, F θstar ≤ F θ) (θ : E) :
    μ * L / (μ + L) * ‖θ - θstar‖ ^ 2 + 1 / (μ + L) * ‖gradient F θ‖ ^ 2
      ≤ inner ℝ (gradient F θ) (θ - θstar) := by
  have h0 := gradient_eq_zero_of_min hF hmin
  have key := strongConvex_smooth_cocoercive hμL hconv hF hsmooth θ θstar
  rw [h0, sub_zero] at key
  have hs : 0 < μ + L := by linarith
  have e : μ * L / (μ + L) * ‖θ - θstar‖ ^ 2 + 1 / (μ + L) * ‖gradient F θ‖ ^ 2
      = (μ * L * ‖θ - θstar‖ ^ 2 + ‖gradient F θ‖ ^ 2) / (μ + L) := by
    field_simp
  rw [e, div_le_iff₀ hs]
  linarith

/-- **Step 1 of the proof of Thm. `thm:ball-comparison` (contraction).**  For
`0 < η ≤ 2/(μ+L)`, the deterministic gradient step satisfies
`‖θ − η∇F θ − θ*‖² ≤ (1 − ημ)‖θ − θ*‖²`. -/
theorem gradient_step_contraction (hμ : 0 < μ) (hμL : μ ≤ L)
    (hconv : StrongConvexOn univ μ F) (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    {θstar : E} (hmin : ∀ θ, F θstar ≤ F θ) {η : ℝ} (hη : 0 < η) (hηL : η ≤ 2 / (μ + L))
    (θ : E) :
    ‖θ - η • gradient F θ - θstar‖ ^ 2 ≤ (1 - η * μ) * ‖θ - θstar‖ ^ 2 := by
  have hc := coercivity hμ hμL hconv hF hsmooth hmin θ
  have hs : 0 < μ + L := by linarith
  have hrw : θ - η • gradient F θ - θstar = (θ - θstar) - η • gradient F θ := by abel
  rw [hrw, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_comm]
  set c := ‖θ - θstar‖ ^ 2
  set a := ‖gradient F θ‖ ^ 2
  set b := inner ℝ (gradient F θ) (θ - θstar)
  have hη' : η * (μ + L) ≤ 2 := by rwa [le_div_iff₀ hs] at hηL
  have ha : 0 ≤ a := by positivity
  have hcn : 0 ≤ c := by positivity
  -- multiply the coercivity inequality by `η (μ + L)`
  have hc' : η * μ * L * c + η * a ≤ η * (μ + L) * b := by
    have := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ η * (μ + L))
    have e : η * (μ + L) * (μ * L / (μ + L) * c + 1 / (μ + L) * a)
        = η * μ * L * c + η * a := by field_simp
    linarith
  -- `η (μ + L) b ≥ …` and `η ≤ 2/(μ+L)` give the contraction
  have h1 : η ^ 2 * a ≤ 2 * η * a / (μ + L) := by
    rw [le_div_iff₀ hs]; nlinarith [mul_nonneg hη.le ha]
  have h2 : 2 * η * b ≥ (2 * η * μ * L * c + 2 * η * a) / (μ + L) := by
    rw [ge_iff_le, div_le_iff₀ hs]; nlinarith
  have h3 : η * μ * c ≤ 2 * η * μ * L * c / (μ + L) := by
    rw [le_div_iff₀ hs]; nlinarith [mul_nonneg (mul_nonneg hη.le hμ.le) hcn]
  have h4 : (2 * η * μ * L * c + 2 * η * a) / (μ + L)
      = 2 * η * μ * L * c / (μ + L) + 2 * η * a / (μ + L) := add_div _ _ _
  nlinarith

/-- An `L`-Lipschitz gradient is continuous. -/
theorem continuous_gradient_of_smooth
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖) :
    Continuous (gradient F) :=
  (LipschitzWith.of_dist_le' (K := L) fun x y => by
    simpa [dist_eq_norm] using hsmooth x y).continuous

end Deterministic

/-! ## Oracle-driven SGD with conditional expectations -/

section Stochastic

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- No cross term: if `X` is `𝒢`-measurable and `E[ξ | 𝒢] = 0`, then
`E‖X − η ξ‖² = E‖X‖² + η² E‖ξ‖²`. -/
theorem integral_norm_sub_smul_sq {G : MeasurableSpace Ω} (hG : G ≤ m0) {X ξ : Ω → E}
    (hX : StronglyMeasurable[G] X) (hXint : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (hξm : AEStronglyMeasurable[m0] ξ P) (hξint : Integrable (fun ω => ‖ξ ω‖ ^ 2) P)
    (hξ0 : P[ξ | G] =ᵐ[P] 0) (η : ℝ) :
    ∫ ω, ‖X ω - η • ξ ω‖ ^ 2 ∂P = ∫ ω, ‖X ω‖ ^ 2 ∂P + η ^ 2 * ∫ ω, ‖ξ ω‖ ^ 2 ∂P := by
  have hXm : AEStronglyMeasurable[m0] X P := (hX.mono hG).aestronglyMeasurable
  have hξ1 : Integrable ξ P :=
    ((memLp_two_iff_integrable_sq_norm hξm).2 hξint).integrable one_le_two
  have hinner : Integrable (fun ω => inner ℝ (X ω) (ξ ω)) P := by
    refine Integrable.mono' ((hXint.add hξint).div_const 2)
      (AEStronglyMeasurable.inner (𝕜 := ℝ) hXm hξm) ?_
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    calc |inner ℝ (X ω) (ξ ω)| ≤ ‖X ω‖ * ‖ξ ω‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖X ω‖ ^ 2 + ‖ξ ω‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖X ω‖ - ‖ξ ω‖)]
  have hzero : ∫ ω, inner ℝ (X ω) (ξ ω) ∂P = 0 := by
    have e : (fun ω => innerSL ℝ (X ω) (ξ ω)) = fun ω => inner ℝ (X ω) (ξ ω) := by
      funext ω; rfl
    have hpull := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) (μ := P) hX
      (by rw [e]; exact hinner) hξ1
    rw [e] at hpull
    rw [← integral_condExp hG]
    have : P[fun ω => inner ℝ (X ω) (ξ ω) | G] =ᵐ[P] 0 := by
      filter_upwards [hpull, hξ0] with ω h1 h2
      rw [h1, innerSL_apply_apply (𝕜 := ℝ), h2, Pi.zero_apply, inner_zero_right, Pi.zero_apply]
    rw [integral_congr_ae this]
    simp
  have hexp : (fun ω => ‖X ω - η • ξ ω‖ ^ 2) = fun ω =>
      (‖X ω‖ ^ 2 - (2 * η) * inner ℝ (X ω) (ξ ω)) + η ^ 2 * ‖ξ ω‖ ^ 2 := by
    funext ω
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [hexp, integral_add (f := fun ω => ‖X ω‖ ^ 2 - (2 * η) * inner ℝ (X ω) (ξ ω))
    (g := fun ω => η ^ 2 * ‖ξ ω‖ ^ 2) (hXint.sub (hinner.const_mul _)) (hξint.const_mul _),
    integral_sub (f := fun ω => ‖X ω‖ ^ 2) (g := fun ω => (2 * η) * inner ℝ (X ω) (ξ ω))
    hXint (hinner.const_mul _), integral_const_mul, integral_const_mul, hzero]
  ring

/-- The expectation of a function is at most `V` when its conditional expectation is. -/
theorem integral_le_of_condExp_le {G : MeasurableSpace Ω} (hG : G ≤ m0) {f : Ω → ℝ}
    {V : ℝ} (hf : P[f | G] ≤ᵐ[P] fun _ => V) :
    ∫ ω, f ω ∂P ≤ V := by
  rw [← integral_condExp hG]
  calc ∫ ω, (P[f | G]) ω ∂P ≤ ∫ _, V ∂P := integral_mono_ae integrable_condExp
        (integrable_const V) hf
    _ = V := by simp

/-- The expectation of a function equals `V` when its conditional expectation does. -/
theorem integral_eq_of_condExp_eq {G : MeasurableSpace Ω} (hG : G ≤ m0) {f : Ω → ℝ}
    {V : ℝ} (hf : P[f | G] =ᵐ[P] fun _ => V) :
    ∫ ω, f ω ∂P = V := by
  rw [← integral_condExp hG, integral_congr_ae hf]
  simp

/-- An SGD run `θ_{t+1} = θ_t − η_t g̃_t` driven by a conditionally unbiased oracle for the
vector field `G` (in the applications, `G = ∇F`).

* `ℱ t` is the σ-algebra conditioned on at step `t` (in the paper, `σ(θ_t)`); no monotonicity
  (filtration property) is needed;
* `θ₀` is the deterministic initialization;
* `unbiased`: `E[g̃_t | ℱ_t] = G(θ_t)` a.s.;
* `mse_int`: the oracle error `‖g̃_t − G(θ_t)‖²` is integrable (standard side condition: it
  makes the conditional MSE hypothesis meaningful, the paper's MSE being finite). -/
structure SGDRun (P : Measure Ω) (ℱ : ℕ → MeasurableSpace Ω) (G : E → E) (η : ℕ → ℝ)
    (θ₀ : E) (θ g : ℕ → Ω → E) : Prop where
  le : ∀ t, ℱ t ≤ m0
  init : ∀ ω, θ 0 ω = θ₀
  step : ∀ t ω, θ (t + 1) ω = θ t ω - η t • g t ω
  meas : ∀ t, StronglyMeasurable[ℱ t] (θ t)
  unbiased : ∀ t, P[g t | ℱ t] =ᵐ[P] fun ω => G (θ t ω)
  mse_int : ∀ t, Integrable (fun ω => ‖g t ω - G (θ t ω)‖ ^ 2) P

namespace SGDRun

variable {ℱ : ℕ → MeasurableSpace Ω} {G : E → E} {η : ℕ → ℝ} {θ₀ : E} {θ g : ℕ → Ω → E}

omit [CompleteSpace E] in
/-- `E‖θ_0 − θ*‖² = R₀²` for the deterministic initialization. -/
theorem integral_init (run : SGDRun P ℱ G η θ₀ θ g) (θstar : E) :
    ∫ ω, ‖θ 0 ω - θstar‖ ^ 2 ∂P = ‖θ₀ - θstar‖ ^ 2 := by
  simp [run.init]

omit [CompleteSpace E] in
theorem integrable_init (run : SGDRun P ℱ G η θ₀ θ g) (θstar : E) :
    Integrable (fun ω => ‖θ 0 ω - θstar‖ ^ 2) P := by
  simp [run.init]

/-- **Step 2 of the proof of Thm. `thm:ball-comparison`** (no cross term): with
`X_t = θ_t − η_t G(θ_t) − θ*`,
`E‖θ_{t+1} − θ*‖² = E‖X_t‖² + η_t² E‖g̃_t − G(θ_t)‖²`. -/
theorem step_identity (run : SGDRun P ℱ G η θ₀ θ g) (hGc : Continuous G) (θstar : E)
    (t : ℕ) (hη : η t ≠ 0)
    (he : Integrable (fun ω => ‖θ t ω - θstar‖ ^ 2) P)
    (hX : Integrable (fun ω => ‖θ t ω - η t • G (θ t ω) - θstar‖ ^ 2) P) :
    Integrable (fun ω => ‖θ (t + 1) ω - θstar‖ ^ 2) P ∧
    ∫ ω, ‖θ (t + 1) ω - θstar‖ ^ 2 ∂P = ∫ ω, ‖θ t ω - η t • G (θ t ω) - θstar‖ ^ 2 ∂P
      + η t ^ 2 * ∫ ω, ‖g t ω - G (θ t ω)‖ ^ 2 ∂P := by
  have hle := run.le t
  have hθsm := run.meas t
  have hGsm : StronglyMeasurable[ℱ t] fun ω => G (θ t ω) := hGc.comp_stronglyMeasurable hθsm
  have hXsm : StronglyMeasurable[ℱ t] fun ω => θ t ω - η t • G (θ t ω) - θstar :=
    (hθsm.sub (hGsm.const_smul (η t))).sub stronglyMeasurable_const
  have hθm : AEStronglyMeasurable (θ t) P := (hθsm.mono hle).aestronglyMeasurable
  have hθm' : AEStronglyMeasurable (θ (t + 1)) P :=
    ((run.meas (t + 1)).mono (run.le (t + 1))).aestronglyMeasurable
  have hg_eq : g t = fun ω => (η t)⁻¹ • (θ t ω - θ (t + 1) ω) := by
    funext ω
    rw [run.step, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hη, one_smul]
  have hgm : AEStronglyMeasurable (g t) P := by
    rw [hg_eq]; exact (hθm.sub hθm').const_smul _
  have hGm : AEStronglyMeasurable (fun ω => G (θ t ω)) P := (hGsm.mono hle).aestronglyMeasurable
  have hξm : AEStronglyMeasurable (fun ω => g t ω - G (θ t ω)) P := hgm.sub hGm
  have hXm : AEStronglyMeasurable (fun ω => θ t ω - η t • G (θ t ω) - θstar) P :=
    (hXsm.mono hle).aestronglyMeasurable
  have memE : MemLp (fun ω => θ t ω - θstar) 2 P :=
    (memLp_two_iff_integrable_sq_norm (hθm.sub aestronglyMeasurable_const)).2 he
  have memX : MemLp (fun ω => θ t ω - η t • G (θ t ω) - θstar) 2 P :=
    (memLp_two_iff_integrable_sq_norm hXm).2 hX
  have memξ : MemLp (fun ω => g t ω - G (θ t ω)) 2 P :=
    (memLp_two_iff_integrable_sq_norm hξm).2 (run.mse_int t)
  have hGint : Integrable (fun ω => G (θ t ω)) P := by
    have h := ((memE.sub memX).const_smul (η t)⁻¹).integrable one_le_two
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.smul_apply, Pi.sub_apply]
    rw [sub_sub_sub_cancel_right, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hη, one_smul]
  have hξint1 : Integrable (fun ω => g t ω - G (θ t ω)) P := memξ.integrable one_le_two
  have hgint : Integrable (g t) P := by
    refine (hξint1.add hGint).congr (Eventually.of_forall fun ω => ?_)
    simp
  have hξ0 : P[fun ω => g t ω - G (θ t ω) | ℱ t] =ᵐ[P] 0 := by
    have hsub := condExp_sub (m := ℱ t) hgint hGint
    have hG' : P[fun ω => G (θ t ω) | ℱ t] = fun ω => G (θ t ω) :=
      condExp_of_stronglyMeasurable hle hGsm hGint
    filter_upwards [hsub, run.unbiased t] with ω h1 h2
    have h1' : (P[fun ω => g t ω - G (θ t ω) | ℱ t]) ω
        = (P[g t | ℱ t]) ω - (P[fun ω => G (θ t ω) | ℱ t]) ω := h1
    rw [h1', h2, hG', sub_self, Pi.zero_apply]
  have hpt : (fun ω => ‖θ (t + 1) ω - θstar‖ ^ 2)
      = fun ω => ‖(θ t ω - η t • G (θ t ω) - θstar) - η t • (g t ω - G (θ t ω))‖ ^ 2 := by
    funext ω
    rw [run.step, smul_sub]
    congr 2
    abel
  refine ⟨?_, ?_⟩
  · rw [hpt]
    exact (memLp_two_iff_integrable_sq_norm (hXm.sub (hξm.const_smul _))).1
      (memX.sub (memξ.const_smul _))
  · rw [hpt]
    exact integral_norm_sub_smul_sq hle hXsm hX hξm (run.mse_int t) hξ0 (η t)

end SGDRun

/-! ## Thm. `thm:ball-comparison` and Remark `rem:varying-step-sizes` -/

variable {F : E → ℝ} {μ L : ℝ} {θstar θ₀ : E} {ℱ : ℕ → MeasurableSpace Ω}
  {θ g : ℕ → Ω → E}

/-- **Steps 1–2 of the proof of Thm. `thm:ball-comparison`** (for an arbitrary deterministic
step-size schedule, as in Remark `rem:varying-step-sizes`): every `‖θ_t − θ*‖²` is
integrable and `E‖θ_{t+1} − θ*‖² ≤ (1 − μη_t) E‖θ_t − θ*‖² + η_t² 𝒱`. -/
theorem smooth_recursion (hμ : 0 < μ) (hμL : μ ≤ L) (hconv : StrongConvexOn univ μ F)
    (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ θ, F θstar ≤ F θ) {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hηL : ∀ t, η t ≤ 2 / (μ + L)) {V : ℝ}
    (run : SGDRun P ℱ (gradient F) η θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient F (θ t ω)‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => V)
    (t : ℕ) :
    Integrable (fun ω => ‖θ t ω - θstar‖ ^ 2) P ∧
    ∫ ω, ‖θ (t + 1) ω - θstar‖ ^ 2 ∂P
      ≤ (1 - η t * μ) * ∫ ω, ‖θ t ω - θstar‖ ^ 2 ∂P + η t ^ 2 * V := by
  have hGc := continuous_gradient_of_smooth hsmooth
  have hXint : ∀ s, Integrable (fun ω => ‖θ s ω - θstar‖ ^ 2) P →
      Integrable (fun ω => ‖θ s ω - η s • gradient F (θ s ω) - θstar‖ ^ 2) P := by
    intro s hs
    refine (hs.const_mul (1 - η s * μ)).mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact ((((run.meas s).sub ((hGc.comp_stronglyMeasurable (run.meas s)).const_smul
        (η s))).sub stronglyMeasurable_const).mono (run.le s)).aestronglyMeasurable.norm.pow 2
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact gradient_step_contraction hμ hμL hconv hF hsmooth hmin (hη s) (hηL s) _
  have hint : ∀ s, Integrable (fun ω => ‖θ s ω - θstar‖ ^ 2) P := by
    intro s
    induction s with
    | zero => exact run.integrable_init θstar
    | succ s ih => exact (run.step_identity hGc θstar s (hη s).ne' ih (hXint s ih)).1
  refine ⟨hint t, ?_⟩
  rw [(run.step_identity hGc θstar t (hη t).ne' (hint t) (hXint t (hint t))).2]
  have h1 : ∫ ω, ‖θ t ω - η t • gradient F (θ t ω) - θstar‖ ^ 2 ∂P
      ≤ (1 - η t * μ) * ∫ ω, ‖θ t ω - θstar‖ ^ 2 ∂P := by
    rw [← integral_const_mul]
    exact integral_mono (hXint t (hint t)) ((hint t).const_mul _) fun ω =>
      gradient_step_contraction hμ hμL hconv hF hsmooth hmin (hη t) (hηL t) _
  have h2 := integral_le_of_condExp_le (run.le t) (hV t)
  nlinarith [sq_nonneg (η t)]

omit [CompleteSpace E] in
/-- The MSE bound `𝒱` is necessarily nonnegative. -/
theorem SGDRun.mse_bound_nonneg {G : E → E} {η : ℕ → ℝ} (run : SGDRun P ℱ G η θ₀ θ g) {V : ℝ}
    (hV : ∀ t, P[fun ω => ‖g t ω - G (θ t ω)‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => V) : 0 ≤ V :=
  (integral_nonneg fun _ => by positivity).trans (integral_le_of_condExp_le (run.le 0) (hV 0))

theorem step_le_inv_mu (hμ : 0 < μ) (hμL : μ ≤ L) {η : ℝ} (hη : 0 < η)
    (hηL : η ≤ 2 / (μ + L)) : η * μ ≤ 1 := by
  have hs : 0 < μ + L := by linarith
  rw [le_div_iff₀ hs] at hηL
  nlinarith

/-- **Thm. `thm:ball-comparison`, Claim 1 (smaller ball at equal speed), Eq. `eq:noise-ball`**,
for a generic oracle.  `F` is `μ`-strongly convex and `L`-smooth with minimizer `θ*`
(`0 < μ ≤ L`), `θ_{t+1} = θ_t − η g̃_t` with `0 < η ≤ 2/(μ+L)`, `θ_0 = θ₀` deterministic,
`E[g̃_t | ℱ_t] = ∇F(θ_t)` and `E[‖g̃_t − ∇F(θ_t)‖² | ℱ_t] ≤ 𝒱` a.s.  Then for every `T`,
`E‖θ_T − θ*‖² ≤ (1 − ημ)^T R₀² + η𝒱/μ`, `R₀ = ‖θ₀ − θ*‖`.  Apply it with
`𝒱 = 𝒱_thr` and `𝒱 = 𝒱_pers` for the two mechanisms (see `ball_comparison`).
Side conditions (bundled in `SGDRun`): `θ_t` is `ℱ_t`-strongly measurable, `ℱ_t` is a
sub-σ-algebra, and `‖g̃_t − ∇F(θ_t)‖²` is integrable. -/
theorem noise_ball_expectation (hμ : 0 < μ) (hμL : μ ≤ L) (hconv : StrongConvexOn univ μ F)
    (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ θ, F θstar ≤ F θ) {η : ℝ} (hη : 0 < η) (hηL : η ≤ 2 / (μ + L)) {V : ℝ}
    (run : SGDRun P ℱ (gradient F) (fun _ => η) θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient F (θ t ω)‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => V)
    (T : ℕ) :
    ∫ ω, ‖θ T ω - θstar‖ ^ 2 ∂P ≤ (1 - η * μ) ^ T * ‖θ₀ - θstar‖ ^ 2 + η * V / μ := by
  have h := Limites.noise_ball η μ V hη hμ (step_le_inv_mu hμ hμL hη hηL)
    (run.mse_bound_nonneg hV) (fun t => ∫ ω, ‖θ t ω - θstar‖ ^ 2 ∂P)
    (fun t => (smooth_recursion hμ hμL hconv hF hsmooth hmin (fun _ => hη) (fun _ => hηL)
      run hV t).2) T
  rwa [run.integral_init] at h

/-- **Proof of Thm. `thm:ball-comparison`, Step 2:**
`limsup_{T→∞} E‖θ_T − θ*‖² ≤ η𝒱/μ`. -/
theorem noise_ball_limsup (hμ : 0 < μ) (hμL : μ ≤ L) (hconv : StrongConvexOn univ μ F)
    (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ θ, F θstar ≤ F θ) {η : ℝ} (hη : 0 < η) (hηL : η ≤ 2 / (μ + L)) {V : ℝ}
    (run : SGDRun P ℱ (gradient F) (fun _ => η) θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient F (θ t ω)‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => V) :
    limsup (fun T => ∫ ω, ‖θ T ω - θstar‖ ^ 2 ∂P) atTop ≤ η * V / μ := by
  have h1 := step_le_inv_mu hμ hμL hη hηL
  have hb : Tendsto (fun T : ℕ => (1 - η * μ) ^ T * ‖θ₀ - θstar‖ ^ 2 + η * V / μ) atTop
      (𝓝 (η * V / μ)) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - η * μ)
      (by nlinarith [mul_pos hη hμ] : 1 - η * μ < 1)).mul_const (‖θ₀ - θstar‖ ^ 2)).add_const
      (η * V / μ)
    simpa using this
  calc limsup (fun T => ∫ ω, ‖θ T ω - θstar‖ ^ 2 ∂P) atTop
      ≤ limsup (fun T : ℕ => (1 - η * μ) ^ T * ‖θ₀ - θstar‖ ^ 2 + η * V / μ) atTop :=
        limsup_le_limsup (Eventually.of_forall fun T =>
          noise_ball_expectation hμ hμL hconv hF hsmooth hmin hη hηL run hV T)
          (isCoboundedUnder_le_of_le atTop fun T => integral_nonneg fun _ => by positivity)
          hb.isBoundedUnder_le
    _ = η * V / μ := hb.limsup_eq

/-- **Thm. `thm:ball-comparison`, Claim 2 (equal ball at slower speed).**  If
`𝒱_thr = r 𝒱_pers` with `r ≥ 1` (i.e. `r = r_g`), the threshold run with step size `η/r`
satisfies `E‖θ_T − θ*‖² ≤ (1 − ημ/r)^T R₀² + η𝒱_pers/μ`. -/
theorem noise_ball_slow_expectation (hμ : 0 < μ) (hμL : μ ≤ L)
    (hconv : StrongConvexOn univ μ F) (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ θ, F θstar ≤ F θ) {η r Vthr Vpers : ℝ} (hη : 0 < η) (hηL : η ≤ 2 / (μ + L))
    (hr : 1 ≤ r) (hVr : Vthr = r * Vpers)
    (run : SGDRun P ℱ (gradient F) (fun _ => η / r) θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient F (θ t ω)‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => Vthr)
    (T : ℕ) :
    ∫ ω, ‖θ T ω - θstar‖ ^ 2 ∂P
      ≤ (1 - η * μ / r) ^ T * ‖θ₀ - θstar‖ ^ 2 + η * Vpers / μ := by
  have hr0 : 0 < r := by linarith
  have hηr : 0 < η / r := div_pos hη hr0
  have hηrL : η / r ≤ 2 / (μ + L) := (div_le_self hη.le hr).trans hηL
  have hVthr := run.mse_bound_nonneg hV
  have hVpers : 0 ≤ Vpers := by
    rw [hVr] at hVthr
    exact nonneg_of_mul_nonneg_right (by linarith) hr0
  have h := Limites.noise_ball_slow η μ Vthr Vpers r hη hμ (step_le_inv_mu hμ hμL hη hηL) hr
    hVpers hVr (fun t => ∫ ω, ‖θ t ω - θstar‖ ^ 2 ∂P)
    (fun t => (smooth_recursion hμ hμL hconv hF hsmooth hmin (fun _ => hηr) (fun _ => hηrL)
      run hV t).2) T
  rwa [run.integral_init] at h

/-- **Thm. `thm:ball-comparison`** (both claims, two mechanisms).  Threshold run `θ` with
oracle MSE `≤ 𝒱_thr`, personalized run `θ'` with oracle MSE `≤ 𝒱_pers`, same step `η` and
initialization `θ₀`; and the threshold run `θ''` at step `η/r` when `𝒱_thr = r 𝒱_pers`,
`r ≥ 1`. -/
theorem ball_comparison (hμ : 0 < μ) (hμL : μ ≤ L) (hconv : StrongConvexOn univ μ F)
    (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ θ, F θstar ≤ F θ) {η r Vthr Vpers : ℝ} (hη : 0 < η) (hηL : η ≤ 2 / (μ + L))
    {ℱ' ℱ'' : ℕ → MeasurableSpace Ω} {θ' g' θ'' g'' : ℕ → Ω → E}
    (run_thr : SGDRun P ℱ (gradient F) (fun _ => η) θ₀ θ g)
    (hV_thr : ∀ t, P[fun ω => ‖g t ω - gradient F (θ t ω)‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => Vthr)
    (run_pers : SGDRun P ℱ' (gradient F) (fun _ => η) θ₀ θ' g')
    (hV_pers : ∀ t, P[fun ω => ‖g' t ω - gradient F (θ' t ω)‖ ^ 2 | ℱ' t] ≤ᵐ[P]
      fun _ => Vpers)
    (hr : 1 ≤ r) (hVr : Vthr = r * Vpers)
    (run_slow : SGDRun P ℱ'' (gradient F) (fun _ => η / r) θ₀ θ'' g'')
    (hV_slow : ∀ t, P[fun ω => ‖g'' t ω - gradient F (θ'' t ω)‖ ^ 2 | ℱ'' t] ≤ᵐ[P]
      fun _ => Vthr) (T : ℕ) :
    (∫ ω, ‖θ T ω - θstar‖ ^ 2 ∂P ≤ (1 - η * μ) ^ T * ‖θ₀ - θstar‖ ^ 2 + η * Vthr / μ ∧
      ∫ ω, ‖θ' T ω - θstar‖ ^ 2 ∂P ≤ (1 - η * μ) ^ T * ‖θ₀ - θstar‖ ^ 2 + η * Vpers / μ) ∧
    ∫ ω, ‖θ'' T ω - θstar‖ ^ 2 ∂P
      ≤ (1 - η * μ / r) ^ T * ‖θ₀ - θstar‖ ^ 2 + η * Vpers / μ :=
  ⟨⟨noise_ball_expectation hμ hμL hconv hF hsmooth hmin hη hηL run_thr hV_thr T,
    noise_ball_expectation hμ hμL hconv hF hsmooth hmin hη hηL run_pers hV_pers T⟩,
    noise_ball_slow_expectation hμ hμL hconv hF hsmooth hmin hη hηL hr hVr run_slow hV_slow T⟩

/-! ### Remark `rem:varying-step-sizes` -/

/-- The error guarantee of Remark `rem:varying-step-sizes`:
`R₀² ∏_{t<T} (1 − μη_t) + 𝒱 ∑_{t<T} η_t² ∏_{s=t+1}^{T−1} (1 − μη_s)`. -/
noncomputable def varyingBound (μ R₀ V : ℝ) (η : ℕ → ℝ) (T : ℕ) : ℝ :=
  R₀ ^ 2 * ∏ t ∈ Finset.range T, (1 - μ * η t)
    + V * ∑ t ∈ Finset.range T, η t ^ 2 * ∏ s ∈ Finset.Ico (t + 1) T, (1 - μ * η s)

theorem varyingBound_succ (μ R₀ V : ℝ) (η : ℕ → ℝ) (T : ℕ) :
    varyingBound μ R₀ V η (T + 1)
      = (1 - μ * η T) * varyingBound μ R₀ V η T + η T ^ 2 * V := by
  unfold varyingBound
  rw [Finset.prod_range_succ, Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty]
  have hs : ∑ t ∈ Finset.range T, η t ^ 2 * ∏ s ∈ Finset.Ico (t + 1) (T + 1), (1 - μ * η s)
      = (∑ t ∈ Finset.range T, η t ^ 2 * ∏ s ∈ Finset.Ico (t + 1) T, (1 - μ * η s))
        * (1 - μ * η T) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_Ico_succ_top (by simp at ht; omega)]
    ring
  rw [hs]
  ring

/-- Iterating `x_{t+1} ≤ (1 − μη_t) x_t + η_t² 𝒱` (with `1 − μη_t ≥ 0`) from `x₀ = R₀²`. -/
theorem varying_recursion (μ R₀ V : ℝ) (η : ℕ → ℝ) (hk : ∀ t, 0 ≤ 1 - μ * η t) (x : ℕ → ℝ)
    (h0 : x 0 = R₀ ^ 2) (h : ∀ t, x (t + 1) ≤ (1 - μ * η t) * x t + η t ^ 2 * V) (T : ℕ) :
    x T ≤ varyingBound μ R₀ V η T := by
  induction T with
  | zero => simp [varyingBound, h0]
  | succ T ih =>
    rw [varyingBound_succ]
    nlinarith [h T, mul_le_mul_of_nonneg_left ih (hk T)]

/-- **Remark `rem:varying-step-sizes`** (bound).  With a deterministic schedule
`0 < η_t ≤ 2/(μ+L)` and the assumptions of Thm. `thm:ball-comparison`,
`E‖θ_T − θ*‖² ≤ R₀² ∏_{t<T}(1 − μη_t) + 𝒱 ∑_{t<T} η_t² ∏_{s=t+1}^{T−1}(1 − μη_s)`. -/
theorem varying_steps_bound (hμ : 0 < μ) (hμL : μ ≤ L) (hconv : StrongConvexOn univ μ F)
    (hF : Differentiable ℝ F)
    (hsmooth : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ θ, F θstar ≤ F θ) {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hηL : ∀ t, η t ≤ 2 / (μ + L)) {V : ℝ}
    (run : SGDRun P ℱ (gradient F) η θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient F (θ t ω)‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => V)
    (T : ℕ) :
    ∫ ω, ‖θ T ω - θstar‖ ^ 2 ∂P ≤ varyingBound μ ‖θ₀ - θstar‖ V η T := by
  refine varying_recursion μ _ V η (fun t => ?_) (fun t => ∫ ω, ‖θ t ω - θstar‖ ^ 2 ∂P)
    (run.integral_init θstar) (fun t => ?_) T
  · have := step_le_inv_mu hμ hμL (hη t) (hηL t); linarith
  · rw [mul_comm μ]
    exact (smooth_recursion hμ hμL hconv hF hsmooth hmin hη hηL run hV t).2

/-- **Remark `rem:varying-step-sizes`** (comparison).  For the same schedule
`0 < η_t ≤ 2/(μ+L)` and the same initialization, the ratio of the threshold and personalized
error guarantees is at most `r_g = 𝒱_thr/𝒱_pers` for every `T ≥ 1`.  (`𝒱_pers ≤ 𝒱_thr`, i.e.
`r_g ≥ 1`, is the standing comparison of the two oracles, as in Lemma `lem:bias`.) -/
theorem varying_steps_ratio (hμ : 0 < μ) (hμL : μ ≤ L) {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hηL : ∀ t, η t ≤ 2 / (μ + L)) (R₀ : ℝ) {Vthr Vpers : ℝ} (hVp : 0 < Vpers)
    (hle : Vpers ≤ Vthr) (T : ℕ) (hT : 1 ≤ T) :
    varyingBound μ R₀ Vthr η T / varyingBound μ R₀ Vpers η T ≤ Vthr / Vpers := by
  have hk : ∀ t, 0 ≤ 1 - μ * η t := fun t => by
    have := step_le_inv_mu hμ hμL (hη t) (hηL t); linarith
  set c := ∑ t ∈ Finset.range T, η t ^ 2 * ∏ s ∈ Finset.Ico (t + 1) T, (1 - μ * η s)
  have hc : 0 < c := by
    obtain ⟨T', rfl⟩ := Nat.exists_eq_add_of_le' hT
    simp only [c]
    rw [Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, mul_one]
    have : 0 ≤ ∑ t ∈ Finset.range T', η t ^ 2 * ∏ s ∈ Finset.Ico (t + 1) (T' + 1),
        (1 - μ * η s) :=
      Finset.sum_nonneg fun t _ => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun s _ => hk s)
    have := pow_pos (hη T') 2
    linarith
  have hb0 : 0 ≤ R₀ ^ 2 * ∏ t ∈ Finset.range T, (1 - μ * η t) :=
    mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun s _ => hk s)
  have := Limites.bias_attenuation_le _ c Vthr Vpers hb0 hc hVp hle
  unfold varyingBound
  rwa [mul_comm Vthr, mul_comm Vpers]

/-! ## Prop. `prop:quadratic-propagation` (isotropic quadratic) -/

/-- The isotropic quadratic `F(θ) = (μ/2)‖θ − θ*‖²`. -/
noncomputable def quadF (μ : ℝ) (θstar : E) : E → ℝ := fun θ => μ / 2 * ‖θ - θstar‖ ^ 2

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem quadF_self (μ : ℝ) (θstar : E) : quadF μ θstar θstar = 0 := by simp [quadF]

theorem gradient_quadF (μ : ℝ) (θstar θ : E) : gradient (quadF μ θstar) θ = μ • (θ - θstar) := by
  have h := (((hasFDerivAt_id θ).sub_const θstar).norm_sq).const_mul (μ / 2)
  have hg : HasGradientAt (quadF μ θstar) (μ • (θ - θstar)) θ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have e : toDual ℝ E (μ • (θ - θstar))
        = (μ / 2) • (2 • (innerSL ℝ (θ - θstar)).comp (ContinuousLinearMap.id ℝ E)) := by
      ext v
      simp
      ring
    rw [e]
    exact h
  exact hg.gradient

variable {η V : ℝ}

/-- Exact second moment on the isotropic quadratic (proof of Prop.
`prop:quadratic-propagation`): with `a = 1 − ημ`,
`E‖θ_T − θ*‖² = a^{2T} R₀² + η²𝒱 (1 − a^{2T})/(1 − a²)`, when the conditional MSE is
exactly `𝒱`. -/
theorem quadratic_sq_dist (hμ : 0 < μ) (hη : 0 < η) (hη2 : η < 2 / μ)
    (run : SGDRun P ℱ (gradient (quadF μ θstar)) (fun _ => η) θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient (quadF μ θstar) (θ t ω)‖ ^ 2 | ℱ t] =ᵐ[P]
      fun _ => V) (T : ℕ) :
    ∫ ω, ‖θ T ω - θstar‖ ^ 2 ∂P = (1 - η * μ) ^ (2 * T) * ‖θ₀ - θstar‖ ^ 2
      + η ^ 2 * V * (1 - (1 - η * μ) ^ (2 * T)) / (1 - (1 - η * μ) ^ 2) := by
  have hGc : Continuous (gradient (quadF μ θstar)) := by
    have : gradient (quadF μ θstar) = fun θ => μ • (θ - θstar) := funext (gradient_quadF μ θstar)
    rw [this]; fun_prop
  have hXeq : ∀ x : E, ‖x - η • gradient (quadF μ θstar) x - θstar‖ ^ 2
      = (1 - η * μ) ^ 2 * ‖x - θstar‖ ^ 2 := by
    intro x
    rw [gradient_quadF, show x - η • (μ • (x - θstar)) - θstar = (1 - η * μ) • (x - θstar) by
      rw [smul_smul, sub_smul, one_smul]; abel, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hXint : ∀ s, Integrable (fun ω => ‖θ s ω - θstar‖ ^ 2) P →
      Integrable (fun ω => ‖θ s ω - η • gradient (quadF μ θstar) (θ s ω) - θstar‖ ^ 2) P := by
    intro s hs
    simp_rw [hXeq]
    exact hs.const_mul _
  have hint : ∀ s, Integrable (fun ω => ‖θ s ω - θstar‖ ^ 2) P := by
    intro s
    induction s with
    | zero => exact run.integrable_init θstar
    | succ s ih => exact (run.step_identity hGc θstar s hη.ne' ih (hXint s ih)).1
  have hrec : ∀ t, ∫ ω, ‖θ (t + 1) ω - θstar‖ ^ 2 ∂P
      = (1 - η * μ) ^ 2 * ∫ ω, ‖θ t ω - θstar‖ ^ 2 ∂P + η ^ 2 * V := by
    intro t
    rw [(run.step_identity hGc θstar t hη.ne' (hint t) (hXint t (hint t))).2,
      integral_eq_of_condExp_eq (run.le t) (hV t)]
    simp_rw [hXeq]
    rw [integral_const_mul]
  have hημ : η * μ < 2 := by rwa [lt_div_iff₀ hμ] at hη2
  have hημ0 : 0 < η * μ := mul_pos hη hμ
  have ha : (1 - η * μ) ^ 2 ≠ 1 := by
    intro h
    have : (1 - η * μ) ^ 2 < 1 := by nlinarith
    linarith
  have := Limites.quadratic_recursion ((1 - η * μ) ^ 2) (η ^ 2 * V) ha
    (fun t => ∫ ω, ‖θ t ω - θstar‖ ^ 2 ∂P) hrec T
  rw [this, run.integral_init, ← pow_mul]

/-- **Prop. `prop:quadratic-propagation`, Eq. `eq:quadratic-general`.**  For
`F(θ) = (μ/2)‖θ − θ*‖²`, `0 < η < 2/μ`, a conditionally unbiased oracle with conditional MSE
exactly `𝒱`, and `a = 1 − ημ`:
`E[F(θ_T) − F(θ*)] = (μ/2) a^{2T} R₀² + (μη²/2) (1 − a^{2T})/(1 − a²) 𝒱`.
(Side conditions bundled in `SGDRun`, as in `noise_ball_expectation`.) -/
theorem quadratic_general (hμ : 0 < μ) (hη : 0 < η) (hη2 : η < 2 / μ)
    (run : SGDRun P ℱ (gradient (quadF μ θstar)) (fun _ => η) θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient (quadF μ θstar) (θ t ω)‖ ^ 2 | ℱ t] =ᵐ[P]
      fun _ => V) (T : ℕ) :
    ∫ ω, (quadF μ θstar (θ T ω) - quadF μ θstar θstar) ∂P
      = μ / 2 * (1 - η * μ) ^ (2 * T) * ‖θ₀ - θstar‖ ^ 2
        + μ * η ^ 2 / 2 * ((1 - (1 - η * μ) ^ (2 * T)) / (1 - (1 - η * μ) ^ 2)) * V := by
  simp only [quadF_self, sub_zero]
  simp only [quadF]
  rw [integral_const_mul, quadratic_sq_dist hμ hη hη2 run hV T]
  ring

/-- **Prop. `prop:quadratic-propagation`, Eq. `eq:quadratic-explicit-convergence`.**  At step
size `η = 1/μ`, `E[F(θ_T) − F(θ*)] = 𝒱/(2μ)` for every `T ≥ 1`. -/
theorem quadratic_unit_step_expectation (hμ : 0 < μ)
    (run : SGDRun P ℱ (gradient (quadF μ θstar)) (fun _ => 1 / μ) θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient (quadF μ θstar) (θ t ω)‖ ^ 2 | ℱ t] =ᵐ[P]
      fun _ => V) (T : ℕ) (hT : 1 ≤ T) :
    ∫ ω, (quadF μ θstar (θ T ω) - quadF μ θstar θstar) ∂P = V / (2 * μ) := by
  have h1 : (0 : ℝ) < 1 / μ := by positivity
  have h2 : 1 / μ < 2 / μ := by gcongr; norm_num
  rw [quadratic_general hμ h1 h2 run hV T, one_div_mul_cancel hμ.ne', sub_self,
    zero_pow (by omega), zero_pow two_ne_zero]
  field_simp
  ring

/-- **Prop. `prop:quadratic-propagation`, consequence (via Lemma `lem:bias`).**  For two runs
on the isotropic quadratic with the same `η ∈ (0, 2/μ)` and `θ₀` and conditional MSEs exactly
`𝒱_thr`, `𝒱_pers > 0`, the excess-risk ratio at every `T ≥ 1` equals
`1 + (r_g − 1)/(1 + β_g)`, `β_g = a^{2T} R₀² (1 − a²)/(η² (1 − a^{2T}) 𝒱_pers)`, and is at most
`r_g` when `𝒱_pers ≤ 𝒱_thr` (the standing assumption `r_g ≥ 1` of Lemma `lem:bias`). -/
theorem quadratic_ratio (hμ : 0 < μ) (hη : 0 < η) (hη2 : η < 2 / μ)
    {ℱ' : ℕ → MeasurableSpace Ω} {θ' g' : ℕ → Ω → E} {Vthr Vpers : ℝ}
    (run_thr : SGDRun P ℱ (gradient (quadF μ θstar)) (fun _ => η) θ₀ θ g)
    (hV_thr : ∀ t, P[fun ω => ‖g t ω - gradient (quadF μ θstar) (θ t ω)‖ ^ 2 | ℱ t] =ᵐ[P]
      fun _ => Vthr)
    (run_pers : SGDRun P ℱ' (gradient (quadF μ θstar)) (fun _ => η) θ₀ θ' g')
    (hV_pers : ∀ t, P[fun ω => ‖g' t ω - gradient (quadF μ θstar) (θ' t ω)‖ ^ 2 | ℱ' t] =ᵐ[P]
      fun _ => Vpers)
    (hVp : 0 < Vpers) (T : ℕ) (hT : 1 ≤ T) :
    (∫ ω, (quadF μ θstar (θ T ω) - quadF μ θstar θstar) ∂P)
        / (∫ ω, (quadF μ θstar (θ' T ω) - quadF μ θstar θstar) ∂P)
      = 1 + (Vthr / Vpers - 1) / (1 + (1 - η * μ) ^ (2 * T) * ‖θ₀ - θstar‖ ^ 2
          * (1 - (1 - η * μ) ^ 2) / (η ^ 2 * (1 - (1 - η * μ) ^ (2 * T)) * Vpers)) ∧
    (Vpers ≤ Vthr →
      (∫ ω, (quadF μ θstar (θ T ω) - quadF μ θstar θstar) ∂P)
        / (∫ ω, (quadF μ θstar (θ' T ω) - quadF μ θstar θstar) ∂P) ≤ Vthr / Vpers) := by
  rw [quadratic_general hμ hη hη2 run_thr hV_thr T, quadratic_general hμ hη hη2 run_pers hV_pers T]
  have hημ : η * μ < 2 := by rwa [lt_div_iff₀ hμ] at hη2
  have hημ0 : 0 < η * μ := mul_pos hη hμ
  have ha2 : (1 - η * μ) ^ 2 < 1 := by nlinarith
  have h1a : 0 < 1 - (1 - η * μ) ^ 2 := by linarith
  have haT : (1 - η * μ) ^ (2 * T) < 1 := by
    rw [pow_mul]; exact pow_lt_one₀ (sq_nonneg _) ha2 (by omega)
  have h1aT : 0 < 1 - (1 - η * μ) ^ (2 * T) := by linarith
  have hb0 : 0 ≤ μ / 2 * (1 - η * μ) ^ (2 * T) * ‖θ₀ - θstar‖ ^ 2 := by
    have : 0 ≤ (1 - η * μ) ^ (2 * T) := by rw [pow_mul]; positivity
    positivity
  have hc : 0 < μ * η ^ 2 / 2 * ((1 - (1 - η * μ) ^ (2 * T)) / (1 - (1 - η * μ) ^ 2)) := by
    positivity
  refine ⟨?_, fun hle => Limites.bias_attenuation_le _ _ _ _ hb0 hc hVp hle⟩
  rw [Limites.bias_attenuation_eq _ _ _ _ hb0 hc hVp]
  congr 3
  field_simp

/-- **Prop. `prop:quadratic-propagation`, consequence:** the excess-risk ratio tends to
`r_g = 𝒱_thr/𝒱_pers` as `T → ∞`. -/
theorem quadratic_ratio_tendsto (hμ : 0 < μ) (hη : 0 < η) (hη2 : η < 2 / μ)
    {ℱ' : ℕ → MeasurableSpace Ω} {θ' g' : ℕ → Ω → E} {Vthr Vpers : ℝ}
    (run_thr : SGDRun P ℱ (gradient (quadF μ θstar)) (fun _ => η) θ₀ θ g)
    (hV_thr : ∀ t, P[fun ω => ‖g t ω - gradient (quadF μ θstar) (θ t ω)‖ ^ 2 | ℱ t] =ᵐ[P]
      fun _ => Vthr)
    (run_pers : SGDRun P ℱ' (gradient (quadF μ θstar)) (fun _ => η) θ₀ θ' g')
    (hV_pers : ∀ t, P[fun ω => ‖g' t ω - gradient (quadF μ θstar) (θ' t ω)‖ ^ 2 | ℱ' t] =ᵐ[P]
      fun _ => Vpers)
    (hVp : 0 < Vpers) :
    Tendsto (fun T => (∫ ω, (quadF μ θstar (θ T ω) - quadF μ θstar θstar) ∂P)
        / (∫ ω, (quadF μ θstar (θ' T ω) - quadF μ θstar θstar) ∂P)) atTop
      (𝓝 (Vthr / Vpers)) := by
  have hημ : η * μ < 2 := by rwa [lt_div_iff₀ hμ] at hη2
  have hημ0 : 0 < η * μ := mul_pos hη hμ
  have ha2 : (1 - η * μ) ^ 2 < 1 := by nlinarith
  have h1a : 0 < 1 - (1 - η * μ) ^ 2 := by linarith
  have hq : Tendsto (fun T : ℕ => (1 - η * μ) ^ (2 * T)) atTop (𝓝 0) := by
    simp_rw [pow_mul]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) ha2
  have hN : ∀ V : ℝ, Tendsto (fun T : ℕ => μ / 2 * (1 - η * μ) ^ (2 * T) * ‖θ₀ - θstar‖ ^ 2
      + μ * η ^ 2 / 2 * ((1 - (1 - η * μ) ^ (2 * T)) / (1 - (1 - η * μ) ^ 2)) * V) atTop
      (𝓝 (μ / 2 * 0 * ‖θ₀ - θstar‖ ^ 2
        + μ * η ^ 2 / 2 * ((1 - 0) / (1 - (1 - η * μ) ^ 2)) * V)) := fun V =>
    ((hq.const_mul (μ / 2)).mul_const _).add
      ((((tendsto_const_nhds.sub hq).div_const _).const_mul _).mul_const V)
  have hc : 0 < μ * η ^ 2 / 2 * ((1 - 0) / (1 - (1 - η * μ) ^ 2)) := by positivity
  have hlim := (hN Vthr).div (hN Vpers) (by
    simp only [mul_zero, zero_mul, zero_add]; positivity)
  have hval : (μ / 2 * 0 * ‖θ₀ - θstar‖ ^ 2
        + μ * η ^ 2 / 2 * ((1 - 0) / (1 - (1 - η * μ) ^ 2)) * Vthr)
      / (μ / 2 * 0 * ‖θ₀ - θstar‖ ^ 2
        + μ * η ^ 2 / 2 * ((1 - 0) / (1 - (1 - η * μ) ^ 2)) * Vpers) = Vthr / Vpers := by
    simp only [mul_zero, zero_mul, zero_add]
    exact mul_div_mul_left _ _ hc.ne'
  rw [hval] at hlim
  refine hlim.congr fun T => ?_
  rw [Pi.div_apply, quadratic_general hμ hη hη2 run_thr hV_thr T,
    quadratic_general hμ hη hη2 run_pers hV_pers T]

/-- **Prop. `prop:quadratic-propagation`, final claim:** at `η = 1/μ` the excess-risk ratio
equals `r_g = 𝒱_thr/𝒱_pers` exactly, for every `T ≥ 1`. -/
theorem quadratic_ratio_unit_step (hμ : 0 < μ)
    {ℱ' : ℕ → MeasurableSpace Ω} {θ' g' : ℕ → Ω → E} {Vthr Vpers : ℝ}
    (run_thr : SGDRun P ℱ (gradient (quadF μ θstar)) (fun _ => 1 / μ) θ₀ θ g)
    (hV_thr : ∀ t, P[fun ω => ‖g t ω - gradient (quadF μ θstar) (θ t ω)‖ ^ 2 | ℱ t] =ᵐ[P]
      fun _ => Vthr)
    (run_pers : SGDRun P ℱ' (gradient (quadF μ θstar)) (fun _ => 1 / μ) θ₀ θ' g')
    (hV_pers : ∀ t, P[fun ω => ‖g' t ω - gradient (quadF μ θstar) (θ' t ω)‖ ^ 2 | ℱ' t] =ᵐ[P]
      fun _ => Vpers) (T : ℕ) (hT : 1 ≤ T) :
    (∫ ω, (quadF μ θstar (θ T ω) - quadF μ θstar θstar) ∂P)
        / (∫ ω, (quadF μ θstar (θ' T ω) - quadF μ θstar θstar) ∂P) = Vthr / Vpers := by
  rw [quadratic_unit_step_expectation hμ run_thr hV_thr T hT,
    quadratic_unit_step_expectation hμ run_pers hV_pers T hT]
  exact div_div_div_cancel_right₀ (by positivity) _ _

/-! ## Prop. `prop:ball-comparison-detailed`, Claim 3 -/

/-- **Proof of Thm. `thm:ball-comparison`, Step 2 (isotropic quadratic limit):**
`η²𝒱/(1 − a²) = η𝒱/(μ(2 − ημ))` with `a = 1 − ημ`. -/
theorem isotropic_limit_eq (hμ : 0 < μ) (hη : 0 < η) (hη2 : η < 2 / μ) (V : ℝ) :
    η ^ 2 * V / (1 - (1 - η * μ) ^ 2) = η * V / (μ * (2 - η * μ)) := by
  have hημ : η * μ < 2 := by rwa [lt_div_iff₀ hμ] at hη2
  have h2 : 2 - η * μ ≠ 0 := by linarith
  have h3 : 1 - (1 - η * μ) ^ 2 = η * μ * (2 - η * μ) := by ring
  rw [h3]
  field_simp

/-- **Prop. `prop:ball-comparison-detailed`, Claim 3 (limit).**  On the isotropic quadratic,
with `0 < η < 2/μ` and conditional MSE exactly `𝒱`,
`E‖θ_T − θ*‖² → η𝒱/(μ(2 − ημ))` as `T → ∞`. -/
theorem quadratic_sq_dist_tendsto (hμ : 0 < μ) (hη : 0 < η) (hη2 : η < 2 / μ)
    (run : SGDRun P ℱ (gradient (quadF μ θstar)) (fun _ => η) θ₀ θ g)
    (hV : ∀ t, P[fun ω => ‖g t ω - gradient (quadF μ θstar) (θ t ω)‖ ^ 2 | ℱ t] =ᵐ[P]
      fun _ => V) :
    Tendsto (fun T => ∫ ω, ‖θ T ω - θstar‖ ^ 2 ∂P) atTop
      (𝓝 (η * V / (μ * (2 - η * μ)))) := by
  have hημ : η * μ < 2 := by rwa [lt_div_iff₀ hμ] at hη2
  have hημ0 : 0 < η * μ := mul_pos hη hμ
  have ha2 : (1 - η * μ) ^ 2 < 1 := by nlinarith
  have hq : Tendsto (fun T : ℕ => (1 - η * μ) ^ (2 * T)) atTop (𝓝 0) := by
    simp_rw [pow_mul]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) ha2
  have hc1 : Tendsto (fun _ : ℕ => η ^ 2 * V) atTop (𝓝 (η ^ 2 * V)) := tendsto_const_nhds
  have hc2 : Tendsto (fun T : ℕ => 1 - (1 - η * μ) ^ (2 * T)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hq
  have hlim := (hq.mul_const (‖θ₀ - θstar‖ ^ 2)).add
    ((hc1.mul hc2).div_const (1 - (1 - η * μ) ^ 2))
  simp only [zero_mul, zero_add, sub_zero, mul_one] at hlim
  rw [isotropic_limit_eq hμ hη hη2 V] at hlim
  exact hlim.congr fun T => (quadratic_sq_dist hμ hη hη2 run hV T).symm

/-- **Prop. `prop:ball-comparison-detailed`, Claim 3 (ratio).**  The asymptotic squared radii
`η𝒱/(μ(2 − ημ))` of the two mechanisms are in the exact ratio `𝒱_thr/𝒱_pers = r_g`. -/
theorem isotropic_radius_ratio (hμ : 0 < μ) (hη : 0 < η) (hη2 : η < 2 / μ) (Vthr Vpers : ℝ) :
    (η * Vthr / (μ * (2 - η * μ))) / (η * Vpers / (μ * (2 - η * μ))) = Vthr / Vpers := by
  have hημ : η * μ < 2 := by rwa [lt_div_iff₀ hμ] at hη2
  have h2 : μ * (2 - η * μ) ≠ 0 := mul_ne_zero hμ.ne' (by linarith)
  rw [div_div_div_cancel_right₀ h2]
  exact mul_div_mul_left _ _ hη.ne'

/-! ## Remark: non-smooth strongly convex objectives -/

/-- **Remark (non-smooth strongly convex objectives), second-moment bound.**  If `g` is
`𝒢`-measurable with `‖g‖ ≤ C` (in the remark, a subgradient `g_t ∈ ∂F(θ_t)`, `𝒢 = σ(θ_t)`)
and the oracle output `g̃` satisfies `E[g̃ | 𝒢] = g` and `E[‖g̃ − g‖² | 𝒢] ≤ 𝒱`, then
`E‖g̃‖² = E‖g‖² + E‖g̃ − g‖² ≤ C² + 𝒱`.  Side conditions: `g̃` is a.e. strongly measurable
and `‖g̃ − g‖²` is integrable.  The last-iterate bound of Shamir–Zhang that the remark then
invokes is cited, not formalized. -/
theorem nonsmooth_second_moment {G : MeasurableSpace Ω} (hG : G ≤ m0) {gs gt : Ω → E}
    {C : ℝ} (hgs : StronglyMeasurable[G] gs) (hC : ∀ ω, ‖gs ω‖ ≤ C)
    (hgtm : AEStronglyMeasurable[m0] gt P) (hunb : P[gt | G] =ᵐ[P] gs)
    (hint : Integrable (fun ω => ‖gt ω - gs ω‖ ^ 2) P)
    (hV : P[fun ω => ‖gt ω - gs ω‖ ^ 2 | G] ≤ᵐ[P] fun _ => V) :
    ∫ ω, ‖gt ω‖ ^ 2 ∂P = ∫ ω, ‖gs ω‖ ^ 2 ∂P + ∫ ω, ‖gt ω - gs ω‖ ^ 2 ∂P ∧
    ∫ ω, ‖gt ω‖ ^ 2 ∂P ≤ C ^ 2 + V := by
  have hgsm : AEStronglyMeasurable[m0] gs P := (hgs.mono hG).aestronglyMeasurable
  have hgsint : Integrable gs P := Integrable.of_bound hgsm C (Eventually.of_forall hC)
  have hsq : ∀ ω, ‖gs ω‖ ^ 2 ≤ C ^ 2 := fun ω => pow_le_pow_left₀ (norm_nonneg _) (hC ω) 2
  have hgs2 : Integrable (fun ω => ‖gs ω‖ ^ 2) P :=
    Integrable.of_bound (hgsm.norm.pow 2) (C ^ 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hsq ω)
  have hξm : AEStronglyMeasurable[m0] (fun ω => gt ω - gs ω) P := hgtm.sub hgsm
  have hξint1 : Integrable (fun ω => gt ω - gs ω) P :=
    ((memLp_two_iff_integrable_sq_norm hξm).2 hint).integrable one_le_two
  have hgtint : Integrable gt P := (hξint1.add hgsint).congr (Eventually.of_forall fun ω => by simp)
  have hξ0 : P[fun ω => gt ω - gs ω | G] =ᵐ[P] 0 := by
    have hsub := condExp_sub (m := G) hgtint hgsint
    have hG' : P[gs | G] = gs := condExp_of_stronglyMeasurable hG hgs hgsint
    filter_upwards [hsub, hunb] with ω h1 h2
    have h1' : (P[fun ω => gt ω - gs ω | G]) ω = (P[gt | G]) ω - (P[gs | G]) ω := h1
    rw [h1', h2, hG', sub_self, Pi.zero_apply]
  have hid := integral_norm_sub_smul_sq hG hgs hgs2 hξm hint hξ0 (-1)
  have hfun : (fun ω => ‖gs ω - (-1 : ℝ) • (gt ω - gs ω)‖ ^ 2) = fun ω => ‖gt ω‖ ^ 2 := by
    funext ω; congr 2; simp
  rw [hfun] at hid
  refine ⟨by rw [hid]; ring, ?_⟩
  rw [hid]
  have h1 : ∫ ω, ‖gs ω‖ ^ 2 ∂P ≤ C ^ 2 := by
    calc ∫ ω, ‖gs ω‖ ^ 2 ∂P ≤ ∫ _, C ^ 2 ∂P := integral_mono hgs2 (integrable_const _) hsq
      _ = C ^ 2 := by simp
  have h2 := integral_le_of_condExp_le hG hV
  nlinarith

/-- **Remark (non-smooth strongly convex objectives), ratio.**  The guarantees
`17(C² + 𝒱)(1 + log T)/(μT)` of the two mechanisms are in the ratio
`(C² + 𝒱_thr)/(C² + 𝒱_pers) = 1 + (r_g − 1)/(1 + β) ≤ r_g`, `β = C²/𝒱_pers`. -/
theorem nonsmooth_ratio (C : ℝ) {Vthr Vpers : ℝ} (hVp : 0 < Vpers) (hle : Vpers ≤ Vthr) :
    (C ^ 2 + Vthr) / (C ^ 2 + Vpers) = 1 + (Vthr / Vpers - 1) / (1 + C ^ 2 / Vpers) ∧
    (C ^ 2 + Vthr) / (C ^ 2 + Vpers) ≤ Vthr / Vpers := by
  have h1 := Limites.bias_attenuation_eq (C ^ 2) 1 Vthr Vpers (sq_nonneg C) one_pos hVp
  have h2 := Limites.bias_attenuation_le (C ^ 2) 1 Vthr Vpers (sq_nonneg C) one_pos hVp hle
  simp only [one_mul] at h1 h2
  exact ⟨h1, h2⟩

/-- The non-smooth guarantees themselves: their ratio is the ratio above. -/
theorem nonsmooth_guarantee_ratio (C μ : ℝ) (T : ℕ) (hμ : 0 < μ) (hT : 1 < T)
    {Vthr Vpers : ℝ} (hVp : 0 < Vpers) :
    (17 * (C ^ 2 + Vthr) * (1 + Real.log T) / (μ * T))
      / (17 * (C ^ 2 + Vpers) * (1 + Real.log T) / (μ * T))
      = (C ^ 2 + Vthr) / (C ^ 2 + Vpers) := by
  have hT' : (1 : ℝ) < T := by exact_mod_cast hT
  have hlog : 0 < 1 + Real.log T := by have := Real.log_pos hT'; linarith
  have hd : 0 < C ^ 2 + Vpers := by positivity
  field_simp

end Stochastic

end Limites.Convergence
