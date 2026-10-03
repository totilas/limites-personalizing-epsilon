import Mathlib

/-!
# The Laplace distribution `Lap(b)`

Mathlib has no Laplace distribution; we define `Lap(b)`, for a scale `b > 0`, as the
measure on `ℝ` with density `x ↦ e^{-|x|/b} / (2b)` w.r.t. Lebesgue measure.

* `laplace b` — the measure `Lap(b)`.
* `isProbabilityMeasure_laplace` — it is a probability measure.
* `integral_id_laplace`, `integral_sq_laplace`, `variance_id_laplace` — mean `0`,
  second moment and variance `2b²`; `integrable_id_laplace`, `integrable_sq_laplace`,
  `memLp_two_laplace` give the integrability facts.
* `laplace_Iic_neg` — `Lap(b)((-∞, -w]) = e^{-w/b}/2` for `w ≥ 0`.
* `laplace_map_const_add` — the law of `c + Z`, `Z ~ Lap(b)`, has density
  `y ↦ e^{-|y-c|/b}/(2b)`.
* `laplace_map_const_add_le` — the density-ratio bound behind the Laplace mechanism:
  `Pr(c + Z ∈ S) ≤ e^{|c - c'|/b} Pr(c' + Z ∈ S)`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Limites

/-- The density `e^{-|x|/b} / (2b)` of `Lap(b)`. -/
noncomputable def laplacePDFReal (b x : ℝ) : ℝ := Real.exp (-|x| / b) / (2 * b)

/-- The density of `Lap(b)` as an extended nonnegative real. -/
noncomputable def laplacePDF (b x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (laplacePDFReal b x)

/-- The Laplace distribution `Lap(b)` (meaningful for `b > 0`). -/
noncomputable def laplace (b : ℝ) : Measure ℝ := volume.withDensity (laplacePDF b)

variable {b : ℝ}

lemma laplacePDFReal_nonneg (hb : 0 < b) (x : ℝ) : 0 ≤ laplacePDFReal b x := by
  unfold laplacePDFReal; positivity

lemma measurable_laplacePDFReal (b : ℝ) : Measurable (laplacePDFReal b) := by
  unfold laplacePDFReal; fun_prop

lemma measurable_laplacePDF (b : ℝ) : Measurable (laplacePDF b) :=
  (measurable_laplacePDFReal b).ennreal_ofReal

/-- An even function is integrable on `ℝ` as soon as it is integrable on `(0, ∞)`. -/
lemma integrable_comp_abs_of_integrableOn {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) :
    Integrable (fun x => g |x|) := by
  have hIoi : IntegrableOn (fun x => g |x|) (Ioi 0) :=
    hg.congr_fun (fun x hx => by rw [abs_of_pos (mem_Ioi.mp hx)]) measurableSet_Ioi
  have hIic : IntegrableOn (fun x => g |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

lemma integrableOn_exp_neg_div (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Real.exp (-t / b)) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 (b := 1 / b) (by positivity)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  congr 1; ring

lemma integrableOn_sq_mul_exp_neg_div (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-t / b)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (b := 1 / b)
    (by norm_num) one_pos (by positivity)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  simp only [Real.rpow_one, Real.rpow_two]
  congr 2; ring

lemma integral_exp_neg_div (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t / b) = b := by
  have := integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1 / b) one_pos (by positivity)
  have e : ∀ t : ℝ, t ^ ((1 : ℝ) - 1) * Real.exp (-(1 / b * t)) = Real.exp (-t / b) := by
    intro t; rw [sub_self, Real.rpow_zero, one_mul]; congr 1; ring
  simp only [e] at this
  rw [this]; simp [Real.Gamma_one]

lemma integral_sq_mul_exp_neg_div (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-t / b) = 2 * b ^ 3 := by
  have := integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1 / b) (by norm_num) (by positivity)
  have hG : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  have e : ∀ t : ℝ, t ^ ((3 : ℝ) - 1) * Real.exp (-(1 / b * t)) = t ^ 2 * Real.exp (-t / b) := by
    intro t
    rw [show (3 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]; congr 2; ring
  simp only [e] at this
  rw [this, hG, one_div_one_div, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  ring

lemma integrable_laplacePDFReal (hb : 0 < b) : Integrable (laplacePDFReal b) :=
  integrable_comp_abs_of_integrableOn (g := fun t => Real.exp (-t / b) / (2 * b))
    ((integrableOn_exp_neg_div hb).div_const _)

lemma integral_laplacePDFReal (hb : 0 < b) : ∫ x, laplacePDFReal b x = 1 := by
  change ∫ x, (fun t => Real.exp (-t / b) / (2 * b)) |x| = 1
  rw [integral_comp_abs (f := fun t => Real.exp (-t / b) / (2 * b)), integral_div,
    integral_exp_neg_div hb]
  field_simp

/-- `Lap(b)` is a probability measure. -/
lemma isProbabilityMeasure_laplace (hb : 0 < b) : IsProbabilityMeasure (laplace b) := by
  constructor
  rw [laplace, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change ∫⁻ x, ENNReal.ofReal (laplacePDFReal b x) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_laplacePDFReal hb)
    (Filter.Eventually.of_forall (laplacePDFReal_nonneg hb)), integral_laplacePDFReal hb,
    ENNReal.ofReal_one]

lemma integral_laplace_eq (hb : 0 < b) (f : ℝ → ℝ) :
    ∫ x, f x ∂laplace b = ∫ x, laplacePDFReal b x * f x := by
  rw [laplace, integral_withDensity_eq_integral_toReal_smul (measurable_laplacePDF b)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [laplacePDF, ENNReal.toReal_ofReal (laplacePDFReal_nonneg hb _)]

lemma integrable_laplace_iff (hb : 0 < b) {f : ℝ → ℝ} :
    Integrable f (laplace b) ↔ Integrable (fun x => laplacePDFReal b x * f x) := by
  rw [laplace, integrable_withDensity_iff_integrable_smul' (measurable_laplacePDF b)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp [laplacePDF, ENNReal.toReal_ofReal (laplacePDFReal_nonneg hb _)]

lemma laplacePDFReal_mul_sq (b x : ℝ) :
    laplacePDFReal b x * x ^ 2 = (fun t => 1 / (2 * b) * (t ^ 2 * Real.exp (-t / b))) |x| := by
  simp only [laplacePDFReal, sq_abs]; ring

/-- `x ↦ x²` is `Lap(b)`-integrable. -/
lemma integrable_sq_laplace (hb : 0 < b) : Integrable (fun x : ℝ => x ^ 2) (laplace b) := by
  rw [integrable_laplace_iff hb]
  simp_rw [laplacePDFReal_mul_sq]
  exact integrable_comp_abs_of_integrableOn ((integrableOn_sq_mul_exp_neg_div hb).const_mul _)

lemma memLp_two_laplace (hb : 0 < b) : MemLp (fun x : ℝ => x) 2 (laplace b) :=
  (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr (integrable_sq_laplace hb)

/-- `x ↦ x` is `Lap(b)`-integrable. -/
lemma integrable_id_laplace (hb : 0 < b) : Integrable (fun x : ℝ => x) (laplace b) := by
  have := isProbabilityMeasure_laplace hb
  exact (memLp_two_laplace hb).integrable one_le_two

/-- `Lap(b)` has mean `0`. -/
lemma integral_id_laplace (hb : 0 < b) : ∫ x, x ∂laplace b = 0 := by
  rw [integral_laplace_eq hb]
  have h := integral_neg_eq_self (fun x => laplacePDFReal b x * x) volume
  have hodd : ∀ x, laplacePDFReal b (-x) * -x = -(laplacePDFReal b x * x) := by
    intro x; simp [laplacePDFReal, abs_neg]
  simp only [hodd, integral_neg] at h
  linarith

/-- `Lap(b)` has second moment `2b²`. -/
lemma integral_sq_laplace (hb : 0 < b) : ∫ x, x ^ 2 ∂laplace b = 2 * b ^ 2 := by
  rw [integral_laplace_eq hb]
  simp_rw [laplacePDFReal_mul_sq]
  rw [integral_comp_abs (f := fun t => 1 / (2 * b) * (t ^ 2 * Real.exp (-t / b))),
    integral_const_mul, integral_sq_mul_exp_neg_div hb]
  field_simp

/-- `Lap(b)` has variance `2b²`. -/
lemma variance_id_laplace (hb : 0 < b) : variance (fun x : ℝ => x) (laplace b) = 2 * b ^ 2 := by
  rw [variance_eq_integral (by fun_prop : AEMeasurable (fun x : ℝ => x) (laplace b)),
    integral_id_laplace hb]
  simpa using integral_sq_laplace hb

/-- Lower tail: `Lap(b)((-∞, -w]) = e^{-w/b}/2` for `w ≥ 0`. -/
lemma laplace_Iic_neg (hb : 0 < b) {w : ℝ} (hw : 0 ≤ w) :
    laplace b (Iic (-w)) = ENNReal.ofReal (Real.exp (-w / b) / 2) := by
  rw [laplace, withDensity_apply _ measurableSet_Iic]
  change ∫⁻ x in Iic (-w), ENNReal.ofReal (laplacePDFReal b x) = _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_laplacePDFReal hb).integrableOn
    (Filter.Eventually.of_forall (laplacePDFReal_nonneg hb))]
  congr 1
  have : ∫ x in Iic (-w), laplacePDFReal b x
      = ∫ x in Iic (-w), 1 / (2 * b) * Real.exp (1 / b * x) := by
    refine setIntegral_congr_fun measurableSet_Iic (fun x hx => ?_)
    have hx0 : x ≤ 0 := le_trans (mem_Iic.mp hx) (by linarith)
    simp only [laplacePDFReal, abs_of_nonpos hx0]
    rw [div_eq_mul_inv, mul_comm]; congr 2 <;> ring
  rw [this, integral_const_mul, integral_exp_mul_Iic (by positivity),
    show 1 / b * -w = -w / b by ring]
  field_simp

/-- The law of `c + Z` for `Z ~ Lap(b)` has density `y ↦ e^{-|y - c|/b}/(2b)`. -/
lemma laplace_map_const_add (b c : ℝ) :
    (laplace b).map (fun z => c + z) = volume.withDensity (fun y => laplacePDF b (y - c)) := by
  ext S hS
  rw [Measure.map_apply (measurable_const_add c) hS, laplace,
    withDensity_apply _ (measurable_const_add c hS), withDensity_apply _ hS]
  have := (measurePreserving_add_left (volume : Measure ℝ) c).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft c) (fun y => laplacePDF b (y - c)) S
  rw [← this]
  simp

/-- Density-ratio bound of the Laplace mechanism: for every measurable `S`,
`Pr(c + Z ∈ S) ≤ e^{|c - c'|/b} Pr(c' + Z ∈ S)`, `Z ~ Lap(b)`. -/
lemma laplace_map_const_add_le (hb : 0 < b) (c c' : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    (laplace b).map (fun z => c + z) S
      ≤ ENNReal.ofReal (Real.exp (|c - c'| / b)) * (laplace b).map (fun z => c' + z) S := by
  have hm : Measurable fun y => laplacePDF b (y - c') :=
    (measurable_laplacePDF b).comp (measurable_sub_const c')
  rw [laplace_map_const_add, laplace_map_const_add, withDensity_apply _ hS,
    withDensity_apply _ hS, ← lintegral_const_mul _ hm]
  refine lintegral_mono fun y => ?_
  simp only [laplacePDF]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [laplacePDFReal]
  rw [← mul_div_assoc, ← Real.exp_add]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
  rw [← add_div, div_le_div_iff_of_pos_right hb]
  have := abs_sub_le y c c'
  linarith

end Limites
