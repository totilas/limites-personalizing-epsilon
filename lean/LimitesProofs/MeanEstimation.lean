import LimitesProofs.Laplace
import LimitesProofs.Privacy.Defs
import LimitesProofs.Risks

/-!
# Private mean estimation: Laplace, affine and threshold estimators

Paper result ↔ Lean name.

* Definition "Laplace mechanism" (`(ε, 0)`-DP): `laplaceMech_approxDP`.
* Section "Best affine estimator", heterogeneous `ε`-DP of `∑ wᵢ xᵢ + Lap(η)` holds
  iff `η ≥ maxᵢ wᵢ/ε⁽ⁱ⁾`: `affineMech_hetDP_iff`.
* Definition "Unique-threshold `ε` estimator", the threshold mechanism `M_ε` is
  heterogeneous `ε`-DP: `thrMech_hetDP` (`thrMech_eq_affineMech` identifies it with an
  affine estimator).
* Definition "Distributionally-Robust MSE" (`mse`, `drMSE`, `SupportedProb`) and the
  first paragraph of the proof of Lemma `clm:threshold_characterization`:
  unbiasedness `mean_affineMech`, `mse_affineMech` (`MSE = Var(P) ∑ wᵢ² + 2η²`),
  Popoviciu-type bound `variance_le_quarter`, two-point extremal law `twoPoint`, and
  `drMSE_affineMech` (`DR-MSE = ∑ wᵢ²/4 + 2η²`).
* Lemma `clm:threshold_characterization`, first equality of Eq. `eq:mseafftedious`:
  `sInf_affRiskSet` (best DR-MSE over heterogeneous-DP affine Laplace estimators equals
  `persRisk ∅ ε (1/4) 2`).
* Eq. `eq:msethr`: `drMSE_thrMech` (`DR-MSE(M_ε) = 1/(4 n_ε) + 2/(ε n_ε)²`) and
  `sInf_thrRiskSet` (its infimum over thresholds equals `thrRisk ∅ ε (1/4) 2`).
* Proof of Theorem `thm:lower-bound-general-m-levels` (`P = δ₀`):
  `mse_thrMech_dirac_zero`.

Conventions.  Datasets are `Fin n → ℝ`.  A mechanism is a map from datasets to the law
of its output (`Measure ℝ`); privacy is stated for datasets with records in
`[-1/2, 1/2]` (`Fin n → Icc (-1/2) (1/2)`), i.e. for the restriction of the mechanism to
the data domain of the paper.  The MSE of a mechanism `M` under a data law `P` is
`E_{x ~ Pⁿ} E_{y ~ M(x)} (y - μ_P)²` with `Pⁿ = Measure.pi`; for the affine estimators
this is `E[(∑ wᵢ xᵢ + Z - μ_P)²]` with `Z ~ Lap(η)` independent of the data.  The
distributionally-robust MSE is the `sSup` over all probability measures `P` on `ℝ` with
`P([-1/2, 1/2]) = 1`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Limites

/-! ## The Laplace mechanism -/

/-- The Laplace mechanism `D ↦ f(D) + Lap(b)` (as the law of its output). -/
noncomputable def laplaceMech {Data : Type*} (f : Data → ℝ) (b : ℝ) (D : Data) : Measure ℝ :=
  (laplace b).map (fun z => f D + z)

/-- **Definition "Laplace mechanism".**  If `|f(x) - f(x')| ≤ Δ` for all neighbours
`x ∼ x'` (for an arbitrary neighbouring relation `Adj`), then `x ↦ f(x) + Lap(Δ/ε)` is
`(ε, 0)`-DP.  (The paper takes `Δ` to be the maximum; any upper bound `Δ > 0` works.) -/
theorem laplaceMech_approxDP {Data : Type*} (Adj : Data → Data → Prop) (f : Data → ℝ)
    {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) (hf : ∀ D D', Adj D D' → |f D - f D'| ≤ Δ) :
    ApproxDP Adj (laplaceMech f (Δ / ε)) ε 0 := by
  intro D D' hadj S hS
  simp only [laplaceMech]
  rw [ENNReal.ofReal_zero, add_zero]
  refine (laplace_map_const_add_le (by positivity) (f D) (f D') hS).trans ?_
  gcongr
  rw [div_le_iff₀ (by positivity)]
  calc |f D - f D'| ≤ Δ := hf D D' hadj
    _ = ε * (Δ / ε) := by field_simp

/-! ## Affine estimators and heterogeneous DP -/

/-- The affine Laplace estimator `x ↦ ∑ wᵢ xᵢ + Lap(η)`. -/
noncomputable def affineMech {n : ℕ} (w : Fin n → ℝ) (η : ℝ) : (Fin n → ℝ) → Measure ℝ :=
  laplaceMech (fun x => ∑ i, w i * x i) η

/-- The data domain `[-1/2, 1/2]`. -/
abbrev Rec : Type := Icc (-1/2 : ℝ) (1/2)

lemma sum_sub_of_neighborAt {n : ℕ} (w : Fin n → ℝ) {i : Fin n} {D D' : Fin n → Rec}
    (h : NeighborAt i D D') :
    ∑ j, w j * (D j : ℝ) - ∑ j, w j * (D' j : ℝ) = w i * ((D i : ℝ) - D' i) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · ring
  · intro j _ hj; rw [h j hj]; ring
  · simp

/-- **Section "Best affine estimator".**  For records in `[-1/2, 1/2]`, nonnegative
weights `w`, noise scale `η > 0` and budgets `ε⁽ⁱ⁾ > 0`, the affine estimator
`∑ wᵢ xᵢ + Lap(η)` is heterogeneous `ε`-DP iff `η ≥ wᵢ/ε⁽ⁱ⁾` for every `i`. -/
theorem affineMech_hetDP_iff {n : ℕ} {w : Fin n → ℝ} {η : ℝ} {ε : Fin n → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hη : 0 < η) (hε : ∀ i, 0 < ε i) :
    HetDP (fun D : Fin n → Rec => affineMech w η (fun i => (D i : ℝ))) ε ↔
      ∀ i, w i / ε i ≤ η := by
  constructor
  · intro h i
    by_contra hlt
    push Not at hlt
    have hwi : η * ε i < w i := by rwa [lt_div_iff₀ (hε i)] at hlt
    let lo : Rec := ⟨-1/2, by norm_num, by norm_num⟩
    let hi : Rec := ⟨1/2, by norm_num, by norm_num⟩
    let D : Fin n → Rec := fun _ => lo
    let D' : Fin n → Rec := Function.update D i hi
    have hnb : NeighborAt i D D' := fun j hj => (Function.update_of_ne hj hi D).symm
    set c := ∑ j, w j * (D j : ℝ) with hc
    have hc' : ∑ j, w j * (D' j : ℝ) = c + w i := by
      have := sum_sub_of_neighborAt w hnb
      simp only [D', Function.update_self, D] at this
      simp only [D', D, hc]
      norm_num at this ⊢
      linarith
    have key := h i D D' hnb (Iic c) measurableSet_Iic
    simp only [affineMech, laplaceMech, hc'] at key
    rw [← hc, Measure.map_apply (measurable_const_add _) measurableSet_Iic,
      Measure.map_apply (measurable_const_add _) measurableSet_Iic] at key
    have e1 : (fun z => c + z) ⁻¹' Iic c = Iic (-0) := by ext z; simp
    have e2 : (fun z => c + w i + z) ⁻¹' Iic c = Iic (-w i) := by
      ext z; simp only [mem_preimage, mem_Iic]; constructor <;> intro <;> linarith
    rw [e1, e2, laplace_Iic_neg hη le_rfl, laplace_Iic_neg hη (hw i),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
    have hlt' : ε i - w i / η < 0 := by
      rw [sub_neg, lt_div_iff₀ hη]; linarith
    have : Real.exp (ε i) * (Real.exp (-w i / η) / 2) < Real.exp (-0 / η) / 2 := by
      rw [neg_zero, zero_div, Real.exp_zero, ← mul_div_assoc, ← Real.exp_add,
        div_lt_div_iff_of_pos_right two_pos, ← Real.exp_zero, Real.exp_lt_exp, neg_div]
      linarith
    linarith
  · intro h i D D' hnb S hS
    simp only [affineMech, laplaceMech]
    refine (laplace_map_const_add_le hη _ (∑ j, w j * (D' j : ℝ)) hS).trans ?_
    gcongr
    rw [sum_sub_of_neighborAt w hnb, abs_mul, abs_of_nonneg (hw i), div_le_iff₀ hη]
    have hd : |((D i : ℝ) - D' i)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [(D i).2.1, (D i).2.2, (D' i).2.1, (D' i).2.2]
    have := (div_le_iff₀ (hε i)).mp (h i)
    calc w i * |((D i : ℝ) - D' i)| ≤ w i * 1 := mul_le_mul_of_nonneg_left hd (hw i)
      _ ≤ ε i * η := by linarith

/-! ## The threshold mechanism -/

/-- The weights `𝟙(ε)ᵢ / n_ε` of the threshold mechanism. -/
noncomputable def thrWeights {n : ℕ} (ε : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  (if t ≤ ε i then 1 else 0) / (nThr ∅ ε t : ℝ)

/-- **Definition "Unique-threshold `ε` estimator"**: the threshold mechanism
`M_t(D) = (1/n_t) ∑ᵢ 𝟙(t)ᵢ xᵢ + Lap(Δ/(n_t t))` with `Δ = 1` (the length of the data
range), where `n_t = nThr ∅ ε t = #{i | ε⁽ⁱ⁾ ≥ t}`. -/
noncomputable def thrMech {n : ℕ} (ε : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) : Measure ℝ :=
  (laplace (1 / ((nThr ∅ ε t : ℝ) * t))).map
    (fun z => 1 / (nThr ∅ ε t : ℝ) * ∑ i, (if t ≤ ε i then (1 : ℝ) else 0) * x i + z)

lemma thrMech_eq_affineMech {n : ℕ} (ε : Fin n → ℝ) (t : ℝ) :
    thrMech ε t = affineMech (thrWeights ε t) (1 / ((nThr ∅ ε t : ℝ) * t)) := by
  funext x
  simp only [thrMech, affineMech, laplaceMech, thrWeights, Finset.mul_sum]
  congr 2; ext z; congr 1; refine Finset.sum_congr rfl fun i _ => ?_; ring

lemma nThr_empty_eq_sum {n : ℕ} (ε : Fin n → ℝ) (t : ℝ) :
    (nThr ∅ ε t : ℝ) = ∑ i, if t ≤ ε i then (1 : ℝ) else 0 := by
  simp [nThr, Finset.sum_boole]

lemma thrWeights_nonneg {n : ℕ} (ε : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    0 ≤ thrWeights ε t i := by
  unfold thrWeights; split_ifs <;> positivity

lemma sum_thrWeights {n : ℕ} {ε : Fin n → ℝ} {t : ℝ} (hN : 0 < nThr ∅ ε t) :
    ∑ i, thrWeights ε t i = 1 := by
  have hN' : (0 : ℝ) < nThr ∅ ε t := by exact_mod_cast hN
  simp only [thrWeights, ← Finset.sum_div, ← nThr_empty_eq_sum]
  exact div_self hN'.ne'

lemma sum_sq_thrWeights {n : ℕ} {ε : Fin n → ℝ} {t : ℝ} (hN : 0 < nThr ∅ ε t) :
    ∑ i, thrWeights ε t i ^ 2 = 1 / (nThr ∅ ε t : ℝ) := by
  have hN' : (0 : ℝ) < nThr ∅ ε t := by exact_mod_cast hN
  have : ∀ i, thrWeights ε t i ^ 2 = (if t ≤ ε i then (1 : ℝ) else 0) / (nThr ∅ ε t : ℝ) ^ 2 :=
    fun i => by unfold thrWeights; split_ifs <;> simp
  simp only [this, ← Finset.sum_div, ← nThr_empty_eq_sum]
  field_simp

/-- **Definition "Unique-threshold `ε` estimator"**: the threshold mechanism `M_t` is
heterogeneous `ε`-DP (for any threshold `t > 0` retaining `n_t ≥ 1` records). -/
theorem thrMech_hetDP {n : ℕ} {ε : Fin n → ℝ} (hε : ∀ i, 0 < ε i) {t : ℝ} (ht : 0 < t)
    (hN : 0 < nThr ∅ ε t) :
    HetDP (fun D : Fin n → Rec => thrMech ε t (fun i => (D i : ℝ))) ε := by
  have hN' : (0 : ℝ) < nThr ∅ ε t := by exact_mod_cast hN
  rw [thrMech_eq_affineMech]
  refine (affineMech_hetDP_iff (thrWeights_nonneg ε t) (div_pos one_pos (mul_pos hN' ht))
    hε).mpr fun i => ?_
  unfold thrWeights
  split_ifs with h
  · rw [div_div, one_div_le_one_div (mul_pos hN' (hε i)) (mul_pos hN' ht)]
    exact mul_le_mul_of_nonneg_left h hN'.le
  · simp only [zero_div]; exact (div_pos one_pos (mul_pos hN' ht)).le

/-! ## Mean-squared error -/

/-- Probability measures on `ℝ` supported in `[-1/2, 1/2]`. -/
def SupportedProb : Set (Measure ℝ) :=
  {P | IsProbabilityMeasure P ∧ ∀ᵐ x ∂P, x ∈ Icc (-1/2 : ℝ) (1/2)}

/-- MSE `E[(μ̂ - μ_P)²]` of a mechanism `M` when the `n` records are i.i.d. from `P`
(randomness over the data and the mechanism). -/
noncomputable def mse {n : ℕ} (M : (Fin n → ℝ) → Measure ℝ) (P : Measure ℝ) : ℝ :=
  ∫ x, ∫ y, (y - ∫ t, t ∂P) ^ 2 ∂(M x) ∂(Measure.pi fun _ : Fin n => P)

/-- **Definition "Distributionally-Robust MSE"**: `sup_P E[(μ̂ - μ_P)²]` over data laws
supported in `[-1/2, 1/2]`. -/
noncomputable def drMSE {n : ℕ} (M : (Fin n → ℝ) → Measure ℝ) : ℝ :=
  sSup (mse M '' SupportedProb)

section MSE

variable {n : ℕ} {P : Measure ℝ}

lemma integral_sq_laplace_shift {η : ℝ} (hη : 0 < η) (c μ : ℝ) :
    ∫ y, (y - μ) ^ 2 ∂((laplace η).map (fun z => c + z)) = (c - μ) ^ 2 + 2 * η ^ 2 := by
  have := isProbabilityMeasure_laplace hη
  rw [integral_map (measurable_const_add c).aemeasurable (by fun_prop)]
  have e : ∀ z, (c + z - μ) ^ 2 = ((c - μ) ^ 2 + 2 * (c - μ) * z) + z ^ 2 := fun z => by ring
  simp_rw [e]
  have h0 : Integrable (fun _ : ℝ => (c - μ) ^ 2) (laplace η) := integrable_const _
  have h1 : Integrable (fun z : ℝ => 2 * (c - μ) * z) (laplace η) :=
    (integrable_id_laplace hη).const_mul _
  have h01 : Integrable (fun z : ℝ => (c - μ) ^ 2 + 2 * (c - μ) * z) (laplace η) := h0.add h1
  rw [integral_add h01 (integrable_sq_laplace hη), integral_add h0 h1, integral_const,
    probReal_univ, one_smul, integral_const_mul, integral_id_laplace hη,
    integral_sq_laplace hη]
  ring

lemma integral_laplace_shift {η : ℝ} (hη : 0 < η) (c : ℝ) :
    ∫ y, y ∂((laplace η).map (fun z => c + z)) = c := by
  have := isProbabilityMeasure_laplace hη
  rw [integral_map (measurable_const_add c).aemeasurable (by fun_prop),
    integral_add (integrable_const _) (integrable_id_laplace hη), integral_const,
    probReal_univ, one_smul, integral_id_laplace hη, add_zero]

lemma memLp_coord (hP : P ∈ SupportedProb) (i : Fin n) (p : ℝ≥0∞) :
    MemLp (fun x : Fin n → ℝ => x i) p (Measure.pi fun _ => P) := by
  have := hP.1
  exact (memLp_of_bounded hP.2 aestronglyMeasurable_id p).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => P) i)

lemma integral_coord (hP : P ∈ SupportedProb) (i : Fin n) :
    ∫ x : Fin n → ℝ, x i ∂(Measure.pi fun _ => P) = ∫ t, t ∂P := by
  have := hP.1
  have h := integral_map (μ := Measure.pi fun _ : Fin n => P)
    (measurable_pi_apply i).aemeasurable (f := fun t : ℝ => t) aestronglyMeasurable_id
  rw [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq] at h
  exact h.symm

lemma integral_weighted_sum (hP : P ∈ SupportedProb) {w : Fin n → ℝ} (hw : ∑ i, w i = 1) :
    ∫ x : Fin n → ℝ, ∑ i, w i * x i ∂(Measure.pi fun _ => P) = ∫ t, t ∂P := by
  have := hP.1
  rw [integral_finsetSum _ fun i _ => ((memLp_coord hP i 1).integrable le_rfl).const_mul _]
  simp_rw [integral_const_mul, integral_coord hP, ← Finset.sum_mul, hw, one_mul]

/-- The affine estimator is unbiased when `∑ wᵢ = 1`: `E[μ̂_w] = μ_P`. -/
theorem mean_affineMech (hP : P ∈ SupportedProb) {w : Fin n → ℝ} {η : ℝ} (hη : 0 < η)
    (hw : ∑ i, w i = 1) :
    ∫ x, ∫ y, y ∂(affineMech w η x) ∂(Measure.pi fun _ : Fin n => P) = ∫ t, t ∂P := by
  simp only [affineMech, laplaceMech, integral_laplace_shift hη]
  exact integral_weighted_sum hP hw

/-- The data part of the error: `E[(∑ wᵢ xᵢ - μ_P)²] = Var(P) ∑ wᵢ²` when `∑ wᵢ = 1`. -/
lemma integral_sq_weighted_sum (hP : P ∈ SupportedProb) {w : Fin n → ℝ}
    (hw : ∑ i, w i = 1) :
    ∫ x : Fin n → ℝ, (∑ i, w i * x i - ∫ t, t ∂P) ^ 2 ∂(Measure.pi fun _ => P)
      = variance id P * ∑ i, w i ^ 2 := by
  have := hP.1
  set X : Fin n → (Fin n → ℝ) → ℝ := fun i x => w i * x i with hX
  have hmem : ∀ i, MemLp (X i) 2 (Measure.pi fun _ => P) :=
    fun i => (memLp_coord hP i 2).const_mul _
  have hS : (fun x : Fin n → ℝ => ∑ i, w i * x i) = ∑ i, X i := by
    ext x; simp [hX, Finset.sum_apply]
  have hind : iIndepFun X (Measure.pi fun _ : Fin n => P) :=
    iIndepFun_pi (X := fun i (t : ℝ) => w i * t) (fun i => by fun_prop)
  have hvar := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hmem i)
    (fun i _ j _ hij => hind.indepFun hij)
  have hSm : Measurable fun x : Fin n → ℝ => ∑ i, w i * x i := by fun_prop
  rw [← hS, variance_eq_integral hSm.aemeasurable, integral_weighted_sum hP hw] at hvar
  rw [hvar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hX, variance_const_mul, mul_comm]
  congr 1
  exact (measurePreserving_eval (fun _ : Fin n => P) i).variance_fun_comp
    (f := id) measurable_id.aemeasurable

/-- **DR-MSE, proof of Lemma `clm:threshold_characterization`.**  For `P` supported in
`[-1/2, 1/2]` and `∑ wᵢ = 1`, `E[(∑ wᵢ xᵢ + Z - μ_P)²] = Var(P) ∑ wᵢ² + 2η²`,
`Z ~ Lap(η)` independent of the i.i.d. data. -/
theorem mse_affineMech (hP : P ∈ SupportedProb) {w : Fin n → ℝ} {η : ℝ} (hη : 0 < η)
    (hw : ∑ i, w i = 1) :
    mse (affineMech w η) P = variance id P * ∑ i, w i ^ 2 + 2 * η ^ 2 := by
  have := hP.1
  have h1 : mse (affineMech w η) P = ∫ x : Fin n → ℝ,
      ((∑ i, w i * x i - ∫ t, t ∂P) ^ 2 + 2 * η ^ 2) ∂(Measure.pi fun _ => P) := by
    unfold mse affineMech laplaceMech
    congr 1; funext x
    exact integral_sq_laplace_shift hη _ _
  have hS : MemLp (fun x : Fin n → ℝ => ∑ i, w i * x i) 2 (Measure.pi fun _ => P) :=
    memLp_finsetSum _ fun i _ => (memLp_coord hP i 2).const_mul (w i)
  have hS' : MemLp (fun x : Fin n → ℝ => ∑ i, w i * x i - ∫ t, t ∂P) 2
      (Measure.pi fun _ => P) := hS.sub (memLp_const _)
  have hint : Integrable (fun x : Fin n → ℝ => (∑ i, w i * x i - ∫ t, t ∂P) ^ 2)
      (Measure.pi fun _ => P) := hS'.integrable_sq
  rw [h1, integral_add hint (integrable_const _), integral_sq_weighted_sum hP hw, integral_const,
    probReal_univ, one_smul]

/-- Popoviciu's bound for the data range `[-1/2, 1/2]`: `Var(P) ≤ 1/4`. -/
lemma variance_le_quarter (hP : P ∈ SupportedProb) : variance id P ≤ 1 / 4 := by
  have := hP.1
  have h := variance_le_sq_of_bounded (X := id) hP.2 measurable_id.aemeasurable
  norm_num at h ⊢
  exact h

/-- The extremal law `½ δ_{-1/2} + ½ δ_{1/2}`. -/
noncomputable def twoPoint : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (-1/2 : ℝ) + (1 / 2 : ℝ≥0∞) • Measure.dirac (1/2 : ℝ)

lemma twoPoint_mem : twoPoint ∈ SupportedProb := by
  refine ⟨⟨?_⟩, ?_⟩
  · simp [twoPoint, ENNReal.inv_two_add_inv_two]
  · simp only [twoPoint, ae_add_measure_iff]
    constructor <;> refine Measure.ae_smul_measure ?_ _ <;>
      exact (ae_dirac_iff measurableSet_Icc).mpr (by norm_num)

lemma integral_twoPoint (f : ℝ → ℝ) :
    ∫ x, f x ∂twoPoint = (f (-1/2) + f (1/2)) / 2 := by
  have h1 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1/2 : ℝ)) :=
    (integrable_dirac enorm_lt_top).smul_measure (by simp)
  have h2 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac (1/2 : ℝ)) :=
    (integrable_dirac enorm_lt_top).smul_measure (by simp)
  rw [twoPoint, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp; ring

lemma variance_twoPoint : variance id twoPoint = 1 / 4 := by
  rw [variance_eq_integral measurable_id.aemeasurable]
  simp only [id, integral_twoPoint]
  norm_num

/-- **DR-MSE of the affine estimator** (proof of Lemma `clm:threshold_characterization`):
for `∑ wᵢ = 1` and `η > 0`, `sup_P E[(∑ wᵢ xᵢ + Z - μ_P)²] = ∑ wᵢ²/4 + 2η²`, the
supremum being attained at `P = ½ δ_{-1/2} + ½ δ_{1/2}`. -/
theorem drMSE_affineMech {w : Fin n → ℝ} {η : ℝ} (hη : 0 < η) (hw : ∑ i, w i = 1) :
    drMSE (affineMech w η) = 1 / 4 * ∑ i, w i ^ 2 + 2 * η ^ 2 := by
  refine IsGreatest.csSup_eq ⟨⟨twoPoint, twoPoint_mem, ?_⟩, ?_⟩
  · rw [mse_affineMech twoPoint_mem hη hw, variance_twoPoint]
  · rintro _ ⟨P, hP, rfl⟩
    rw [mse_affineMech hP hη hw]
    have h0 : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (w i)
    have := mul_le_mul_of_nonneg_right (variance_le_quarter hP) h0
    linarith

end MSE

/-! ## Optimal affine risk and threshold risk -/

/-- DR-MSEs of all unbiased affine Laplace estimators that are heterogeneous `ε`-DP. -/
def affRiskSet {n : ℕ} (ε : Fin n → ℝ) : Set ℝ :=
  {r | ∃ (w : Fin n → ℝ) (η : ℝ), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ 0 < η ∧
    HetDP (fun D : Fin n → Rec => affineMech w η (fun i => (D i : ℝ))) ε ∧
    drMSE (affineMech w η) = r}

/-- **Lemma `clm:threshold_characterization`, first equality of Eq. `eq:mseafftedious`.**
The infimum of the DR-MSE over unbiased affine Laplace estimators (`w ≥ 0`, `∑ w = 1`,
`η > 0`) that are heterogeneous `ε`-DP equals
`𝓡_pers(ε; 1/4, 2) = inf_w {∑ wᵢ²/4 + 2 (maxᵢ wᵢ/ε⁽ⁱ⁾)²}`. -/
theorem sInf_affRiskSet {n : ℕ} {ε : Fin n → ℝ} (hε : ∀ i, 0 < ε i) :
    sInf (affRiskSet ε) = persRisk ∅ ε (1 / 4) 2 := by
  unfold persRisk
  congr 1
  ext r
  constructor
  · rintro ⟨w, η, hw, hsum, hη, hdp, rfl⟩
    refine ⟨w, η, ⟨hw, hsum, hη.le, fun i _ => ?_⟩, ?_⟩
    · have := ((affineMech_hetDP_iff hw hη hε).mp hdp i)
      rwa [div_le_iff₀ (hε i)] at this
    · rw [drMSE_affineMech hη hsum, persObj]
  · rintro ⟨w, M, ⟨hw, hsum, hM, hwM⟩, rfl⟩
    have hMpos : 0 < M := by
      obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
        (g := w) (by simp [hsum])
      have := hwM i (Finset.notMem_empty i)
      by_contra h
      push Not at h
      nlinarith [hε i]
    refine ⟨w, M, hw, hsum, hMpos, (affineMech_hetDP_iff hw hMpos hε).mpr fun i => ?_, ?_⟩
    · rw [div_le_iff₀ (hε i)]; exact hwM i (Finset.notMem_empty i)
    · rw [drMSE_affineMech hMpos hsum, persObj]

/-- **Eq. `eq:msethr`.**  For a threshold `t > 0` retaining `n_t ≥ 1` records, the DR-MSE
of the threshold mechanism is `1/(4 n_t) + 2/(t n_t)²`. -/
theorem drMSE_thrMech {n : ℕ} {ε : Fin n → ℝ} {t : ℝ} (ht : 0 < t) (hN : 0 < nThr ∅ ε t) :
    drMSE (thrMech ε t) = thrObj (1 / 4) 2 t (nThr ∅ ε t) := by
  have hN' : (0 : ℝ) < nThr ∅ ε t := by exact_mod_cast hN
  rw [thrMech_eq_affineMech, drMSE_affineMech (div_pos one_pos (mul_pos hN' ht))
    (sum_thrWeights hN),
    sum_sq_thrWeights hN, thrObj]
  field_simp

/-- **Eq. `eq:msethr`.**  The infimum over thresholds `t > 0` with `n_t ≥ 1` of the DR-MSE
of the threshold mechanism `M_t` equals `𝓡_thr(ε; 1/4, 2)`. -/
theorem sInf_thrRiskSet {n : ℕ} (ε : Fin n → ℝ) :
    sInf {r | ∃ t, 0 < t ∧ 0 < nThr ∅ ε t ∧ drMSE (thrMech ε t) = r}
      = thrRisk ∅ ε (1 / 4) 2 := by
  unfold thrRisk thrSet
  congr 1
  ext r
  constructor
  · rintro ⟨t, ht, hN, rfl⟩; exact ⟨t, ht, hN, (drMSE_thrMech ht hN).symm⟩
  · rintro ⟨t, ht, hN, rfl⟩; exact ⟨t, ht, hN, drMSE_thrMech ht hN⟩

/-- **Proof of Theorem `thm:lower-bound-general-m-levels`**: for `P = δ₀` the MSE of the
threshold mechanism is exactly `2/(n_t t)²`. -/
theorem mse_thrMech_dirac_zero {n : ℕ} {ε : Fin n → ℝ} {t : ℝ} (ht : 0 < t)
    (hN : 0 < nThr ∅ ε t) :
    mse (thrMech ε t) (Measure.dirac 0) = 2 / ((nThr ∅ ε t : ℝ) * t) ^ 2 := by
  have hN' : (0 : ℝ) < nThr ∅ ε t := by exact_mod_cast hN
  have hmem : Measure.dirac (0 : ℝ) ∈ SupportedProb :=
    ⟨inferInstance, (ae_dirac_iff measurableSet_Icc).mpr (by norm_num)⟩
  rw [thrMech_eq_affineMech, mse_affineMech hmem (div_pos one_pos (mul_pos hN' ht))
    (sum_thrWeights hN),
    variance_dirac, zero_mul, zero_add]
  field_simp

end Limites
