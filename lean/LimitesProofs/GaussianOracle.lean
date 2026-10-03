import LimitesProofs.Renyi
import LimitesProofs.Risks

/-!
# Gaussian gradient oracles (Section `sec:affine-private-gradients`)

Datasets are `n` per-record gradients in the closed ball `B_C ⊂ ℝ^d`
(`GradBall d C`, Assumption `ass:gradient-estimation`.3); a release maps a dataset to the
law of its output.  Budgets are finite zCDP budgets `ρᵢ > 0`, `uᵢ = √ρᵢ` (so the public set
of `Risks.lean` is `∅`).

Random model for the MSEs (Eq. `eq:gradient-assumptions-formal`): the gradients
`g₁, …, gₙ : Ω → ℝ^d` are independent (`iIndepFun`) square-integrable random vectors on a
probability space `(Ω, P)` with common mean `m = ∇F(θ)` and `E‖gᵢ − m‖² = V`; the noise
`Z ∼ N(0, s² I_d)` is independent of them, realised on the product `P ⊗ N(0, s² I_d)`.

* `affineRelease` — Eq. `eq:affine-gradient-formal`.
* `affineRelease_hetZCDP_iff`, `affineRelease_hetZCDP_iff_noise` — Prop.
  `prop:affine-gradient-formal`, Eq. `eq:affine-gradient-noise-formal` (the release is
  heterogeneous `ρ`-zCDP iff `s² ≥ s_w² = 2C²(maxᵢ wᵢ/uᵢ)²`); `affineRelease_hetZCDP_of`
  is the sufficiency direction.
* `affine_mse_eq` (general model, pairwise independence), `affineMSE_eq`,
  `affineMSE_minNoise` — Eq. `eq:affine-gradient-risk-formal`; `affineMSE_le` — the
  bounded-variance version.
* `persOracleMSE`, `persOracleMSE_eq` — Def. `def:oracle-mse` and the first equality of
  Eq. `eq:gradient-claim-form`: `𝒱_pers(θ) = 𝓡_pers(u; V(θ), 2dC²)`.
* `thrRelease`, `thrRelease_hetZCDP`, `thrMSE_eq`, `thrOracleMSE`, `thrOracleMSE_eq` —
  Eqs. `eq:threshold-gradient` and `eq:gradient-threshold-risk`:
  `𝒱_thr(θ) = 𝓡_thr(u; V(θ), 2dC²)`.
* `hetZCDP_preprocess` (in `Renyi.lean`) — remark after Lemma `lem:preprocessing`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Limites

variable {n d : ℕ}

/-- Admissible per-record gradients: the closed ball of radius `C` in `ℝ^d`. -/
abbrev GradBall (d : ℕ) (C : ℝ) := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) C

/-- The affine release `D ↦ law of ∑ᵢ wᵢ gᵢ + Z`, `Z ∼ N(0, s² I_d)`
(Eq. `eq:affine-gradient-formal`), on datasets of gradients `gᵢ ∈ B_C`. -/
noncomputable def affineRelease (C : ℝ) (w : Fin n → ℝ) (s : ℝ) (D : Fin n → GradBall d C) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (gaussNoise 0 s).map (fun z ↦ ∑ i, w i • (D i : EuclideanSpace ℝ (Fin d)) + z)

lemma affineRelease_eq (C : ℝ) (w : Fin n → ℝ) (s : ℝ) (D : Fin n → GradBall d C) :
    affineRelease C w s D = gaussNoise (∑ i, w i • (D i : EuclideanSpace ℝ (Fin d))) s := by
  rw [affineRelease, gaussNoise_map_const_add, add_zero]

lemma sum_smul_sub_of_neighborAt {E : Type*} [AddCommGroup E] [Module ℝ E] {i : Fin n}
    {D D' : Fin n → E} (h : NeighborAt i D D') (w : Fin n → ℝ) :
    ∑ j, w j • D j - ∑ j, w j • D' j = w i • (D i - D' i) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [smul_sub]
  · intro j _ hj; rw [h j hj, sub_self]
  · simp

/-- Sufficiency in Eq. `eq:affine-gradient-noise-formal`: replacing record `i` moves the
mean by at most `2 C |wᵢ|`, so the release is `2 C² wᵢ² / s²`-zCDP for record `i`. -/
theorem affineRelease_hetZCDP_of {C : ℝ} (w : Fin n → ℝ) {s : ℝ} (hs : 0 < s)
    (ρ : Fin n → ℝ) (h : ∀ i, 2 * C ^ 2 * w i ^ 2 / s ^ 2 ≤ ρ i) :
    HetZCDP (affineRelease (d := d) C w s) ρ := by
  have hrel : affineRelease (d := d) C w s
      = fun D ↦ gaussNoise (∑ i, w i • (D i : EuclideanSpace ℝ (Fin d))) s :=
    funext (affineRelease_eq C w s)
  rw [hrel]
  intro i
  rw [gaussMech_zCDP_iff _ _ hs.ne']
  intro D D' hD
  have hN' : NeighborAt i (fun j ↦ (D j : EuclideanSpace ℝ (Fin d)))
      (fun j ↦ (D' j : EuclideanSpace ℝ (Fin d))) := fun j hj ↦ congrArg Subtype.val (hD j hj)
  rw [sum_smul_sub_of_neighborAt hN']
  have hDi : ‖(D i : EuclideanSpace ℝ (Fin d))‖ ≤ C := mem_closedBall_zero_iff.mp (D i).2
  have hDi' : ‖(D' i : EuclideanSpace ℝ (Fin d))‖ ≤ C := mem_closedBall_zero_iff.mp (D' i).2
  have hsub : ‖(D i : EuclideanSpace ℝ (Fin d)) - D' i‖ ≤ 2 * C :=
    (norm_sub_le _ _).trans (by linarith)
  have hsq : ‖w i • ((D i : EuclideanSpace ℝ (Fin d)) - D' i)‖ ^ 2
      ≤ w i ^ 2 * (2 * C) ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    gcongr
  calc ‖w i • ((D i : EuclideanSpace ℝ (Fin d)) - D' i)‖ ^ 2 / (2 * s ^ 2)
      ≤ w i ^ 2 * (2 * C) ^ 2 / (2 * s ^ 2) := by gcongr
    _ = 2 * C ^ 2 * w i ^ 2 / s ^ 2 := by field_simp
    _ ≤ ρ i := h i

/-- **Prop. `prop:affine-gradient-formal`, Eq. `eq:affine-gradient-noise-formal`
(record-wise form).**  For gradients in the ball `B_C` (`C ≥ 0`, `d ≥ 1`) and `s > 0`, the
affine release is heterogeneous `ρ`-zCDP if and only if `2 C² wᵢ² / s² ≤ ρᵢ` for every `i`.
Necessity uses the records `gᵢ = C e₁` and `gᵢ' = −C e₁`. -/
theorem affineRelease_hetZCDP_iff (hd : 0 < d) {C : ℝ} (hC : 0 ≤ C) (w : Fin n → ℝ)
    {s : ℝ} (hs : 0 < s) (ρ : Fin n → ℝ) :
    HetZCDP (affineRelease (d := d) C w s) ρ ↔ ∀ i, 2 * C ^ 2 * w i ^ 2 / s ^ 2 ≤ ρ i := by
  refine ⟨fun h ↦ ?_, affineRelease_hetZCDP_of w hs ρ⟩
  have hrel : affineRelease (d := d) C w s
      = fun D ↦ gaussNoise (∑ i, w i • (D i : EuclideanSpace ℝ (Fin d))) s :=
    funext (affineRelease_eq C w s)
  rw [hrel] at h
  intro i
  have h := (gaussMech_zCDP_iff _ _ hs.ne' _).1 (h i)
  set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  have hmem : ∀ c : ℝ, |c| ≤ C → c • e ∈ GradBall d C := fun c hc ↦ by
    simp [norm_smul, he, hc]
  let D : Fin n → GradBall d C := fun _ ↦ ⟨C • e, hmem C (abs_of_nonneg hC).le⟩
  let D' : Fin n → GradBall d C :=
    Function.update D i ⟨(-C) • e, hmem (-C) (by simp [abs_of_nonneg hC])⟩
  have hN : NeighborAt i D D' := fun j hj ↦ by simp [D', Function.update_of_ne hj]
  have h1 := h D D' hN
  have hN' : NeighborAt i (fun j ↦ (D j : EuclideanSpace ℝ (Fin d)))
      (fun j ↦ (D' j : EuclideanSpace ℝ (Fin d))) := fun j hj ↦ congrArg Subtype.val (hN j hj)
  rw [sum_smul_sub_of_neighborAt hN'] at h1
  have hdiff : (D i : EuclideanSpace ℝ (Fin d)) - D' i = (2 * C) • e := by
    simp only [D', Function.update_self, D]
    module
  rw [hdiff, norm_smul, norm_smul, he, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 2 * C)] at h1
  have : (|w i| * (2 * C * 1)) ^ 2 / (2 * s ^ 2) = 2 * C ^ 2 * w i ^ 2 / s ^ 2 := by
    rw [mul_pow, sq_abs]; field_simp
  linarith

/-- **Prop. `prop:affine-gradient-formal`, Eq. `eq:affine-gradient-noise-formal`.**
With budgets `ρᵢ = uᵢ² > 0` and weights `w ≥ 0`, the affine release is heterogeneous
`ρ`-zCDP if and only if `s² ≥ s_w² = 2 C² (maxᵢ wᵢ/uᵢ)²`: `s_w²` is the smallest feasible
Gaussian variance. -/
theorem affineRelease_hetZCDP_iff_noise (hd : 0 < d) {C : ℝ} (hC : 0 ≤ C) (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) {s : ℝ} (hs : 0 < s) (ρ : Fin n → ℝ)
    (hρ : ∀ i, 0 < ρ i) :
    HetZCDP (affineRelease (d := d) C w s) ρ ↔
      2 * C ^ 2 * (univ.sup' ⟨⟨0, hn⟩, mem_univ _⟩ fun i ↦ w i / √(ρ i)) ^ 2 ≤ s ^ 2 := by
  rw [affineRelease_hetZCDP_iff hd hC w hs ρ]
  have key : ∀ i, 2 * C ^ 2 * w i ^ 2 / s ^ 2 ≤ ρ i ↔ 2 * C ^ 2 * (w i / √(ρ i)) ^ 2 ≤ s ^ 2 := by
    intro i
    rw [div_le_iff₀ (by positivity), div_pow, Real.sq_sqrt (hρ i).le, mul_div_assoc',
      div_le_iff₀ (hρ i), mul_comm (ρ i)]
  simp_rw [key]
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' ⟨⟨0, hn⟩, mem_univ _⟩ fun i ↦ w i / √(ρ i)
    rw [hi]; exact h i
  · intro h i
    refine le_trans ?_ h
    have h0 : 0 ≤ w i / √(ρ i) := div_nonneg (hw i) (Real.sqrt_nonneg _)
    gcongr
    exact le_sup' (fun i ↦ w i / √(ρ i)) (mem_univ i)

/-! ## Oracle MSE (Eq. `eq:affine-gradient-risk-formal`) -/

section MSE

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `E‖∑ⱼ Yⱼ‖² = ∑ⱼ E‖Yⱼ‖²` for pairwise independent, centred, square-integrable random
vectors. -/
lemma integral_norm_sq_sum_indep {J ι : Type*} [Fintype ι] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : Finset J) (Y : J → Ω → EuclideanSpace ℝ ι)
    (hY : ∀ j ∈ S, MemLp (Y j) 2 P) (h0 : ∀ j ∈ S, ∫ ω, Y j ω ∂P = 0)
    (hind : (S : Set J).Pairwise fun j l ↦ IndepFun (Y j) (Y l) P) :
    ∫ ω, ‖∑ j ∈ S, Y j ω‖ ^ 2 ∂P = ∑ j ∈ S, ∫ ω, ‖Y j ω‖ ^ 2 ∂P := by
  have hc : ∀ j ∈ S, ∀ k, MemLp (fun ω ↦ Y j ω k) 2 P := fun j hj k ↦
    (EuclideanSpace.proj k : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp_memLp' (hY j hj)
  have hc0 : ∀ j ∈ S, ∀ k, ∫ ω, Y j ω k ∂P = 0 := fun j hj k ↦ by
    have := (EuclideanSpace.proj k : EuclideanSpace ℝ ι →L[ℝ] ℝ).integral_comp_comm
      ((hY j hj).integrable one_le_two)
    exact this.trans (by rw [h0 j hj]; simp)
  have hci : ∀ k, (S : Set J).Pairwise fun j l ↦
      IndepFun (fun ω ↦ Y j ω k) (fun ω ↦ Y l ω k) P := fun k j hj l hl hjl ↦
    (hind hj hl hjl).comp (by fun_prop : Measurable fun x : EuclideanSpace ℝ ι ↦ x k)
      (by fun_prop : Measurable fun x : EuclideanSpace ℝ ι ↦ x k)
  simp_rw [EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_sum, Finset.sum_apply]
  rw [integral_finsetSum _ fun k _ ↦ (memLp_finsetSum S fun j hj ↦ hc j hj k).integrable_sq]
  rw [Finset.sum_congr rfl fun j hj ↦
    integral_finsetSum _ fun k _ ↦ (hc j hj k).integrable_sq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hvar := IndepFun.variance_sum (X := fun j ω ↦ Y j ω k) (fun j hj ↦ hc j hj k) (hci k)
  have hA : AEMeasurable (∑ j ∈ S, fun ω ↦ Y j ω k) P :=
    (memLp_finsetSum' S fun j hj ↦ hc j hj k).aemeasurable
  have hM : P[∑ j ∈ S, fun ω ↦ Y j ω k] = 0 := by
    simp_rw [Finset.sum_apply]
    rw [integral_finsetSum _ fun j hj ↦ (hc j hj k).integrable one_le_two]
    exact Finset.sum_eq_zero fun j hj ↦ hc0 j hj k
  rw [variance_of_integral_eq_zero hA hM] at hvar
  simp_rw [Finset.sum_apply] at hvar
  rw [hvar]
  exact Finset.sum_congr rfl fun j hj ↦
    variance_of_integral_eq_zero (hc j hj k).aemeasurable (hc0 j hj k)

/-- Independence is preserved by composing with a measure-preserving map. -/
lemma IndepFun.comp_measurePreserving' {Ω' β γ : Type*} [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace γ] {P : Measure Ω} {P' : Measure Ω'}
    {f : Ω → β} {g : Ω → γ} (h : IndepFun f g P) (hf : AEMeasurable f P)
    (hg : AEMeasurable g P) {T : Ω' → Ω} (hT : MeasurePreserving T P' P) :
    IndepFun (f ∘ T) (g ∘ T) P' := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro A B hA hB
  have hfA : NullMeasurableSet (f ⁻¹' A) P := hf.nullMeasurable hA
  have hgB : NullMeasurableSet (g ⁻¹' B) P := hg.nullMeasurable hB
  rw [Set.preimage_comp, Set.preimage_comp, ← Set.preimage_inter,
    hT.measure_preimage (hfA.inter hgB), hT.measure_preimage hfA, hT.measure_preimage hgB]
  exact h A B hA hB

/-- `E‖Z‖² = d s²` for `Z ∼ N(0, s² I_d)`. -/
lemma integral_norm_sq_gaussNoise (s : ℝ) :
    ∫ x, ‖x‖ ^ 2 ∂(gaussNoise (0 : EuclideanSpace ℝ (Fin d)) s) = d * s ^ 2 := by
  have hmem : ∀ k : Fin d, MemLp (fun x : EuclideanSpace ℝ (Fin d) ↦ x k) 2
      (gaussNoise 0 s) := fun k ↦
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp_memLp'
      IsGaussian.memLp_two_id
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ fun k _ ↦ (hmem k).integrable_sq]
  have hk : ∀ k : Fin d, ∫ x, (x k) ^ 2 ∂(gaussNoise (0 : EuclideanSpace ℝ (Fin d)) s)
      = s ^ 2 := by
    intro k
    have hmp := measurePreserving_eval_gaussNoise (0 : EuclideanSpace ℝ (Fin d)) s k
    rw [← integral_map hmp.measurable.aemeasurable (by fun_prop : AEStronglyMeasurable
      (fun y : ℝ ↦ y ^ 2) _), hmp.map_eq]
    have hv := variance_of_integral_eq_zero (X := id)
      (μ := gaussianReal ((0 : EuclideanSpace ℝ (Fin d)) k) (s ^ 2).toNNReal)
      aemeasurable_id (by simp [integral_id_gaussianReal])
    rw [variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg s)] at hv
    simpa using hv.symm
  simp [hk]

/-- **Eq. `eq:affine-gradient-risk-formal`, general form.**  Let `g₁, …, gₙ` be pairwise
independent square-integrable random vectors with common mean `m`, and `Z ∼ N(0, s² I_d)`
independent of each `gᵢ`.  For weights with `∑ wᵢ = 1`,
`E‖∑ wᵢ gᵢ + Z − m‖² = ∑ wᵢ² E‖gᵢ − m‖² + d s²`.  (Pairwise independence is implied by
the paper's mutual independence.) -/
theorem affine_mse_eq {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (Z : Ω → EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d)) (w : Fin n → ℝ) (hw : ∑ i, w i = 1) (s : ℝ)
    (hg : ∀ i, MemLp (g i) 2 P) (hmean : ∀ i, ∫ ω, g i ω ∂P = m)
    (hind : ∀ i j, i ≠ j → IndepFun (g i) (g j) P) (hZind : ∀ i, IndepFun (g i) Z P)
    (hZ : HasLaw Z (gaussNoise 0 s) P) :
    ∫ ω, ‖∑ i, w i • g i ω + Z ω - m‖ ^ 2 ∂P
      = ∑ i, w i ^ 2 * ∫ ω, ‖g i ω - m‖ ^ 2 ∂P + d * s ^ 2 := by
  let Y : Option (Fin n) → Ω → EuclideanSpace ℝ (Fin d) :=
    fun j ↦ Option.elim j Z (fun i ω ↦ w i • (g i ω - m))
  have hsum : ∀ ω, ∑ i, w i • g i ω + Z ω - m = ∑ j, Y j ω := by
    intro ω
    rw [Fintype.sum_option]
    simp only [Y, Option.elim]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul]
    abel
  have hφ : ∀ i, Measurable fun x : EuclideanSpace ℝ (Fin d) ↦ w i • (x - m) := fun i ↦ by
    fun_prop
  have hZm : MemLp Z 2 P := by
    have h := IsGaussian.memLp_two_id (μ := gaussNoise (0 : EuclideanSpace ℝ (Fin d)) s)
    rw [← hZ.map_eq] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hZ.aemeasurable).mp h
  simp_rw [hsum]
  rw [integral_norm_sq_sum_indep univ Y ?_ ?_ ?_, Fintype.sum_option]
  · simp only [Y, Option.elim]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      exact integral_const_mul _ _
    · have := hZ.integral_comp (f := fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2)
        (by fun_prop)
      rw [integral_norm_sq_gaussNoise] at this
      exact this
  · rintro (_ | i) -
    · exact hZm
    · exact ((hg i).sub (memLp_const m)).const_smul (w i)
  · rintro (_ | i) -
    · simp only [Y, Option.elim]
      rw [hZ.integral_eq]; simp
    · simp only [Y, Option.elim]
      rw [integral_smul, integral_sub ((hg i).integrable one_le_two) (integrable_const m),
        hmean i]
      simp
  · rintro (_ | i) - (_ | j) - hij
    · exact absurd rfl hij
    · exact (hZind j).symm.comp measurable_id (hφ j)
    · exact (hZind i).comp (hφ i) measurable_id
    · exact (hind i j fun h ↦ hij (congrArg some h)).comp (hφ i) (hφ j)

/-- Oracle MSE `E‖g̃_w(θ) − ∇F(θ)‖²` of the affine release, in the following random
model: the per-record gradients `gᵢ` are random vectors on `(Ω, P)`, the target is
`m = ∇F(θ)`, and the noise `Z ∼ N(0, s² I_d)` lives on an independent factor, i.e. the
pair `(ω, Z)` has law `P ⊗ N(0, s² I_d)`. -/
noncomputable def affineMSE (P : Measure Ω) (g : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (m : EuclideanSpace ℝ (Fin d)) (w : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∫ p, ‖∑ i, w i • g i p.1 + p.2 - m‖ ^ 2 ∂(P.prod (gaussNoise 0 s))

/-- `affineMSE` in terms of the per-record variances. -/
theorem affineMSE_eq_sum {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d))
    (hg : ∀ i, MemLp (g i) 2 P) (hmean : ∀ i, ∫ ω, g i ω ∂P = m) (hind : iIndepFun g P)
    (w : Fin n → ℝ) (hw : ∑ i, w i = 1) (s : ℝ) :
    affineMSE P g m w s = ∑ i, w i ^ 2 * ∫ ω, ‖g i ω - m‖ ^ 2 ∂P + d * s ^ 2 := by
  have mpf : MeasurePreserving Prod.fst (P.prod (gaussNoise (0 : EuclideanSpace ℝ (Fin d)) s))
      P := measurePreserving_fst
  have h := affine_mse_eq (P := P.prod (gaussNoise 0 s)) (fun i p ↦ g i p.1) Prod.snd m w hw s
    (fun i ↦ (hg i).comp_measurePreserving mpf)
    (fun i ↦ by rw [integral_fun_fst]; simp [hmean i])
    (fun i j hij ↦ Limites.IndepFun.comp_measurePreserving' (hind.indepFun hij)
      (hg i).aemeasurable (hg j).aemeasurable mpf)
    (fun i ↦ indepFun_prod₀ (hg i).aemeasurable aemeasurable_id)
    measurePreserving_snd.hasLaw
  rw [affineMSE, h]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_fun_fst (f := fun x ↦ ‖g i x - m‖ ^ 2)]
  simp

/-- **Eq. `eq:affine-gradient-risk-formal`.**  With independent per-record gradients of
common mean `m` and common variance `E‖gᵢ − m‖² = V`:
`E‖g̃_w − m‖² = V ∑ wᵢ² + d s²`. -/
theorem affineMSE_eq {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) {V : ℝ}
    (hg : ∀ i, MemLp (g i) 2 P) (hmean : ∀ i, ∫ ω, g i ω ∂P = m) (hind : iIndepFun g P)
    (hV : ∀ i, ∫ ω, ‖g i ω - m‖ ^ 2 ∂P = V)
    (w : Fin n → ℝ) (hw : ∑ i, w i = 1) (s : ℝ) :
    affineMSE P g m w s = V * ∑ i, w i ^ 2 + d * s ^ 2 := by
  rw [affineMSE_eq_sum g m hg hmean hind w hw s, Finset.mul_sum]
  simp_rw [hV, mul_comm V]

/-- **Prop. `prop:affine-gradient-formal`, variance bounded above.**  If
`E‖gᵢ − m‖² ≤ V` for every `i`, then `E‖g̃_w − m‖² ≤ V ∑ wᵢ² + d s²`. -/
theorem affineMSE_le {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) {V : ℝ}
    (hg : ∀ i, MemLp (g i) 2 P) (hmean : ∀ i, ∫ ω, g i ω ∂P = m) (hind : iIndepFun g P)
    (hV : ∀ i, ∫ ω, ‖g i ω - m‖ ^ 2 ∂P ≤ V)
    (w : Fin n → ℝ) (hw : ∑ i, w i = 1) (s : ℝ) :
    affineMSE P g m w s ≤ V * ∑ i, w i ^ 2 + d * s ^ 2 := by
  rw [affineMSE_eq_sum g m hg hmean hind w hw s, Finset.mul_sum]
  have : ∑ i, w i ^ 2 * ∫ ω, ‖g i ω - m‖ ^ 2 ∂P ≤ ∑ i, V * w i ^ 2 :=
    Finset.sum_le_sum fun i _ ↦ by
      rw [mul_comm V]; exact mul_le_mul_of_nonneg_left (hV i) (sq_nonneg _)
  linarith

/-- **Eq. `eq:affine-gradient-risk-formal` at the smallest feasible noise** `s = s_w`,
`s_w² = 2 C² (maxᵢ wᵢ/uᵢ)²`: `E‖g̃_w − m‖² = V ∑ wᵢ² + 2 d C² (maxᵢ wᵢ/uᵢ)²`. -/
theorem affineMSE_minNoise {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) {V : ℝ}
    (hg : ∀ i, MemLp (g i) 2 P) (hmean : ∀ i, ∫ ω, g i ω ∂P = m) (hind : iIndepFun g P)
    (hV : ∀ i, ∫ ω, ‖g i ω - m‖ ^ 2 ∂P = V) (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∑ i, w i = 1) (C : ℝ) (u : Fin n → ℝ) :
    affineMSE P g m w (√2 * C * univ.sup' ⟨⟨0, hn⟩, mem_univ _⟩ fun i ↦ w i / u i)
      = V * ∑ i, w i ^ 2
        + 2 * d * C ^ 2 * (univ.sup' ⟨⟨0, hn⟩, mem_univ _⟩ fun i ↦ w i / u i) ^ 2 := by
  rw [affineMSE_eq g m hg hmean hind hV w hw, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

end MSE

/-! ## Personalized oracle MSE (Def. `def:oracle-mse`, Eq. `eq:gradient-claim-form`) -/

section Pers

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `𝒱_pers(θ)` of Def. `def:oracle-mse`: the infimum of the oracle MSE `affineMSE` over
the affine releases (weights `w ≥ 0`, `∑ w = 1`, noise `s > 0`) that are heterogeneous
`ρ`-zCDP on datasets of gradients in `B_C`. -/
noncomputable def persOracleMSE (C : ℝ) (ρ : Fin n → ℝ) (P : Measure Ω)
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf {r | ∃ (w : Fin n → ℝ) (s : ℝ), (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ 0 < s ∧
    HetZCDP (affineRelease (d := d) C w s) ρ ∧ affineMSE P g m w s = r}

/-- **Prop. `prop:affine-gradient-formal`, Eq. `eq:gradient-claim-form` (first equality).**
`𝒱_pers(θ) = 𝓡_pers(u; V(θ), 2 d C²)` with `uᵢ = √ρᵢ`. -/
theorem persOracleMSE_eq (hd : 0 < d) {C : ℝ} (hC : 0 < C) (ρ : Fin n → ℝ)
    (hρ : ∀ i, 0 < ρ i) {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) {V : ℝ}
    (hg : ∀ i, MemLp (g i) 2 P) (hmean : ∀ i, ∫ ω, g i ω ∂P = m) (hind : iIndepFun g P)
    (hV : ∀ i, ∫ ω, ‖g i ω - m‖ ^ 2 ∂P = V) :
    persOracleMSE C ρ P g m = persRisk ∅ (fun i ↦ √(ρ i)) V (2 * d * C ^ 2) := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq2 : (0 : ℝ) < √2 := by positivity
  unfold persOracleMSE persRisk
  congr 1
  ext r
  constructor
  · rintro ⟨w, s, hw, hsum, hs, hpriv, rfl⟩
    rw [affineRelease_hetZCDP_iff hd hC.le w hs ρ] at hpriv
    refine ⟨w, s / (√2 * C), ⟨hw, hsum, by positivity, fun i _ ↦ ?_⟩, ?_⟩
    · have h1 := hpriv i
      rw [div_le_iff₀ (by positivity)] at h1
      have h3 : (√2 * C * w i) ^ 2 ≤ (s * √(ρ i)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, h2, Real.sq_sqrt (hρ i).le]; linarith
      have h4 := (pow_le_pow_iff_left₀ (by have := hw i; positivity) (by positivity)
        two_ne_zero).1 h3
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    · rw [affineMSE_eq g m hg hmean hind hV w hsum, persObj, div_pow, mul_pow, h2]
      field_simp
  · rintro ⟨w, M, ⟨hw, hsum, hM, hfeas⟩, rfl⟩
    have hMpos : 0 < M := by
      rcases hM.lt_or_eq with h | h
      · exact h
      · exfalso
        have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ ↦ by
          simpa [← h] using hfeas i (Finset.notMem_empty i)
        linarith
    have hs2 : (√2 * C * M) ^ 2 = 2 * C ^ 2 * M ^ 2 := by rw [mul_pow, mul_pow, h2]
    refine ⟨w, √2 * C * M, hw, hsum, by positivity,
      (affineRelease_hetZCDP_iff hd hC.le w (by positivity) ρ).2 fun i ↦ ?_, ?_⟩
    · rw [div_le_iff₀ (by positivity), hs2]
      have h1 := pow_le_pow_left₀ (hw i) (hfeas i (Finset.notMem_empty i)) 2
      rw [mul_pow, Real.sq_sqrt (hρ i).le] at h1
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * C ^ 2)]
    · rw [affineMSE_eq g m hg hmean hind hV w hsum, hs2, persObj]
      ring

end Pers

/-! ## Unique-threshold comparator (Eqs. `eq:threshold-gradient`, `eq:gradient-threshold-risk`) -/

section Thr

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Noise standard deviation of the threshold release: `s_t² = 2 C² / (t² n_t²)`. -/
noncomputable def thrNoise (C : ℝ) (u : Fin n → ℝ) (t : ℝ) : ℝ :=
  √2 * C / (t * nThr ∅ u t)

/-- Weights of the threshold release: `1/n_t` on the records with `uᵢ ≥ t`, `0` otherwise. -/
noncomputable def gradThrWeights (u : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  if t ≤ u i then ((nThr ∅ u t : ℕ) : ℝ)⁻¹ else 0

/-- The threshold release of Eq. `eq:threshold-gradient`: law of
`(1/n_t) ∑_{uᵢ ≥ t} gᵢ + Z_t`, `Z_t ∼ N(0, 2C²/(t² n_t²) I_d)`. -/
noncomputable def thrRelease (C : ℝ) (u : Fin n → ℝ) (t : ℝ) (D : Fin n → GradBall d C) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (gaussNoise 0 (thrNoise C u t)).map fun z ↦
    ((nThr ∅ u t : ℕ) : ℝ)⁻¹ • ∑ i ∈ univ.filter (fun i ↦ t ≤ u i),
      (D i : EuclideanSpace ℝ (Fin d)) + z

lemma nThr_empty (u : Fin n → ℝ) (t : ℝ) : nThr ∅ u t = #(univ.filter fun i ↦ t ≤ u i) := by
  simp [nThr]

lemma thrNoise_sq (C : ℝ) (u : Fin n → ℝ) (t : ℝ) :
    thrNoise C u t ^ 2 = 2 * C ^ 2 / (t ^ 2 * (nThr ∅ u t : ℝ) ^ 2) := by
  rw [thrNoise, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]

lemma thrNoise_pos {C : ℝ} (hC : 0 < C) (u : Fin n → ℝ) {t : ℝ} (ht : 0 < t)
    (hN : 0 < nThr ∅ u t) : 0 < thrNoise C u t := by
  have : (0 : ℝ) < nThr ∅ u t := by exact_mod_cast hN
  unfold thrNoise; positivity

lemma sum_gradThrWeights_smul {E : Type*} [AddCommGroup E] [Module ℝ E] (u : Fin n → ℝ) (t : ℝ)
    (x : Fin n → E) :
    ∑ i, gradThrWeights u t i • x i
      = ((nThr ∅ u t : ℕ) : ℝ)⁻¹ • ∑ i ∈ univ.filter (fun i ↦ t ≤ u i), x i := by
  rw [Finset.smul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold gradThrWeights
  split_ifs <;> simp

lemma thrRelease_eq_affine (C : ℝ) (u : Fin n → ℝ) (t : ℝ) :
    thrRelease (d := d) C u t = affineRelease C (gradThrWeights u t) (thrNoise C u t) := by
  funext D
  unfold thrRelease affineRelease
  simp_rw [sum_gradThrWeights_smul]

lemma sum_gradThrWeights (u : Fin n → ℝ) {t : ℝ} (hN : 0 < nThr ∅ u t) :
    ∑ i, gradThrWeights u t i = 1 := by
  have := sum_gradThrWeights_smul u t (fun _ ↦ (1 : ℝ))
  simp only [smul_eq_mul, mul_one, Finset.sum_const, nsmul_eq_mul] at this
  rw [this, ← nThr_empty]
  have : (0 : ℝ) < nThr ∅ u t := by exact_mod_cast hN
  field_simp

lemma sum_gradThrWeights_sq (u : Fin n → ℝ) (t : ℝ) :
    ∑ i, gradThrWeights u t i ^ 2 = ((nThr ∅ u t : ℕ) : ℝ)⁻¹ := by
  have h : ∀ i, gradThrWeights u t i ^ 2
      = (if t ≤ u i then 1 else 0) * ((nThr ∅ u t : ℕ) : ℝ)⁻¹ ^ 2 := by
    intro i; unfold gradThrWeights; split_ifs <;> simp
  simp_rw [h]
  rw [← Finset.sum_mul, Finset.sum_boole, ← nThr_empty]
  rcases Nat.eq_zero_or_pos (nThr ∅ u t) with h0 | h0
  · simp [h0]
  · have : (0 : ℝ) < nThr ∅ u t := by exact_mod_cast h0
    field_simp

/-- **Eq. `eq:threshold-gradient`: privacy.**  For every `t > 0` with `n_t ≥ 1`, the
threshold release is heterogeneous `ρ`-zCDP for the budgets `ρᵢ ≥ 0` (`uᵢ = √ρᵢ`). -/
theorem thrRelease_hetZCDP {C : ℝ} (hC : 0 < C) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    {t : ℝ} (ht : 0 < t) (hN : 0 < nThr ∅ (fun i ↦ √(ρ i)) t) :
    HetZCDP (thrRelease (d := d) C (fun i ↦ √(ρ i)) t) ρ := by
  rw [thrRelease_eq_affine]
  refine affineRelease_hetZCDP_of _ (thrNoise_pos hC _ ht hN) ρ fun i ↦ ?_
  have hN' : (0 : ℝ) < nThr ∅ (fun i ↦ √(ρ i)) t := by exact_mod_cast hN
  rw [thrNoise_sq]
  unfold gradThrWeights
  split_ifs with hi
  · have : t ^ 2 ≤ ρ i := by
      have := pow_le_pow_left₀ ht.le hi 2
      rwa [Real.sq_sqrt (hρ i)] at this
    calc _ = t ^ 2 := by field_simp
      _ ≤ ρ i := this
  · simp [hρ i]

/-- Oracle MSE of the threshold release in the random model of `affineMSE`. -/
noncomputable def thrMSE (C : ℝ) (u : Fin n → ℝ) (t : ℝ) (P : Measure Ω)
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ p, ‖((nThr ∅ u t : ℕ) : ℝ)⁻¹ • ∑ i ∈ univ.filter (fun i ↦ t ≤ u i), g i p.1 + p.2 - m‖ ^ 2
    ∂(P.prod (gaussNoise 0 (thrNoise C u t)))

/-- **Eq. `eq:gradient-threshold-risk`, one threshold.**  For `t > 0` with `n_t ≥ 1`, the MSE
of the threshold release is `V/n_t + 2 d C² / (t n_t)²`. -/
theorem thrMSE_eq (C : ℝ) (u : Fin n → ℝ) {t : ℝ} (hN : 0 < nThr ∅ u t)
    {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) {V : ℝ}
    (hg : ∀ i, MemLp (g i) 2 P) (hmean : ∀ i, ∫ ω, g i ω ∂P = m) (hind : iIndepFun g P)
    (hV : ∀ i, ∫ ω, ‖g i ω - m‖ ^ 2 ∂P = V) :
    thrMSE C u t P g m = thrObj V (2 * d * C ^ 2) t (nThr ∅ u t) := by
  have h : thrMSE C u t P g m = affineMSE P g m (gradThrWeights u t) (thrNoise C u t) := by
    unfold thrMSE affineMSE
    simp_rw [sum_gradThrWeights_smul]
  rw [h, affineMSE_eq g m hg hmean hind hV _ (sum_gradThrWeights u hN), sum_gradThrWeights_sq,
    thrNoise_sq, thrObj]
  ring

/-- `𝒱_thr(θ)` of Def. `def:oracle-mse`: the infimum over thresholds `t > 0` with
`n_t ≥ 1` of the threshold-release MSE. -/
noncomputable def thrOracleMSE (C : ℝ) (u : Fin n → ℝ) (P : Measure Ω)
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf {r | ∃ t, 0 < t ∧ 0 < nThr ∅ u t ∧ thrMSE C u t P g m = r}

/-- **Eq. `eq:gradient-threshold-risk`.**  `𝒱_thr(θ) = 𝓡_thr(u; V(θ), 2 d C²)`. -/
theorem thrOracleMSE_eq (C : ℝ) (u : Fin n → ℝ) {P : Measure Ω} [IsProbabilityMeasure P]
    (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (m : EuclideanSpace ℝ (Fin d)) {V : ℝ}
    (hg : ∀ i, MemLp (g i) 2 P) (hmean : ∀ i, ∫ ω, g i ω ∂P = m) (hind : iIndepFun g P)
    (hV : ∀ i, ∫ ω, ‖g i ω - m‖ ^ 2 ∂P = V) :
    thrOracleMSE C u P g m = thrRisk ∅ u V (2 * d * C ^ 2) := by
  unfold thrOracleMSE thrRisk
  congr 1
  ext r
  constructor
  · rintro ⟨t, ht, hN, rfl⟩
    exact ⟨t, ht, hN, (thrMSE_eq C u hN g m hg hmean hind hV).symm⟩
  · rintro ⟨t, ht, hN, rfl⟩
    exact ⟨t, ht, hN, thrMSE_eq C u hN g m hg hmean hind hV⟩

end Thr

end Limites
