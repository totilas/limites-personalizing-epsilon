import Mathlib
import LimitesProofs.Privacy.Defs

/-!
# Rényi divergence, zCDP and the Gaussian mechanism

Supporting file for Section `sec:affine-private-gradients` (Prop.
`prop:affine-gradient-formal`) and the remark after Lemma `lem:preprocessing`.

* `renyiDiv α P Q` — Rényi divergence `D_α(P‖Q) = (α-1)⁻¹ log ∫ (dP/dQ)^α dQ`
  (`+∞` if `P` is not absolutely continuous w.r.t. `Q`), valued in `EReal`.
* `ZCDP Adj M ρ`, `HetZCDP M ρ` — (heterogeneous) zero-concentrated DP:
  `D_α(M(D)‖M(D')) ≤ ρᵢ α` for all `α > 1` and all `D, D'` differing only in record `i`.
* `gaussNoise a s` — `N(a, s² I)` on `EuclideanSpace ℝ ι` (Mathlib's
  `multivariateGaussian a (s² • 1)`).
* `renyiDiv_gaussNoise` — `D_α(N(a, s²I) ‖ N(b, s²I)) = α ‖a − b‖² / (2 s²)`.
* `gaussMech_zCDP_iff`, `gaussMech_zCDP`, `gaussMech_hetZCDP` — the Gaussian mechanism
  with `ℓ₂`-sensitivity `Δ` is `Δ²/(2s²)`-zCDP (Bun–Steinke), with the exact
  characterisation of its zCDP budgets.
* `hetZCDP_preprocess` — remark after Lemma `lem:preprocessing` ("the same argument
  applies verbatim to zCDP budgets"): per-record preprocessing preserves heterogeneous zCDP.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace Limites

section PiDensity

variable {ι : Type*} [Fintype ι]

/-- Lebesgue integral of a product of coordinate functions under a product of
probability measures. -/
lemma lintegral_pi_prod {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (i : ι) → Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  have hind : iIndepFun (fun i (x : (i : ι) → Ω i) ↦ f i (x i)) (Measure.pi μ) :=
    iIndepFun_pi (X := f) (fun i ↦ (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i ↦ (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  exact (measurePreserving_eval μ i).lintegral_comp (hf i)

/-- A product of measures with densities has the product density. -/
lemma pi_eq_withDensity {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ ν : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)]
    (f : (i : ι) → Ω i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (h : ∀ i, ν i = (μ i).withDensity (f i)) :
    Measure.pi ν = (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have : (Set.univ.pi s).indicator (fun x ↦ ∏ i, f i (x i))
      = fun x ↦ ∏ i, (s i).indicator (f i) (x i) := by
    ext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  rw [this, lintegral_pi_prod μ _ (fun i ↦ (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [h i, withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end PiDensity

/-! ## Rényi divergence and zCDP -/

section Renyi

variable {Ω : Type*} [MeasurableSpace Ω]

open Classical in
/-- Rényi divergence of order `α > 1`:
`D_α(P‖Q) = (α - 1)⁻¹ log ∫ (dP/dQ)^α dQ` if `P ≪ Q`, and `+∞` otherwise.
`P.rnDeriv Q` is the Radon–Nikodym derivative `dP/dQ`; the logarithm is the extended
logarithm `[0, ∞] → [-∞, ∞]`, so an infinite integral gives `D_α = +∞`. -/
noncomputable def renyiDiv (α : ℝ) (P Q : Measure Ω) : EReal :=
  if P ≪ Q then (((α - 1)⁻¹ : ℝ) : EReal) * ENNReal.log (∫⁻ x, P.rnDeriv Q x ^ α ∂Q) else ⊤

/-- `ρ`-zCDP for a neighbouring relation `Adj`: `D_α(M(D)‖M(D')) ≤ ρ α` for all `α > 1`
and all `Adj D D'`. -/
def ZCDP {Data Y : Type*} [MeasurableSpace Y] (Adj : Data → Data → Prop)
    (M : Data → Measure Y) (ρ : ℝ) : Prop :=
  ∀ D D', Adj D D' → ∀ α : ℝ, 1 < α → renyiDiv α (M D) (M D') ≤ ((ρ * α : ℝ) : EReal)

/-- **Heterogeneous zCDP.**  `M` is `ρᵢ`-zCDP with respect to record `i`, for every `i`:
`D_α(M(D)‖M(D')) ≤ ρᵢ α` for all `α > 1` and all `D, D'` differing only in record `i`. -/
def HetZCDP {n : ℕ} {X Y : Type*} [MeasurableSpace Y] (M : (Fin n → X) → Measure Y)
    (ρ : Fin n → ℝ) : Prop :=
  ∀ i, ZCDP (NeighborAt i) M (ρ i)

/-- Rényi divergence of a measure given by an explicit density. -/
lemma renyiDiv_withDensity (Q : Measure Ω) [SigmaFinite Q] {g : Ω → ℝ≥0∞}
    (hg : Measurable g) {α y : ℝ} (hα : 1 < α)
    (h : ∫⁻ x, g x ^ α ∂Q = ENNReal.ofReal (Real.exp y)) :
    renyiDiv α (Q.withDensity g) Q = ((y / (α - 1) : ℝ) : EReal) := by
  rw [renyiDiv, if_pos (withDensity_absolutelyContinuous Q g),
    lintegral_congr_ae ((Measure.rnDeriv_withDensity Q hg).mono fun x hx ↦ by rw [hx]), h,
    ENNReal.log_ofReal_of_pos (Real.exp_pos y), Real.log_exp, ← EReal.coe_mul]
  congr 1
  have : α - 1 ≠ 0 := by linarith
  field_simp

/-- Pushing a measure with density through a measurable equivalence. -/
lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

end Renyi

/-! ## One-dimensional Gaussian density ratios -/

section Gauss1

/-- Exponent of the density ratio `dN(a, v)/dN(b, v)`. -/
noncomputable def gaussExp (a b : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  ((x - b) * (a - b) - (a - b) ^ 2 / 2) / v

lemma measurable_gaussExp (a b : ℝ) (v : ℝ≥0) : Measurable (gaussExp a b v) := by
  unfold gaussExp; fun_prop

lemma gaussianPDFReal_ratio (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal a v x = gaussianPDFReal b v x * Real.exp (gaussExp a b v x) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  simp only [gaussianPDFReal, gaussExp, mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

lemma gaussianPDFReal_ratio_rpow (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (α x : ℝ) :
    gaussianPDFReal b v x * Real.exp (α * gaussExp a b v x)
      = Real.exp (α * (α - 1) * (a - b) ^ 2 / (2 * v))
        * gaussianPDFReal (b + α * (a - b)) v x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  simp only [gaussianPDFReal, gaussExp]
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- `N(a, v) = N(b, v).withDensity (exp ∘ gaussExp a b v)`. -/
lemma gaussianReal_eq_withDensity (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal a v = (gaussianReal b v).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (gaussExp a b v x))) := by
  have hm : Measurable fun x ↦ ENNReal.ofReal (Real.exp (gaussExp a b v x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_gaussExp a b v))
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul _ (measurable_gaussianPDF _ _) hm]
  congr 1
  ext x
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_ratio a b hv]

lemma lintegral_gaussExp_rpow (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ} (hα : 0 ≤ α) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (gaussExp a b v x)) ^ α ∂(gaussianReal b v)
      = ENNReal.ofReal (Real.exp (α * (α - 1) * (a - b) ^ 2 / (2 * v))) := by
  have hpt : ∀ x, ENNReal.ofReal (Real.exp (gaussExp a b v x)) ^ α
      = ENNReal.ofReal (Real.exp (α * gaussExp a b v x)) := fun x ↦ by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hα, ← Real.exp_mul, mul_comm]
  simp_rw [hpt]
  have hm : Measurable fun x ↦ ENNReal.ofReal (Real.exp (α * gaussExp a b v x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_gaussExp a b v).const_mul α))
  rw [gaussianReal_of_var_ne_zero _ hv, lintegral_withDensity_eq_lintegral_mul _
    (measurable_gaussianPDF _ _) hm]
  simp only [Pi.mul_apply, gaussianPDF]
  simp_rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal_ratio_rpow a b hv, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_gaussianPDFReal_eq_one _ hv, mul_one]

end Gauss1

/-! ## Isotropic Gaussians on `EuclideanSpace ℝ ι` -/

section GaussD

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma posSemidef_sq_smul_one (s : ℝ) : (s ^ 2 • (1 : Matrix ι ι ℝ)).PosSemidef :=
  Matrix.PosSemidef.one.smul (sq_nonneg s)

/-- The Gaussian `N(a, s² I)` on `EuclideanSpace ℝ ι`, as Mathlib's multivariate
Gaussian with mean `a` and covariance matrix `s² I`. -/
noncomputable def gaussNoise (a : EuclideanSpace ℝ ι) (s : ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian a (s ^ 2 • (1 : Matrix ι ι ℝ))

instance (a : EuclideanSpace ℝ ι) (s : ℝ) : IsGaussian (gaussNoise a s) := by
  unfold gaussNoise; infer_instance

@[simp]
lemma integral_id_gaussNoise (a : EuclideanSpace ℝ ι) (s : ℝ) :
    ∫ x, x ∂(gaussNoise a s) = a :=
  integral_id_multivariateGaussian

/-- Each coordinate of `N(a, s² I)` is `N(aₖ, s²)`. -/
lemma measurePreserving_eval_gaussNoise (a : EuclideanSpace ℝ ι) (s : ℝ) (k : ι) :
    MeasurePreserving (fun x : EuclideanSpace ℝ ι ↦ x k) (gaussNoise a s)
      (gaussianReal (a k) (s ^ 2).toNNReal) := by
  have := measurePreserving_eval_multivariateGaussian (μ := a) (posSemidef_sq_smul_one s) (i := k)
  simpa [gaussNoise] using this


/-- `N(a, s² I)` is the law of a vector with independent `N(aᵢ, s²)` coordinates. -/
lemma gaussNoise_eq_map_pi (a : EuclideanSpace ℝ ι) (s : ℝ) :
    gaussNoise a s
      = (Measure.pi fun i ↦ gaussianReal (a i) (s ^ 2).toNNReal).map (WithLp.toLp 2) := by
  apply Measure.ext_of_charFun
  ext t
  rw [gaussNoise, charFun_multivariateGaussian (posSemidef_sq_smul_one s), charFun_pi]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, Matrix.smul_mulVec, dotProduct]
  simp only [RCLike.inner_apply, ringHom_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow,
    Real.coe_toNNReal _ (sq_nonneg s), Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- `N(a, s² I) = N(b, s² I).withDensity (dN(a)/dN(b))`, with the explicit density
`x ↦ ∏ᵢ exp(gaussExp (aᵢ) (bᵢ) s² (xᵢ))`. -/
lemma gaussNoise_eq_withDensity (a b : EuclideanSpace ℝ ι) {s : ℝ} (hs : s ≠ 0) :
    gaussNoise a s = (gaussNoise b s).withDensity
      (fun x ↦ ∏ i, ENNReal.ofReal (Real.exp (gaussExp (a i) (b i) (s ^ 2).toNNReal (x i)))) := by
  have hv : (s ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hm : ∀ i, Measurable fun y ↦
      ENNReal.ofReal (Real.exp (gaussExp (a i) (b i) (s ^ 2).toNNReal y)) := fun i ↦
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_gaussExp _ _ _))
  have hG : Measurable fun x : ι → ℝ ↦
      ∏ i, ENNReal.ofReal (Real.exp (gaussExp (a i) (b i) (s ^ 2).toNNReal (x i))) :=
    Finset.measurable_prod _ fun i _ ↦ (hm i).comp (measurable_pi_apply i)
  rw [gaussNoise_eq_map_pi, gaussNoise_eq_map_pi,
    pi_eq_withDensity (fun i ↦ gaussianReal (b i) (s ^ 2).toNNReal) _ _ hm
      (fun i ↦ gaussianReal_eq_withDensity _ _ hv),
    ← MeasurableEquiv.coe_toLp, map_withDensity_equiv _ _ hG]
  rfl

/-- **Rényi divergence between isotropic Gaussians.**
`D_α(N(a, s² I) ‖ N(b, s² I)) = α ‖a − b‖² / (2 s²)` for every `α > 1` and `s ≠ 0`. -/
theorem renyiDiv_gaussNoise (a b : EuclideanSpace ℝ ι) {s : ℝ} (hs : s ≠ 0) {α : ℝ}
    (hα : 1 < α) :
    renyiDiv α (gaussNoise a s) (gaussNoise b s)
      = ((α * ‖a - b‖ ^ 2 / (2 * s ^ 2) : ℝ) : EReal) := by
  have hv : (s ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hvs : ((s ^ 2).toNNReal : ℝ) = s ^ 2 := Real.coe_toNNReal _ (sq_nonneg s)
  have hm : ∀ i, Measurable fun y ↦
      ENNReal.ofReal (Real.exp (gaussExp (a i) (b i) (s ^ 2).toNNReal y)) := fun i ↦
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_gaussExp _ _ _))
  have hpow : ∀ x : ι → ℝ,
      (∏ i, ENNReal.ofReal (Real.exp (gaussExp (a i) (b i) (s ^ 2).toNNReal (x i)))) ^ α
        = ∏ i, ENNReal.ofReal (Real.exp (gaussExp (a i) (b i) (s ^ 2).toNNReal (x i))) ^ α := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_pos _).le),
      ENNReal.ofReal_rpow_of_nonneg (Finset.prod_nonneg fun i _ ↦ (Real.exp_pos _).le)
        (by linarith),
      ← Real.finsetProd_rpow _ _ (fun i _ ↦ (Real.exp_pos _).le),
      ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ Real.rpow_nonneg (Real.exp_pos _).le _)]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith)]
  have hG : Measurable fun x : EuclideanSpace ℝ ι ↦
      ∏ i, ENNReal.ofReal (Real.exp (gaussExp (a i) (b i) (s ^ 2).toNNReal (x i))) :=
    Finset.measurable_prod _ fun i _ ↦ (hm i).comp (by fun_prop)
  rw [gaussNoise_eq_withDensity a b hs]
  rw [renyiDiv_withDensity _ hG hα (y := α * (α - 1) * ‖a - b‖ ^ 2 / (2 * s ^ 2))]
  · congr 1
    have : α - 1 ≠ 0 := by linarith
    field_simp
  · rw [gaussNoise_eq_map_pi, ← MeasurableEquiv.coe_toLp, lintegral_map_equiv]
    simp only [MeasurableEquiv.toLp_apply, WithLp.ofLp_toLp]
    simp_rw [hpow]
    rw [lintegral_pi_prod _ _ (fun i ↦ (hm i).pow_const α)]
    simp_rw [lintegral_gaussExp_rpow _ _ hv (by linarith : (0:ℝ) ≤ α)]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_pos _).le), ← Real.exp_sum,
      EuclideanSpace.real_norm_sq_eq, hvs, Finset.mul_sum, Finset.sum_div]
    simp

/-- Translating `N(a, s² I)` by `m` gives `N(m + a, s² I)`: the law of `m + Z` for
`Z ∼ N(a, s² I)`. -/
lemma gaussNoise_map_const_add (m a : EuclideanSpace ℝ ι) (s : ℝ) :
    (gaussNoise a s).map (fun z ↦ m + z) = gaussNoise (m + a) s := by
  rw [gaussNoise, multivariateGaussian, Measure.map_map (measurable_const_add m) (by fun_prop),
    gaussNoise, multivariateGaussian]
  congr 1
  ext1 x
  simp [add_assoc]

/-- The Gaussian mechanism `D ↦ N(f D, s² I)` is `ρ`-zCDP for `Adj` exactly when
`‖f D − f D'‖² / (2 s²) ≤ ρ` for all `Adj D D'`. -/
theorem gaussMech_zCDP_iff {Data : Type*} (Adj : Data → Data → Prop)
    (f : Data → EuclideanSpace ℝ ι) {s : ℝ} (hs : s ≠ 0) (ρ : ℝ) :
    ZCDP Adj (fun D ↦ gaussNoise (f D) s) ρ ↔
      ∀ D D', Adj D D' → ‖f D - f D'‖ ^ 2 / (2 * s ^ 2) ≤ ρ := by
  constructor
  · intro h D D' hD
    have h2 := h D D' hD 2 one_lt_two
    rw [renyiDiv_gaussNoise _ _ hs one_lt_two, EReal.coe_le_coe_iff] at h2
    have : 2 * ‖f D - f D'‖ ^ 2 / (2 * s ^ 2) = 2 * (‖f D - f D'‖ ^ 2 / (2 * s ^ 2)) := by
      ring
    linarith
  · intro h D D' hD α hα
    rw [renyiDiv_gaussNoise _ _ hs hα, EReal.coe_le_coe_iff]
    have := h D D' hD
    have : α * ‖f D - f D'‖ ^ 2 / (2 * s ^ 2) = α * (‖f D - f D'‖ ^ 2 / (2 * s ^ 2)) := by
      ring
    rw [this, mul_comm ρ]
    exact mul_le_mul_of_nonneg_left (h D D' hD) (by linarith)

/-- **Gaussian mechanism** (Bun–Steinke): a query with `ℓ₂`-sensitivity `Δ` released
with noise `N(0, s² I)` is `Δ² / (2 s²)`-zCDP. -/
theorem gaussMech_zCDP {Data : Type*} (Adj : Data → Data → Prop)
    (f : Data → EuclideanSpace ℝ ι) {s : ℝ} (hs : s ≠ 0) {Δ : ℝ}
    (hΔ : ∀ D D', Adj D D' → ‖f D - f D'‖ ≤ Δ) :
    ZCDP Adj (fun D ↦ gaussNoise (f D) s) (Δ ^ 2 / (2 * s ^ 2)) := by
  refine (gaussMech_zCDP_iff Adj f hs _).2 fun D D' hD ↦ ?_
  gcongr
  exact hΔ D D' hD

/-- Heterogeneous version: per-record sensitivities `Δᵢ` give budgets `Δᵢ² / (2 s²)`. -/
theorem gaussMech_hetZCDP {n : ℕ} {X : Type*} (f : (Fin n → X) → EuclideanSpace ℝ ι)
    {s : ℝ} (hs : s ≠ 0) {Δ : Fin n → ℝ}
    (hΔ : ∀ i D D', NeighborAt i D D' → ‖f D - f D'‖ ≤ Δ i) :
    HetZCDP (fun D ↦ gaussNoise (f D) s) (fun i ↦ Δ i ^ 2 / (2 * s ^ 2)) :=
  fun i ↦ gaussMech_zCDP _ f hs (hΔ i)

end GaussD

/-! ## Per-record preprocessing -/

/-- **Remark after Lemma `lem:preprocessing`** (zCDP version): if `M'` is heterogeneous
`ρ`-zCDP on datasets `(y₁, …, yₙ)`, then `D ↦ M'(φ₁(z₁), …, φₙ(zₙ))` is heterogeneous
`ρ`-zCDP on datasets `(z₁, …, zₙ)`.  No measurability of the `φᵢ` is needed. -/
theorem hetZCDP_preprocess {n : ℕ} {Z X Y : Type*} [MeasurableSpace Y]
    {M' : (Fin n → X) → Measure Y} {ρ : Fin n → ℝ} (h : HetZCDP M' ρ)
    (φ : Fin n → Z → X) :
    HetZCDP (fun D ↦ M' (fun i ↦ φ i (D i))) ρ := by
  intro i D D' hD α hα
  exact h i _ _ (fun j hj ↦ by simp only [hD j hj]) α hα

end Limites
