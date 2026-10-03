import Mathlib
import LimitesProofs.Privacy.Defs

/-!
# Arbitrary personalized DP, preprocessing, and the one-step equivalence

Paper result ↔ Lean name:

* Definition "Arbitrary Personalized DP" (`main_SATML.tex`, Preliminaries) ↔
  `Limites.ArbitraryPersonalizedDP`.
* Folklore result (Nissim–Vadhan–Xiao): any arbitrary personalized DP mechanism is
  `(2ε*, (1 + e^{ε*}) δ*)`-DP ↔ `Limites.ArbitraryPersonalizedDP.approxDP`
  (and `Limites.ArbitraryPersonalizedDP.approxDP_of_isLeast` for the "minimum budget" form).
* Lemma `lem:preprocessing` ↔ `Limites.HetDP.comp_preprocess`.
* Remark `rem:one-step-equivalence` / Eq. `eq:one-step-minimax` (`applearning.tex`):
  - the minimax one-step risk `ν_ℓ(θ)` ↔ `Limites.oneStepMinimaxRisk`;
  - the heterogeneous mean-estimation minimax risk `ν*(C)` ↔ `Limites.meanEstMinimaxRisk`;
  - Part 1 (`ν_ℓ(θ) ≤ ν*(C)`) ↔ `Limites.oneStepMinimaxRisk_le_meanEstMinimaxRisk`;
  - the linear family has gradient `z` ↔ `Limites.hasGradientAt_linearLoss`;
  - Part 2 (equality for the linear family) ↔ `Limites.oneStepMinimaxRisk_linear`;
  - `sup_ℓ ν_ℓ(θ) = ν*(C)` ↔ `Limites.isGreatest_oneStepMinimaxRisk`,
    `Limites.sSup_oneStepMinimaxRisk`.

## Formal model for the remark

* The output / gradient space is `EuclideanSpace ℝ (Fin d)`; `B_C = Metric.closedBall 0 C`.
* A mechanism on datasets `Fin n → Z` is a map `M : (Fin n → Z) → Measure (ℝ^d)` that is a
  measurable map into the Giry space (i.e. a Markov kernel), with `M D` a probability measure for
  every `D`, and heterogeneous `ε`-DP (`HetDP`).  This class is `HetDPMechanisms n d Z ε`.
  Kernel measurability is the standard measurability condition left implicit in the paper; it is
  needed for `E_{z ~ Pⁿ}[·]` of the inner expectation to be well behaved.
* Risks are `lintegral`s in `ℝ≥0∞` (`mseRisk`), so no integrability side conditions are needed.
* Only `∇ℓ(θ; ·)` enters `ν_ℓ(θ)`, so a loss family at the fixed `θ` is represented directly by
  its gradient map `g : Z → ℝ^d` (measurable, with `‖g z‖ ≤ C`), and
  `∇F(θ) = E_P[g z]` is a Bochner integral.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace Limites

/-! ## Arbitrary personalized DP and the folklore result -/

/-- **Definition (Arbitrary Personalized DP).**  Records are triples `(x, ε, δ)` drawn from a
record domain `R ⊆ X × ℝ × ℝ`; for datasets differing (arbitrarily) in record `i`, where
`(x, ε, δ)` becomes `(x', ε', δ')`,
`Pr(M(D) ∈ S) ≤ e^{min(ε, ε')} Pr(M(D') ∈ S) + min(δ, δ')`. -/
def ArbitraryPersonalizedDP {n : ℕ} {X Y : Type*} [MeasurableSpace Y] {R : Set (X × ℝ × ℝ)}
    (M : (Fin n → R) → Measure Y) : Prop :=
  ∀ i D D', NeighborAt i D D' → ∀ S, MeasurableSet S →
    M D S ≤ ENNReal.ofReal (Real.exp (min (D i).1.2.1 (D' i).1.2.1)) * M D' S
      + ENNReal.ofReal (min (D i).1.2.2 (D' i).1.2.2)

/-- **Folklore result (Nissim–Vadhan–Xiao).**  If the record domain contains some record
`(x₀, ε₀, δ₀)`, then every arbitrary personalized DP mechanism is
`(2ε₀, (1 + e^{ε₀}) δ₀)`-DP for the "differ in one record" relation.  In the paper `ε₀ = ε*`,
`δ₀ = δ*` are the minimal budgets; the proof only uses that a record carrying them exists (see
`approxDP_of_isLeast`), so no minimality hypothesis is needed here. -/
theorem ArbitraryPersonalizedDP.approxDP {n : ℕ} {X Y : Type*} [MeasurableSpace Y]
    {R : Set (X × ℝ × ℝ)} {M : (Fin n → R) → Measure Y} (hM : ArbitraryPersonalizedDP M)
    {x₀ : X} {ε₀ δ₀ : ℝ} (h₀ : (x₀, ε₀, δ₀) ∈ R) :
    ApproxDP Neighbor M (2 * ε₀) ((1 + Real.exp ε₀) * δ₀) := by
  rintro D D' ⟨i, hi⟩ S hS
  set r₀ : R := ⟨(x₀, ε₀, δ₀), h₀⟩
  set D'' := Function.update D i r₀
  have h1 : NeighborAt i D D'' := fun j hj => (Function.update_of_ne hj _ _).symm
  have h2 : NeighborAt i D'' D' := fun j hj => by
    simp only [D'', Function.update_of_ne hj]; exact hi j hj
  have hD''i : D'' i = r₀ := Function.update_self _ _ _
  -- the two inequalities through the intermediate dataset `D''`
  have e1 : M D S ≤ ENNReal.ofReal (Real.exp ε₀) * M D'' S + ENNReal.ofReal δ₀ := by
    refine (hM i D D'' h1 S hS).trans ?_
    rw [hD''i]
    gcongr
    · exact min_le_right _ _
    · exact min_le_right _ _
  have e2 : M D'' S ≤ ENNReal.ofReal (Real.exp ε₀) * M D' S + ENNReal.ofReal δ₀ := by
    refine (hM i D'' D' h2 S hS).trans ?_
    rw [hD''i]
    gcongr
    · exact min_le_left _ _
    · exact min_le_left _ _
  have hexp : ENNReal.ofReal (Real.exp (2 * ε₀))
      = ENNReal.ofReal (Real.exp ε₀) * ENNReal.ofReal (Real.exp ε₀) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, two_mul]
  have hdelta : ENNReal.ofReal ((1 + Real.exp ε₀) * δ₀)
      = ENNReal.ofReal (Real.exp ε₀) * ENNReal.ofReal δ₀ + ENNReal.ofReal δ₀ := by
    rcases le_or_gt δ₀ 0 with h | h
    · have : (1 + Real.exp ε₀) * δ₀ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      simp [ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_of_nonpos this]
    · rw [add_mul, one_mul, add_comm, ENNReal.ofReal_add (by positivity) h.le,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc M D S ≤ ENNReal.ofReal (Real.exp ε₀) * M D'' S + ENNReal.ofReal δ₀ := e1
    _ ≤ ENNReal.ofReal (Real.exp ε₀) *
          (ENNReal.ofReal (Real.exp ε₀) * M D' S + ENNReal.ofReal δ₀) + ENNReal.ofReal δ₀ := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (2 * ε₀)) * M D' S
          + ENNReal.ofReal ((1 + Real.exp ε₀) * δ₀) := by
        rw [hexp, hdelta, mul_add, mul_assoc, add_assoc]

/-- **Folklore result, minimum-budget form.**  If `ε*` (resp. `δ*`) is the smallest privacy
parameter in the record domain and both are carried by a common record `(x₀, ε*, δ*)`, every
arbitrary personalized DP mechanism is `(2ε*, (1 + e^{ε*}) δ*)`-DP.  (The minimality hypotheses
are not used: this is a special case of `approxDP`.) -/
theorem ArbitraryPersonalizedDP.approxDP_of_isLeast {n : ℕ} {X Y : Type*} [MeasurableSpace Y]
    {R : Set (X × ℝ × ℝ)} {M : (Fin n → R) → Measure Y} (hM : ArbitraryPersonalizedDP M)
    {x₀ : X} {εs δs : ℝ} (h₀ : (x₀, εs, δs) ∈ R)
    (_hε : IsLeast ((fun r => r.2.1) '' R) εs) (_hδ : IsLeast ((fun r => r.2.2) '' R) δs) :
    ApproxDP Neighbor M (2 * εs) ((1 + Real.exp εs) * δs) :=
  hM.approxDP h₀

/-! ## Lemma `lem:preprocessing` -/

/-- **Lemma `lem:preprocessing` (per-record preprocessing preserves heterogeneous DP).**
If `M'` is heterogeneous `ε`-DP on datasets `(y₁, …, yₙ)`, then
`M(z₁, …, zₙ) = M'(φ₁(z₁), …, φₙ(zₙ))` is heterogeneous `ε`-DP on datasets `(z₁, …, zₙ)`.
No measurability of the `φᵢ` is needed for this statement. -/
theorem HetDP.comp_preprocess {n : ℕ} {Z Y' Y : Type*} [MeasurableSpace Y]
    {M' : (Fin n → Y') → Measure Y} {ε : Fin n → ℝ} (hM' : HetDP M' ε) (φ : Fin n → Z → Y') :
    HetDP (fun D => M' (fun i => φ i (D i))) ε := by
  intro i D D' h S hS
  -- the images of `i`-neighbours are `i`-neighbours (possibly equal)
  exact hM' i _ _ (fun j hj => by simp only [h j hj]) S hS

/-! ## Remark `rem:one-step-equivalence` -/

section OneStep

variable {n d : ℕ}

/-- The class of heterogeneous `ε`-DP mechanisms on datasets `Fin n → Z` with outputs in `ℝ^d`:
measurable (Markov kernels), probability-valued, and `HetDP`. -/
def HetDPMechanisms (n d : ℕ) (Z : Type*) [MeasurableSpace Z] (ε : Fin n → ℝ) :
    Set ((Fin n → Z) → Measure (EuclideanSpace ℝ (Fin d))) :=
  {M | Measurable M ∧ (∀ D, IsProbabilityMeasure (M D)) ∧ HetDP M ε}

/-- Mean-squared error `E_{z₁..ₙ ~ Pⁿ i.i.d.} E_{y ~ M(z)} ‖y − m‖²`, valued in `ℝ≥0∞`. -/
noncomputable def mseRisk {Z : Type*} [MeasurableSpace Z]
    (M : (Fin n → Z) → Measure (EuclideanSpace ℝ (Fin d))) (P : Measure Z)
    (m : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ D, ∫⁻ y, ‖y - m‖ₑ ^ 2 ∂(M D) ∂(Measure.pi fun _ : Fin n => P)

/-- **`ν_ℓ(θ)` (Eq. `eq:one-step-minimax`).**  The minimax one-step risk of a loss family at a
fixed `θ`, represented by its gradient map `g = ∇ℓ(θ; ·) : Z → ℝ^d`:
`inf_M sup_P E ‖M(z₁..ₙ) − ∇F(θ)‖²` with `∇F(θ) = E_P[g z]`, the infimum over
`HetDPMechanisms n d Z ε` and the supremum over probability measures `P` on `Z`. -/
noncomputable def oneStepMinimaxRisk {Z : Type*} [MeasurableSpace Z] (ε : Fin n → ℝ)
    (g : Z → EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨅ M ∈ HetDPMechanisms n d Z ε,
    ⨆ (P : Measure Z) (_ : IsProbabilityMeasure P), mseRisk M P (∫ z, g z ∂P)

/-- **`ν*(C)` (Eq. `eq:one-step-minimax`).**  Heterogeneous mean-estimation minimax risk over
distributions supported on `B_C = closedBall 0 C ⊆ ℝ^d`:
`inf_{M'} sup_{Q ∈ Δ(B_C)} E ‖M'(y₁..ₙ) − E_Q[y]‖²`, the infimum over
`HetDPMechanisms n d ℝ^d ε`. -/
noncomputable def meanEstMinimaxRisk (n d : ℕ) (ε : Fin n → ℝ) (C : ℝ) : ℝ≥0∞ :=
  ⨅ M ∈ HetDPMechanisms n d (EuclideanSpace ℝ (Fin d)) ε,
    ⨆ (Q : Measure (EuclideanSpace ℝ (Fin d))) (_ : IsProbabilityMeasure Q)
      (_ : Q (closedBall 0 C)ᶜ = 0), mseRisk M Q (∫ y, y ∂Q)

/-- Composition of a mechanism with a measurable per-record map is in the mechanism class. -/
lemma comp_mem_hetDPMechanisms {Z Y' : Type*} [MeasurableSpace Z] [MeasurableSpace Y']
    {ε : Fin n → ℝ} {M' : (Fin n → Y') → Measure (EuclideanSpace ℝ (Fin d))}
    (hM' : M' ∈ HetDPMechanisms n d Y' ε) {g : Z → Y'} (hg : Measurable g) :
    (fun D : Fin n → Z => M' (fun i => g (D i))) ∈ HetDPMechanisms n d Z ε := by
  obtain ⟨hmeas, hprob, hdp⟩ := hM'
  refine ⟨hmeas.comp ?_, fun D => hprob _, hdp.comp_preprocess fun _ => g⟩
  exact measurable_pi_lambda _ fun i => hg.comp (measurable_pi_apply i)

/-- Pushforward of the product measure: the risk of `M' ∘ gⁿ` under `Pⁿ` is the risk of `M'`
under `(g_# P)ⁿ`, using `(Pⁿ).map gⁿ = (g_# P)ⁿ`. -/
lemma mseRisk_comp {Z Y' : Type*} [MeasurableSpace Z] [MeasurableSpace Y']
    {M' : (Fin n → Y') → Measure (EuclideanSpace ℝ (Fin d))} (hM' : Measurable M')
    {g : Z → Y'} (hg : Measurable g) (P : Measure Z) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d)) :
    mseRisk (fun D : Fin n → Z => M' (fun i => g (D i))) P m = mseRisk M' (P.map g) m := by
  have hF : Measurable fun D' : Fin n → Y' => ∫⁻ y, ‖y - m‖ₑ ^ 2 ∂(M' D') :=
    (Measure.measurable_lintegral
      (((measurable_id.sub_const m).enorm).pow_const 2)).comp hM'
  have hgn : Measurable fun (D : Fin n → Z) (i : Fin n) => g (D i) :=
    measurable_pi_lambda _ fun i => hg.comp (measurable_pi_apply i)
  unfold mseRisk
  rw [← Measure.pi_map_pi (fun _ => hg.aemeasurable), lintegral_map hF hgn]

/-- The mean of the pushforward is the mean of the map. -/
lemma integral_map_id {Z : Type*} [MeasurableSpace Z] {g : Z → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (P : Measure Z) :
    ∫ y, y ∂(P.map g) = ∫ z, g z ∂P :=
  integral_map hg.aemeasurable aestronglyMeasurable_id

/-- **Remark `rem:one-step-equivalence`, Part 1.**  For every loss family whose gradient map
`g = ∇ℓ(θ; ·)` at `θ` is measurable with `‖g z‖ ≤ C`, `ν_ℓ(θ) ≤ ν*(C)`. -/
theorem oneStepMinimaxRisk_le_meanEstMinimaxRisk {Z : Type*} [MeasurableSpace Z]
    (ε : Fin n → ℝ) {C : ℝ} {g : Z → EuclideanSpace ℝ (Fin d)} (hg : Measurable g)
    (hgC : ∀ z, ‖g z‖ ≤ C) :
    oneStepMinimaxRisk ε g ≤ meanEstMinimaxRisk n d ε C := by
  refine le_iInf₂ fun M' hM' => ?_
  refine (iInf₂_le _ (comp_mem_hetDPMechanisms hM' hg)).trans ?_
  refine iSup₂_le fun P hP => ?_
  have hQ : IsProbabilityMeasure (P.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hsupp : P.map g (closedBall 0 C)ᶜ = 0 := by
    rw [Measure.map_apply hg measurableSet_closedBall.compl]
    have : g ⁻¹' (closedBall 0 C)ᶜ = ∅ := by
      ext z; simpa [mem_closedBall, dist_zero_right] using hgC z
    rw [this, measure_empty]
  rw [mseRisk_comp hM'.1 hg P, ← integral_map_id hg P]
  exact le_iSup_of_le (P.map g) (le_iSup_of_le hQ (le_iSup_of_le hsupp le_rfl))

/-- The linear loss family `ℓ(θ; z) = ⟪z, θ⟫` has gradient `∇ℓ(θ; z) = z` at every `θ`. -/
theorem hasGradientAt_linearLoss (z θ : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (fun θ' => inner ℝ z θ') z θ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) z).hasFDerivAt

/-- **Remark `rem:one-step-equivalence`, Part 2.**  For the linear family with records in
`B_C` (records `z ∈ closedBall 0 C`, gradient map `z ↦ z` by `hasGradientAt_linearLoss`),
`ν_ℓ(θ) = ν*(C)`.  Here `C ≥ 0` (the paper assumes `C > 0`) so that `B_C` is nonempty. -/
theorem oneStepMinimaxRisk_linear (ε : Fin n → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    oneStepMinimaxRisk ε
        (fun z : closedBall (0 : EuclideanSpace ℝ (Fin d)) C => (z : EuclideanSpace ℝ (Fin d)))
      = meanEstMinimaxRisk n d ε C := by
  set B := closedBall (0 : EuclideanSpace ℝ (Fin d)) C
  have hB : MeasurableSet B := measurableSet_closedBall
  have hval : Measurable (Subtype.val : B → EuclideanSpace ℝ (Fin d)) := measurable_subtype_coe
  refine le_antisymm
    (oneStepMinimaxRisk_le_meanEstMinimaxRisk ε (C := C) hval
      fun z => mem_closedBall_zero_iff.1 z.2) ?_
  -- a measurable retraction `ℝ^d → B_C`
  classical
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ B := mem_closedBall_self hC
  let r : EuclideanSpace ℝ (Fin d) → B := fun y =>
    ⟨if y ∈ B then y else 0, by split_ifs with h <;> assumption⟩
  have hr : Measurable r :=
    (Measurable.ite hB measurable_id measurable_const).subtype_mk
  have hrv : ∀ z : B, r z = z := fun z => Subtype.ext (if_pos z.2)
  refine le_iInf₂ fun M hM => ?_
  let ME := fun D : Fin n → EuclideanSpace ℝ (Fin d) => M (fun i => r (D i))
  refine (iInf₂_le ME (comp_mem_hetDPMechanisms hM hr)).trans ?_
  refine iSup_le fun Q => iSup_le fun hQ => iSup_le fun hsupp => ?_
  -- `Q` is the pushforward of its restriction `P` to `B_C`
  set P : Measure B := Q.comap Subtype.val
  have hPQ : P.map Subtype.val = Q := by
    rw [map_comap_subtype_coe hB, Measure.restrict_eq_self_of_ae_mem]
    exact measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono fun y hy => not_not.mp hy
  have hP : IsProbabilityMeasure P := by
    constructor
    rw [comap_subtype_coe_apply hB, image_univ, Subtype.range_coe]
    exact (prob_compl_eq_zero_iff hB).1 hsupp
  have hME : (fun D : Fin n → B => ME (fun i => (D i : EuclideanSpace ℝ (Fin d)))) = M := by
    funext D; simp only [ME, hrv]
  rw [← hPQ, integral_map_id hval, ← mseRisk_comp (comp_mem_hetDPMechanisms hM hr).1 hval, hME]
  exact le_iSup_of_le P (le_iSup_of_le hP le_rfl)

/-- **Remark `rem:one-step-equivalence`, `sup_ℓ ν_ℓ(θ) = ν*(C)`.**  Among all loss families at
`θ` (record spaces `Z`, measurable gradient maps `g = ∇ℓ(θ; ·)` with `‖g z‖ ≤ C`), the value
`ν*(C)` is the greatest one-step minimax risk, attained by the linear family on `B_C`. -/
theorem isGreatest_oneStepMinimaxRisk (ε : Fin n → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    IsGreatest {v | ∃ (Z : Type) (_ : MeasurableSpace Z) (g : Z → EuclideanSpace ℝ (Fin d)),
        Measurable g ∧ (∀ z, ‖g z‖ ≤ C) ∧ v = oneStepMinimaxRisk ε g}
      (meanEstMinimaxRisk n d ε C) := by
  refine ⟨⟨closedBall (0 : EuclideanSpace ℝ (Fin d)) C, inferInstance, Subtype.val,
    measurable_subtype_coe, fun z => mem_closedBall_zero_iff.1 z.2,
    (oneStepMinimaxRisk_linear ε hC).symm⟩, ?_⟩
  rintro v ⟨Z, _, g, hg, hgC, rfl⟩
  exact oneStepMinimaxRisk_le_meanEstMinimaxRisk ε hg hgC

/-- **Remark `rem:one-step-equivalence`:** `sup_ℓ ν_ℓ(θ) = ν*(C)`. -/
theorem sSup_oneStepMinimaxRisk (ε : Fin n → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    sSup {v | ∃ (Z : Type) (_ : MeasurableSpace Z) (g : Z → EuclideanSpace ℝ (Fin d)),
        Measurable g ∧ (∀ z, ‖g z‖ ≤ C) ∧ v = oneStepMinimaxRisk ε g}
      = meanEstMinimaxRisk n d ε C :=
  (isGreatest_oneStepMinimaxRisk ε hC).csSup_eq

end OneStep

end Limites
