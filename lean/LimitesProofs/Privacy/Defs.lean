import Mathlib

/-!
# Differential-privacy definitions (Section "Preliminaries")

Datasets of `n` records from a measurable space `X` are maps `Fin n → X`; a
mechanism is a map from datasets to measures on the output space (the law of its
output).  Records `i` of `D` and `D'` are the only ones that may differ when
`NeighborAt i D D'`.
-/

open MeasureTheory

namespace Limites

/-- `D` and `D'` differ (arbitrarily) only in the `i`-th record. -/
def NeighborAt {n : ℕ} {X : Type*} (i : Fin n) (D D' : Fin n → X) : Prop :=
  ∀ j, j ≠ i → D j = D' j

/-- `D` and `D'` differ in at most one record. -/
def Neighbor {n : ℕ} {X : Type*} (D D' : Fin n → X) : Prop :=
  ∃ i, NeighborAt i D D'

/-- **Definition (Approximate Differential Privacy)**, for a neighbouring relation `Adj`:
`Pr(M(D) ∈ S) ≤ e^ε Pr(M(D') ∈ S) + δ` for all `D ∼ D'` and measurable `S`. -/
def ApproxDP {Data Y : Type*} [MeasurableSpace Y] (Adj : Data → Data → Prop)
    (M : Data → Measure Y) (ε δ : ℝ) : Prop :=
  ∀ D D', Adj D D' → ∀ S, MeasurableSet S →
    M D S ≤ ENNReal.ofReal (Real.exp ε) * M D' S + ENNReal.ofReal δ

/-- **Definition `def:heterogenenous_DP` (Heterogeneous DP).**  For every `i`,
`Pr(M(D) ∈ S) ≤ e^{εᵢ} Pr(M(D'ⁱ) ∈ S)` whenever `D, D'ⁱ` differ only in record `i`. -/
def HetDP {n : ℕ} {X Y : Type*} [MeasurableSpace Y] (M : (Fin n → X) → Measure Y)
    (ε : Fin n → ℝ) : Prop :=
  ∀ i D D', NeighborAt i D D' → ∀ S, MeasurableSet S →
    M D S ≤ ENNReal.ofReal (Real.exp (ε i)) * M D' S

end Limites
