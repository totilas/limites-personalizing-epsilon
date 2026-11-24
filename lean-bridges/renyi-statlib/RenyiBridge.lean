import LimitesProofs.Renyi
import Statlib.Divergence.Renyi.Basic

/-!
# Our Rényi divergence agrees with Statlib's

`Limites.renyiDiv` is the Rényi divergence defined in the main project
(`LimitesProofs/Renyi.lean`, copied here verbatim, see `check-sync.sh`).
`ProbabilityTheory.renyiDiv` is the one of Statlib (https://github.com/stat-lib/statlib),
an independent development of information divergences between measures, which
absorbed R. Degenne and L. Luccioli's TestingLowerBounds project.

`renyiDiv_eq_statlib`: for probability measures and every order `α > 1`
(the orders used by zCDP), the two definitions coincide.
-/

open MeasureTheory
open scoped ENNReal

namespace RenyiBridge

variable {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω} {α : ℝ}

/-- Jensen: `∫ (dP/dQ)^α dQ ≥ (∫ dP/dQ dQ)^α = 1` for `α ≥ 1`. -/
lemma one_le_integral_rpow_rnDeriv [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hα : 1 ≤ α) (hac : P ≪ Q) (hint : Integrable (fun x => (P.rnDeriv Q x).toReal ^ α) Q) :
    1 ≤ ∫ x, (P.rnDeriv Q x).toReal ^ α ∂Q := by
  have hmean : ∫ x, (P.rnDeriv Q x).toReal ∂Q = 1 := by
    rw [Measure.integral_toReal_rnDeriv hac]
    simp
  have hJ := (convexOn_rpow hα).map_integral_le (μ := Q) (f := fun x => (P.rnDeriv Q x).toReal)
    (continuousOn_id.rpow_const fun _ _ => Or.inr (by linarith)) isClosed_Ici
    (ae_of_all _ fun x => ENNReal.toReal_nonneg) Measure.integrable_toReal_rnDeriv hint
  simpa [hmean] using hJ

/-- **Bridge.**  For probability measures `P, Q` and `α > 1`, the Rényi divergence of the
main project equals the one of Statlib (coerced from `ℝ≥0∞` to `EReal`). -/
theorem renyiDiv_eq_statlib [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hα : 1 < α) :
    Limites.renyiDiv α P Q = (ProbabilityTheory.renyiDiv α P Q : EReal) := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  by_cases hac : P ≪ Q
  swap
  · rw [ProbabilityTheory.renyiDiv_of_one_le_of_not_ac hα.le hac]
    simp [Limites.renyiDiv, hac]
  -- `(dP/dQ)^α` as an `ℝ≥0∞`-valued function is a.e. the `ofReal` of its real version
  have hpt : ∀ᵐ x ∂Q, P.rnDeriv Q x ^ α = ENNReal.ofReal ((P.rnDeriv Q x).toReal ^ α) := by
    filter_upwards [Measure.rnDeriv_lt_top P Q] with x hx
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα0.le, ENNReal.ofReal_toReal hx.ne]
  by_cases hint : Integrable (fun x => (P.rnDeriv Q x).toReal ^ α) Q
  · rw [ProbabilityTheory.renyiDiv_eq_log_integral_of_one_lt hα hint hac]
    simp only [measure_univ, ENNReal.toReal_one, Real.log_one, mul_zero, add_zero, sub_zero]
    set I := ∫ x, (P.rnDeriv Q x).toReal ^ α ∂Q with hI_def
    have hI : 1 ≤ I := one_le_integral_rpow_rnDeriv hα.le hac hint
    have hlin : ∫⁻ x, P.rnDeriv Q x ^ α ∂Q = ENNReal.ofReal I := by
      rw [hI_def, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity)]
      exact lintegral_congr_ae hpt
    have hnn : 0 ≤ (α - 1)⁻¹ * Real.log I :=
      mul_nonneg (inv_nonneg.mpr hα1.le) (Real.log_nonneg hI)
    simp only [Limites.renyiDiv, hac, ↓reduceIte]
    rw [hlin, ENNReal.log_ofReal_of_pos (by linarith),
      EReal.coe_ennreal_ofReal, max_eq_left hnn]
    norm_cast
  · have htop : ProbabilityTheory.renyiDiv α P Q = ∞ :=
      (ProbabilityTheory.renyiDiv_eq_top_iff_of_one_lt hα).mpr (Or.inl hint)
    have hlin : ∫⁻ x, P.rnDeriv Q x ^ α ∂Q = ∞ := by
      by_contra hfin
      apply hint
      have := integrable_toReal_of_lintegral_ne_top
        ((Measure.measurable_rnDeriv P Q).pow_const α).aemeasurable hfin
      refine this.congr (ae_of_all _ fun x => ?_)
      simp [ENNReal.toReal_rpow]
    simp only [Limites.renyiDiv, hac, ↓reduceIte]
    rw [htop, hlin, ENNReal.log_top]
    simp [EReal.coe_mul_top_of_pos (inv_pos.mpr hα1)]

end RenyiBridge
