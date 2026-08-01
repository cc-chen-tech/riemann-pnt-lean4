import HardyTheorem.SelbergSqrtZetaSignedLagIntegral
import HardyTheorem.SelbergSqrtZetaSignedTotalShiftBudget

/-!
# Excessive signed windows from the complete shift budget

The total analytic budget is written in fixed square coordinates
`(v,w,x)`. This module identifies that integral with the signed short-mass
second moment and applies the sharp Chebyshev estimate. Consequently the
remaining inequality `TotalShiftBudget ≤ T * eta^2 / 24` is exactly the
arithmetic endpoint needed for the Selberg excessive-window bound.
-/

open MeasureTheory Set

namespace HardyTheorem

/-- The signed short-mass second moment equals the fixed-coordinate
shift-square autocorrelation integral. -/
theorem integral_sq_selbergSqrtZetaSignedShortIntegral_eq_fixedShiftSquare
    (X : ℕ) {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) =
      ∫ v in 0..H, ∫ w in 0..H, ∫ x in A..B,
        selbergSqrtZetaMollifiedHardyZ X (x + v) *
          selbergSqrtZetaMollifiedHardyZ X (x + w) := by
  rw [integral_sq_selbergSqrtZetaSignedShortIntegral_eq_correlation X hAB hH]
  apply intervalIntegral.integral_congr
  intro v _hv
  apply intervalIntegral.integral_congr
  intro w _hw
  have hadd (x : ℝ) : x + v + (w - v) = x + w := by ring
  have hshift :
      (∫ x in A..B,
          selbergSqrtZetaMollifiedHardyZ X (x + v) *
            selbergSqrtZetaMollifiedHardyZ X (x + w)) =
        ∫ x in A + v..B + v,
          selbergSqrtZetaMollifiedHardyZ X x *
            selbergSqrtZetaMollifiedHardyZ X (x + (w - v)) := by
    simpa only [hadd] using
      intervalIntegral.integral_comp_add_right
        (fun x =>
          selbergSqrtZetaMollifiedHardyZ X x *
            selbergSqrtZetaMollifiedHardyZ X (x + (w - v))) v
  exact hshift.symm

/-- Once the complete explicit shift budget fits inside
`T * eta^2 / 24`, the excessive signed-window set has the required measure
at most `T / 24`. -/
theorem
    exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_totalShiftBudget_le :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H M eta : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T → 0 ≤ M → 0 < eta →
        (∀ x ∈ Icc T (2 * T),
          |selbergSqrtZetaSignedThetaModel kappa T X x| ≤ M) →
        selbergSqrtZetaSignedTotalShiftBudget C T X H M ≤
          T * eta ^ 2 / 24 →
        volume.real
            (Icc T (2 * T - H) ∩
              selbergSqrtZetaExcessiveSignedMassStarts X H eta) ≤
          T / 24 := by
  obtain ⟨kappa, C, T0, hC, hT0, htotal⟩ :=
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudget
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X hX T H M eta hT hH hHT hM heta hmodel hbudget
  have hAB : T ≤ 2 * T - H := by linarith
  let actual : ℝ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ x in T..2 * T - H,
      selbergSqrtZetaMollifiedHardyZ X (x + v) *
        selbergSqrtZetaMollifiedHardyZ X (x + w)
  have hactualAbs :
      |actual| ≤ selbergSqrtZetaSignedTotalShiftBudget C T X H M := by
    simpa only [actual] using
      htotal X hX T H M hT hH hHT hM hmodel
  have hactual :
      actual ≤ T * eta ^ 2 / 24 :=
    (le_abs_self actual).trans (hactualAbs.trans hbudget)
  have hcheb :=
    volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_secondMoment
      X (H := H) hAB heta
  rw [Set.inter_comm]
  refine hcheb.trans ?_
  rw [integral_sq_selbergSqrtZetaSignedShortIntegral_eq_fixedShiftSquare
    X hAB hH]
  change actual / eta ^ 2 ≤ T / 24
  rw [div_le_iff₀ (sq_pos_of_pos heta)]
  calc
    actual ≤ T * eta ^ 2 / 24 := hactual
    _ = T / 24 * eta ^ 2 := by ring

/-- Fully arithmetic endpoint for `hexcessive`: the finite coefficient `L1`
bound discharges the model-supremum hypothesis automatically. -/
theorem
    exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_totalShiftBudget_modelSupBound_le :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H eta : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T → 0 < eta →
        selbergSqrtZetaSignedTotalShiftBudget C T X H
            (selbergSqrtZetaSignedModelSupBoundL1 T X) ≤
          T * eta ^ 2 / 24 →
        volume.real
            (Icc T (2 * T - H) ∩
              selbergSqrtZetaExcessiveSignedMassStarts X H eta) ≤
          T / 24 := by
  obtain ⟨kappa, C, T0, hC, hT0, hfinal⟩ :=
    exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_totalShiftBudget_le
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H eta hT hH hHT heta hbudget
  apply hfinal X hX T H
    (selbergSqrtZetaSignedModelSupBoundL1 T X) eta
    hT hH hHT
  · unfold selbergSqrtZetaSignedModelSupBoundL1
    positivity
  · exact heta
  · intro x _hx
    exact
      abs_selbergSqrtZetaSignedThetaModel_le_modelSupBoundL1
        kappa T X x
  · exact hbudget

end HardyTheorem
