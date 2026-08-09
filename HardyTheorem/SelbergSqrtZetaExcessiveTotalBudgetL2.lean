import HardyTheorem.SelbergSqrtZetaExcessiveTotalBudget
import HardyTheorem.SelbergSqrtZetaSignedTotalShiftBudgetL2

/-!
# Excessive signed windows from the explicit L2 shift budget

The L2 transfer removes both the finite-model supremum and abstract square-mass
inputs from the excessive-window endpoint.  The only remaining hypothesis is
the explicit finite budget inequality displayed below.
-/

open MeasureTheory Set

namespace HardyTheorem

/-- If the explicit L2 shift budget fits inside `T * eta² / 24`, the excessive
signed-window set has measure at most `T / 24`. -/
theorem
    exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_totalShiftBudgetL2_le :
    ∃ Cactual Ctransfer T0 : ℝ,
      0 ≤ Cactual ∧ 0 ≤ Ctransfer ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H eta : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T → 0 < eta →
        selbergSqrtZetaSignedTotalShiftBudgetL2
            Cactual Ctransfer T X H ≤ T * eta ^ 2 / 24 →
        volume.real
            (Icc T (2 * T - H) ∩
              selbergSqrtZetaExcessiveSignedMassStarts X H eta) ≤
          T / 24 := by
  obtain ⟨Cactual, Ctransfer, T0, hCactual, hCtransfer, hT0, htotal⟩ :=
    exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudgetL2
  refine ⟨Cactual, Ctransfer, T0, hCactual, hCtransfer, hT0, ?_⟩
  intro X hX T H eta hT hH hHT heta hbudget
  have hAB : T ≤ 2 * T - H := by linarith
  let actual : ℝ :=
    ∫ v in 0..H, ∫ w in 0..H, ∫ x in T..2 * T - H,
      selbergSqrtZetaMollifiedHardyZ X (x + v) *
        selbergSqrtZetaMollifiedHardyZ X (x + w)
  have hactualAbs :
      |actual| ≤
        selbergSqrtZetaSignedTotalShiftBudgetL2
          Cactual Ctransfer T X H := by
    simpa only [actual] using htotal X hX T H hT hH hHT
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

end HardyTheorem
