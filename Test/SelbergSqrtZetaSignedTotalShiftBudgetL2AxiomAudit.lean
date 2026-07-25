import HardyTheorem.SelbergSqrtZetaSignedTotalShiftBudgetL2

open MeasureTheory
open HardyTheorem

#check selbergSqrtZetaSignedModelTransferShiftBudgetL2
#check selbergSqrtZetaSignedTotalShiftBudgetL2
#check
  exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudgetL2

example (Cactual Ctransfer T : ℝ) (X : ℕ) (H : ℝ) :
    selbergSqrtZetaSignedModelTransferShiftBudgetL2
        Cactual Ctransfer T X H =
      H ^ 2 * (4 * Ctransfer * X / Real.sqrt T) *
        Real.sqrt (T - H) *
        (Real.sqrt (selbergSqrtZetaSignedActualL2Budget Cactual T X) +
          Real.sqrt (selbergSqrtZetaSignedModelL2Budget T X)) := rfl

example (Cactual Ctransfer T : ℝ) (X : ℕ) (H : ℝ) :
    selbergSqrtZetaSignedTotalShiftBudgetL2 Cactual Ctransfer T X H =
      selbergSqrtZetaSignedModelTransferShiftBudgetL2
          Cactual Ctransfer T X H +
        selbergSqrtZetaSignedOrdinaryGapShiftBudget T X H +
        selbergSqrtZetaSignedDiagonalShiftBudget T X H := rfl

example :
    ∃ Cactual Ctransfer T0 : ℝ,
      0 ≤ Cactual ∧ 0 ≤ Ctransfer ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T →
        |∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
            selbergSqrtZetaMollifiedHardyZ X (t + v) *
              selbergSqrtZetaMollifiedHardyZ X (t + w)| ≤
          selbergSqrtZetaSignedTotalShiftBudgetL2
            Cactual Ctransfer T X H :=
  exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudgetL2

#print axioms
  exists_abs_integral_integral_integral_selbergSqrtZetaMollifiedAutocorrelation_le_totalShiftBudgetL2
