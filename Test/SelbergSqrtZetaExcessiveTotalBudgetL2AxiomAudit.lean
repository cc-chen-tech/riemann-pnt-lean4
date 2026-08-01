import HardyTheorem.SelbergSqrtZetaExcessiveTotalBudgetL2

open MeasureTheory Set
open HardyTheorem

#check
  exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_totalShiftBudgetL2_le

example :
    ∃ Cactual Ctransfer T0 : ℝ,
      0 ≤ Cactual ∧ 0 ≤ Ctransfer ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H eta : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T → 0 < eta →
        selbergSqrtZetaSignedTotalShiftBudgetL2
            Cactual Ctransfer T X H ≤ T * eta ^ 2 / 24 →
        volume.real
            (Icc T (2 * T - H) ∩
              selbergSqrtZetaExcessiveSignedMassStarts X H eta) ≤
          T / 24 :=
  exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_totalShiftBudgetL2_le

#print axioms
  exists_volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_totalShiftBudgetL2_le
