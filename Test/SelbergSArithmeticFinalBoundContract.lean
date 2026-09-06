import HardyTheorem.SelbergSArithmeticFinalBound

open Complex Nat Finset
open scoped BigOperators

namespace HardyTheorem

#check exists_norm_selbergArithmeticDiagonalSum_le

example :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (theta : ℝ),
        0 ≤ theta → theta ≤ 1 → Real.exp 1 ≤ (X : ℝ) →
        ‖selbergArithmeticDiagonalSum X theta‖ ≤
          C * ((X : ℝ) ^ (2 * theta)) / Real.log (X : ℝ) :=
  exists_norm_selbergArithmeticDiagonalSum_le

end HardyTheorem
