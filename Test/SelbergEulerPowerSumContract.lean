import HardyTheorem.SelbergEulerPowerSum

open scoped BigOperators

namespace HardyTheorem

#check selbergEulerPowerCorrection
#check selbergEulerPowerConstant
#check summable_selbergEulerPowerCorrection
#check abs_selbergEulerPowerConstant_le_one
#check exists_selbergEulerPowerSum_remainder

example {theta : ℝ} (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (N : ℕ) :
    ∃ R : ℝ,
      0 ≤ R ∧ R ≤ ((N + 1 : ℕ) : ℝ) ^ (theta - 1) ∧
      (∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ) ^ (theta - 1))) =
        (((N + 1 : ℕ) : ℝ) ^ theta +
            selbergEulerPowerConstant theta) / theta - R :=
  exists_selbergEulerPowerSum_remainder htheta0 hthetaHalf N

end HardyTheorem
