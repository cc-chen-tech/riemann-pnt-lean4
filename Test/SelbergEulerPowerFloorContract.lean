import HardyTheorem.SelbergEulerPowerFloor

open Finset
open scoped BigOperators

namespace HardyTheorem

#check rpow_increment_div_le_left
#check selbergEulerFloorPowerSum
#check selbergEulerFloorError
#check exists_selbergEulerFloorPowerSum_error
#check abs_selbergEulerFloorError_le
#check selbergEulerFloorPowerSum_eq_main_add_error

example {theta z : ℝ} (htheta0 : 0 < theta)
    (hthetaHalf : theta ≤ 1 / 2) (hz : 1 ≤ z) :
    ∃ E : ℝ,
      |E| ≤ z ^ (theta - 1) ∧
      selbergEulerFloorPowerSum theta z =
        (z ^ theta + selbergEulerPowerConstant theta) / theta + E :=
  exists_selbergEulerFloorPowerSum_error htheta0 hthetaHalf hz

end HardyTheorem
