import HardyTheorem.SelbergFirstMomentRightEdge

open Complex MeasureTheory

namespace HardyTheorem

example {X : ℕ} (hX : 2 ≤ X) {a b : ℝ} :
    ‖∫ t in a..b,
        (selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t) - 1)‖ ≤
      16 / Real.log 2 :=
  norm_intervalIntegral_selbergFirstMomentAuxiliary_rightLine_sub_one_le hX

#print axioms
  norm_intervalIntegral_selbergFirstMomentAuxiliary_rightLine_sub_one_le

end HardyTheorem
