import HardyTheorem.SelbergFirstMomentSliding

open Complex MeasureTheory
open scoped Interval

namespace HardyTheorem

example :
    ∃ c T0 : ℝ, 0 < c ∧ 2 ≤ T0 ∧
      ∀ T H : ℝ, T0 ≤ T → 0 ≤ H → H ≤ T / 2 →
        c * (H * T ^ (3 / 4 : ℝ)) ≤
          ∫ t in 0..T,
            ∫ u in t..t + H,
              |selbergCompletedMollifiedF (1 / T)
                (selbergFirstMomentCutoff T) u| :=
  exists_pos_rpow_three_quarters_selbergSlidingFirstMoment_lower

#print axioms MathlibAux.length_mul_integral_interior_le_integral_slidingWindow
#print axioms exists_pos_rpow_three_quarters_selbergSlidingFirstMoment_lower

end HardyTheorem
