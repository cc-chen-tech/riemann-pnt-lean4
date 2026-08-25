import MathlibAux.AbsoluteSlidingWindowL2

open MeasureTheory Set
open scoped Interval

namespace MathlibAux

#check integral_sq_abs_slidingWindow_le

#print axioms integral_sq_abs_slidingWindow_le

example {F : ℝ → ℂ} (hF : MemLp F 2) :
    (∫ t : ℝ, (∫ u in t..t + 0, ‖F u‖) ^ 2) ≤
      (0 : ℝ) ^ 2 * ∫ u : ℝ, ‖F u‖ ^ 2 := by
  exact integral_sq_abs_slidingWindow_le hF le_rfl

end MathlibAux
