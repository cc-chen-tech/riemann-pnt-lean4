import HardyTheorem.SelbergFirstMomentBridge

open Complex

namespace HardyTheorem

#check abs_selbergCompletedMollifiedF_eq_gamma_tilt_mul_abs_sqrtZeta

example (delta : ℝ) (X : ℕ) (t : ℝ) :
    |selbergCompletedMollifiedF delta X t| =
      (1 / (2 * Real.sqrt (2 * Real.pi))) *
        ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ *
        Real.exp ((Real.pi / 4 - delta / 2) * t) *
        |selbergSqrtZetaMollifiedHardyZ X t| :=
  abs_selbergCompletedMollifiedF_eq_gamma_tilt_mul_abs_sqrtZeta delta X t

#print axioms abs_selbergCompletedMollifiedF_eq_gamma_tilt_mul_abs_sqrtZeta

end HardyTheorem
