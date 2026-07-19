import HardyTheorem.HardyCompletedCriticalLine

open Complex

namespace HardyTheorem

example (t : ℝ) :
    hardyCompletedCriticalLine t =
      ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ * hardyZ t :=
  hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ t

example (t : ℝ) :
    hardyCompletedCriticalLine t = 0 ↔ hardyZ t = 0 :=
  hardyCompletedCriticalLine_eq_zero_iff_hardyZ_eq_zero t

example (t : ℝ) :
    0 < hardyCompletedCriticalLine t ↔ 0 < hardyZ t :=
  hardyCompletedCriticalLine_pos_iff_hardyZ_pos t

example (t : ℝ) :
    hardyCompletedCriticalLine t < 0 ↔ hardyZ t < 0 :=
  hardyCompletedCriticalLine_neg_iff_hardyZ_neg t

end HardyTheorem

#print axioms HardyTheorem.hardyZ_eq_completedRiemannZeta_re_div_norm
#print axioms HardyTheorem.hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ
#print axioms HardyTheorem.hardyCompletedCriticalLine_eq_zero_iff_hardyZ_eq_zero
#print axioms HardyTheorem.hardyCompletedCriticalLine_pos_iff_hardyZ_pos
#print axioms HardyTheorem.hardyCompletedCriticalLine_neg_iff_hardyZ_neg
