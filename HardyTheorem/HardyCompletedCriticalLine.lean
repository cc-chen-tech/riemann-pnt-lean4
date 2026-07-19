import HardyTheorem.HardyIntegralBasics

open Complex

namespace HardyTheorem

/-!
# The real completed zeta function on the critical line

The Fourier-transform proof of Hardy--Littlewood is naturally stated for
the completed zeta function.  This file records that its real critical-line
restriction differs from `hardyZ` by a strictly positive factor, so signs and
zeros can be transferred without loss.
-/

/-- The real value of the completed Riemann zeta function on the critical
line. -/
noncomputable def hardyCompletedCriticalLine (t : ℝ) : ℝ :=
  (completedRiemannZeta ((1 / 2 : ℂ) + I * t)).re

/-- The completed critical-line function is the Hardy function multiplied by
the norm of the archimedean factor. -/
theorem hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ (t : ℝ) :
    hardyCompletedCriticalLine t =
      ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ * hardyZ t := by
  have h := hardyZ_eq_completedRiemannZeta_re_div_norm t
  have hgamma : 0 < ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ := by
    exact norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by norm_num))
  dsimp only [hardyCompletedCriticalLine]
  calc
    (completedRiemannZeta ((1 / 2 : ℂ) + I * t)).re =
        hardyZ t * ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ :=
      ((eq_div_iff hgamma.ne').mp h).symm
    _ = ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ * hardyZ t := mul_comm _ _

/-- The completed critical-line function and `hardyZ` have the same zeros. -/
theorem hardyCompletedCriticalLine_eq_zero_iff_hardyZ_eq_zero (t : ℝ) :
    hardyCompletedCriticalLine t = 0 ↔ hardyZ t = 0 := by
  rw [hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ]
  simp only [mul_eq_zero, norm_eq_zero]
  exact or_iff_right (Gammaℝ_ne_zero_of_re_pos (by norm_num))

/-- The completed critical-line function and `hardyZ` have the same positive
set. -/
theorem hardyCompletedCriticalLine_pos_iff_hardyZ_pos (t : ℝ) :
    0 < hardyCompletedCriticalLine t ↔ 0 < hardyZ t := by
  rw [hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ]
  have hgamma : 0 < ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by norm_num))
  exact mul_pos_iff_of_pos_left hgamma

/-- The completed critical-line function and `hardyZ` have the same negative
set. -/
theorem hardyCompletedCriticalLine_neg_iff_hardyZ_neg (t : ℝ) :
    hardyCompletedCriticalLine t < 0 ↔ hardyZ t < 0 := by
  rw [hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ]
  have hgamma : 0 < ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ :=
    norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by norm_num))
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀ hgamma :
      ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ * hardyZ t <
          ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ * 0 ↔
        hardyZ t < 0)

end HardyTheorem
