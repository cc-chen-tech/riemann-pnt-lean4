import HardyTheorem.SelbergFirstMomentLower

open Complex MeasureTheory
open scoped Interval

namespace HardyTheorem

example :
    ∃ c : ℝ, 0 < c ∧
      ∀ T delta : ℝ, ∀ X : ℕ,
        2 ≤ T → 0 ≤ delta → delta ≤ 1 / T →
        T / 4 ≤
          ‖∫ t in T / 2..T,
              selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)‖ →
        c * T ^ (3 / 4 : ℝ) ≤
          ∫ t in T / 2..T, |selbergCompletedMollifiedF delta X t| :=
  exists_pos_mul_rpow_three_quarters_le_integral_abs_selbergCompletedMollifiedF_of_contour

example :
    ∃ c C T0 : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T delta : ℝ, ∀ X : ℕ,
        T0 ≤ T → 2 ≤ X → 0 ≤ delta → delta ≤ 1 / T →
        16 / Real.log 2 ≤ T / 8 →
        2 * C * X * Real.sqrt (T / 2) ≤ T / 8 →
        c * T ^ (3 / 4 : ℝ) ≤
          ∫ t in T / 2..T, |selbergCompletedMollifiedF delta X t| :=
  exists_pos_rpow_three_quarters_firstMoment_of_horizontal_absorption

#print axioms exists_pos_mul_rpow_three_quarters_le_integral_abs_selbergCompletedMollifiedF_of_contour
#print axioms exists_pos_rpow_three_quarters_firstMoment_of_horizontal_absorption

end HardyTheorem
