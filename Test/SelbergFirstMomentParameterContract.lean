import HardyTheorem.SelbergFirstMomentParameter

open Complex MeasureTheory Filter
open scoped Interval

namespace HardyTheorem

example {C : ℝ} (hC : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      2 ≤ selbergFirstMomentCutoff T ∧
      16 / Real.log 2 ≤ T / 8 ∧
      2 * C * selbergFirstMomentCutoff T * Real.sqrt (T / 2) ≤ T / 8 :=
  eventually_selbergFirstMomentCutoff_absorbs_contour_errors hC

example :
    ∃ c T0 : ℝ, 0 < c ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        c * T ^ (3 / 4 : ℝ) ≤
          ∫ t in T / 2..T,
            |selbergCompletedMollifiedF (1 / T)
              (selbergFirstMomentCutoff T) t| :=
  exists_pos_rpow_three_quarters_selbergFirstMomentCutoff_lower

example :
    ∃ c T0 : ℝ, 0 < c ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        c * T ^ (3 / 4 : ℝ) ≤
          ∫ t in 0..T,
            |selbergCompletedMollifiedF (1 / T)
              (selbergFirstMomentCutoff T) t| :=
  exists_pos_rpow_three_quarters_selbergFirstMomentCutoff_zero_T_lower

#print axioms eventually_selbergFirstMomentCutoff_absorbs_contour_errors
#print axioms exists_pos_rpow_three_quarters_selbergFirstMomentCutoff_lower
#print axioms exists_pos_rpow_three_quarters_selbergFirstMomentCutoff_zero_T_lower

end HardyTheorem
