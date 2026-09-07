import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Real powers on a positive compact interval

The standard `integral_rpow` theorem has a disjunctive side condition.  These
lemmas package the positive-interval case and the two endpoint estimates used
in the critical approximate functional equation.
-/

open Set MeasureTheory

namespace MathlibAux

theorem intervalIntegrable_rpow_of_pos
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ r) volume a b := by
  apply intervalIntegral.intervalIntegrable_rpow
  right
  rw [uIcc_of_le hab]
  intro hzero
  linarith [hzero.1]

theorem intervalIntegral_rpow_eq_of_pos
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : r ≠ -1) :
    (∫ u in a..b, u ^ r) =
      (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  rw [integral_rpow]
  right
  refine ⟨hr, ?_⟩
  rw [uIcc_of_le hab]
  intro hzero
  linarith [hzero.1]

theorem intervalIntegral_rpow_le_right_endpoint
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : -1 < r) :
    (∫ u in a..b, u ^ r) ≤ b ^ (r + 1) / (r + 1) := by
  rw [intervalIntegral_rpow_eq_of_pos ha hab (by linarith)]
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ r + 1)
  nlinarith [Real.rpow_nonneg ha.le (r + 1)]

theorem intervalIntegral_rpow_le_left_endpoint
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hr : r < -1) :
    (∫ u in a..b, u ^ r) ≤ a ^ (r + 1) / (-r - 1) := by
  rw [intervalIntegral_rpow_eq_of_pos ha hab (by linarith)]
  have hrewrite :
      (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) =
        (a ^ (r + 1) - b ^ (r + 1)) / (-r - 1) := by
    field_simp [show r + 1 ≠ 0 by linarith, show -r - 1 ≠ 0 by linarith]
    ring
  rw [hrewrite]
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ -r - 1)
  nlinarith [Real.rpow_nonneg (ha.trans_le hab).le (r + 1)]

end MathlibAux
