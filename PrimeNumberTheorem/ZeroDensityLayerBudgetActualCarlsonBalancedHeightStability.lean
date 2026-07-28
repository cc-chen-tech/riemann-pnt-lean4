import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedHeightFeasibility

/-!
# Quantitative stability of the balanced Carlson height

The robust truncation margin loses exactly the distance from the midpoint
height exponent.  Thus the balanced choice is not only optimal: its loss under
perturbation is explicitly linear and the optimizer is unique.
-/

namespace PrimeNumberTheorem

/-- Exact loss formula for moving the polynomial-height exponent away from
the balanced midpoint. -/
theorem actualCarlsonHeightRobustMargin_eq_balanced_sub_abs
    (beta sigma alpha : ℝ) :
    actualCarlsonHeightRobustMargin beta sigma alpha =
      (2 * beta - 1 - sigma) / 2 -
        |alpha - actualCarlsonBalancedHeightExponent sigma| := by
  unfold actualCarlsonHeightRobustMargin
    actualCarlsonBalancedHeightExponent
  by_cases hleft : alpha ≤ (1 - sigma) / 2
  · rw [min_eq_left (by linarith), abs_of_nonpos (by linarith)]
    ring
  · have hright : (1 - sigma) / 2 ≤ alpha := by
      linarith
    rw [min_eq_right (by linarith), abs_of_nonneg (by linarith)]
    ring

/-- The balanced exponent is the unique maximizer of the two-sided robust
margin. -/
theorem actualCarlsonHeightRobustMargin_eq_balanced_iff
    {beta sigma alpha : ℝ} :
    actualCarlsonHeightRobustMargin beta sigma alpha =
        (2 * beta - 1 - sigma) / 2 ↔
      alpha = actualCarlsonBalancedHeightExponent sigma := by
  rw [actualCarlsonHeightRobustMargin_eq_balanced_sub_abs]
  constructor
  · intro h
    have habs :
        |alpha - actualCarlsonBalancedHeightExponent sigma| = 0 := by
      linarith
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro h
    rw [h, sub_self, abs_zero, sub_zero]

/-- A candidate exponent is within `delta` of the optimal robust margin
exactly when it is within `delta` of the balanced exponent. -/
theorem actualCarlsonHeightRobustMargin_near_optimal_iff
    {beta sigma alpha delta : ℝ} :
    (2 * beta - 1 - sigma) / 2 - delta ≤
        actualCarlsonHeightRobustMargin beta sigma alpha ↔
      |alpha - actualCarlsonBalancedHeightExponent sigma| ≤ delta := by
  rw [actualCarlsonHeightRobustMargin_eq_balanced_sub_abs]
  constructor <;> intro h <;> linarith

end PrimeNumberTheorem
