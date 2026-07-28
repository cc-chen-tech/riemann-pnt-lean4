import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedHeight

/-!
# Exact feasibility criterion for balanced Carlson heights

The contour and canonical low-strip estimates impose the strict window

`1 - beta < alpha < beta - sigma`.

This module proves that the window is nonempty exactly when
`(1 + sigma) / 2 < beta`.  It also identifies window membership with positive
robust margin, making the midpoint optimality theorem an exact truncation
certificate rather than only a sufficient construction.
-/

namespace PrimeNumberTheorem

/-- A candidate height exponent has positive robust margin exactly when both
strict decay inequalities hold. -/
theorem actualCarlsonHeightRobustMargin_pos_iff
    {beta sigma alpha : ℝ} :
    0 < actualCarlsonHeightRobustMargin beta sigma alpha ↔
      1 - beta < alpha ∧ alpha < beta - sigma := by
  unfold actualCarlsonHeightRobustMargin
  rw [lt_min_iff]
  constructor
  · rintro ⟨hcontour, hlow⟩
    constructor <;> linarith
  · rintro ⟨hcontour, hlow⟩
    constructor <;> linarith

/-- Exact nonemptiness criterion for the admissible polynomial-height
exponent window. -/
theorem actualCarlsonHeightWindow_nonempty_iff
    {beta sigma : ℝ} :
    (∃ alpha : ℝ, 1 - beta < alpha ∧ alpha < beta - sigma) ↔
      (1 + sigma) / 2 < beta := by
  constructor
  · rintro ⟨alpha, hcontour, hlow⟩
    linarith
  · intro hbalance
    exact
      ⟨actualCarlsonBalancedHeightExponent sigma,
        actualCarlsonBalancedHeightExponent_contour_margin hbalance,
        actualCarlsonBalancedHeightExponent_low_margin hbalance⟩

/-- The exact feasibility condition is equivalent to positivity of the
balanced robust margin. -/
theorem actualCarlsonBalancedHeightRobustMargin_pos_iff
    {beta sigma : ℝ} :
    0 <
        actualCarlsonHeightRobustMargin beta sigma
          (actualCarlsonBalancedHeightExponent sigma) ↔
      (1 + sigma) / 2 < beta := by
  rw [actualCarlsonHeightRobustMargin_balanced]
  constructor <;> intro h <;> linarith

/-- If the balanced feasibility inequality fails, no polynomial exponent can
make both the contour and low-strip powers decay strictly. -/
theorem actualCarlsonHeightWindow_empty_of_not_balance
    {beta sigma : ℝ} (hbalance : beta ≤ (1 + sigma) / 2) :
    ¬ ∃ alpha : ℝ, 1 - beta < alpha ∧ alpha < beta - sigma := by
  rw [actualCarlsonHeightWindow_nonempty_iff]
  exact not_lt.mpr hbalance

end PrimeNumberTheorem
