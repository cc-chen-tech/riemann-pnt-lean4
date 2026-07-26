import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileBalancedExponentRefinement

/-!
# The finite profile optimizer also optimizes the truncation exponent

For fixed `beta`, both the balanced robust margin and the balanced truncation
exponent are affine increasing functions of the effective Carlson ceiling.
Thus the profile selected by maximal margin also maximizes the truncation
exponent and its raw polynomial scale inside the supplied finite family.
-/

namespace PrimeNumberTheorem

/-- The packaged optimal robust margin is half the gap between the effective
Carlson ceiling and the contour-transition lower endpoint. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_eq_half_ceiling_gap
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) :
    profile.optimalRobustMargin beta =
      (profile.effectiveAlphaCeiling beta - (1 - beta)) / 2 := by
  exact
    actualSelectedHeightFiniteStripBalancedExponent_robustMargin
      beta profile.sigma profile.tau

/-- Comparing optimal robust margins is exactly comparing effective Carlson
ceilings. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_le_iff
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    left.optimalRobustMargin beta ≤ right.optimalRobustMargin beta ↔
      left.effectiveAlphaCeiling beta ≤
        right.effectiveAlphaCeiling beta := by
  rw [left.optimalRobustMargin_eq_half_ceiling_gap,
    right.optimalRobustMargin_eq_half_ceiling_gap]
  constructor <;> intro h <;> linarith

/-- Strict margin comparison is exactly strict effective-ceiling comparison. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_lt_iff
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    left.optimalRobustMargin beta < right.optimalRobustMargin beta ↔
      left.effectiveAlphaCeiling beta <
        right.effectiveAlphaCeiling beta := by
  rw [left.optimalRobustMargin_eq_half_ceiling_gap,
    right.optimalRobustMargin_eq_half_ceiling_gap]
  constructor <;> intro h <;> linarith

/-- Margin ordering and balanced-exponent ordering coincide. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_le_iff_balancedExponent_le
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    left.optimalRobustMargin beta ≤ right.optimalRobustMargin beta ↔
      left.balancedExponent beta ≤ right.balancedExponent beta :=
  (ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_le_iff
    beta left right).trans
    (ActualSelectedHeightFiniteStripProfile.balancedExponent_le_iff
      beta left right).symm

/-- Strict margin ordering and strict balanced-exponent ordering coincide. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_lt_iff_balancedExponent_lt
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    left.optimalRobustMargin beta < right.optimalRobustMargin beta ↔
      left.balancedExponent beta < right.balancedExponent beta :=
  (ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_lt_iff
    beta left right).trans
    (ActualSelectedHeightFiniteStripProfile.balancedExponent_lt_iff
      beta left right).symm

/-- The margin optimizer maximizes the effective Carlson ceiling among all
candidates. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_effectiveAlphaCeiling_ge
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates) :
    candidate.effectiveAlphaCeiling beta ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).effectiveAlphaCeiling beta :=
  (ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_le_iff
    beta candidate
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne)).1
    (optimalActualSelectedHeightFiniteStripProfile_score_ge
      beta candidates hne hcandidate)

/-- The margin optimizer also maximizes the balanced truncation exponent among
all candidates. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_balancedExponent_ge
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates) :
    candidate.balancedExponent beta ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).balancedExponent beta :=
  (ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_le_iff_balancedExponent_le
    beta candidate
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne)).1
    (optimalActualSelectedHeightFiniteStripProfile_score_ge
      beta candidates hne hcandidate)

/-- On bases at least one, the selected profile maximizes the raw polynomial
truncation scale among all candidates. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_balancedPolynomialScale_ge
    (beta x : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (hx : 1 ≤ x) :
    candidate.balancedPolynomialScale beta x ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).balancedPolynomialScale beta x :=
  Real.rpow_le_rpow_of_exponent_le hx
    (optimalActualSelectedHeightFiniteStripProfile_balancedExponent_ge
      beta candidates hne hcandidate)

end PrimeNumberTheorem
