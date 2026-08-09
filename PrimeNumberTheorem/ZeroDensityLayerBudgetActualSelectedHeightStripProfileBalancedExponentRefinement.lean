import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileFeasibilityCharacterization

/-!
# Refinement monotonicity of the balanced truncation exponent

Profile refinement raises the effective Carlson ceiling.  Since the balanced
exponent is the midpoint between `1 - beta` and that ceiling, refinement also
raises the certified polynomial truncation exponent and hence its raw
polynomial scale on bases at least one.

This module deliberately does not assert monotonicity of the subsequently
selected good height: `selectedUniformGoodHeight` has no monotonicity contract.
-/

namespace PrimeNumberTheorem

/-- The effective Carlson ceiling attached to a packaged strip profile. -/
noncomputable def ActualSelectedHeightFiniteStripProfile.effectiveAlphaCeiling
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) : ℝ :=
  actualSelectedHeightFiniteStripEffectiveAlphaCeiling
    beta profile.sigma profile.tau

/-- The raw polynomial truncation scale before good-height selection. -/
noncomputable def ActualSelectedHeightFiniteStripProfile.balancedPolynomialScale
    (beta x : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) : ℝ :=
  x ^ profile.balancedExponent beta

/-- Comparing balanced exponents is exactly comparing effective Carlson
ceilings. -/
theorem
    ActualSelectedHeightFiniteStripProfile.balancedExponent_le_iff
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    left.balancedExponent beta ≤ right.balancedExponent beta ↔
      left.effectiveAlphaCeiling beta ≤
        right.effectiveAlphaCeiling beta := by
  change
    (1 - beta +
          actualSelectedHeightFiniteStripEffectiveAlphaCeiling
            beta left.sigma left.tau) / 2 ≤
        (1 - beta +
          actualSelectedHeightFiniteStripEffectiveAlphaCeiling
            beta right.sigma right.tau) / 2 ↔
      actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta left.sigma left.tau ≤
        actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta right.sigma right.tau
  constructor <;> intro h <;> linarith

/-- Strict comparison of balanced exponents is exactly strict comparison of
effective Carlson ceilings. -/
theorem
    ActualSelectedHeightFiniteStripProfile.balancedExponent_lt_iff
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    left.balancedExponent beta < right.balancedExponent beta ↔
      left.effectiveAlphaCeiling beta <
        right.effectiveAlphaCeiling beta := by
  change
    (1 - beta +
          actualSelectedHeightFiniteStripEffectiveAlphaCeiling
            beta left.sigma left.tau) / 2 <
        (1 - beta +
          actualSelectedHeightFiniteStripEffectiveAlphaCeiling
            beta right.sigma right.tau) / 2 ↔
      actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta left.sigma left.tau <
        actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta right.sigma right.tau
  constructor <;> intro h <;> linarith

/-- A refinement cannot lower the balanced truncation exponent. -/
theorem
    ActualSelectedHeightFiniteStripProfile.Refines.balancedExponent_mono
    {beta : ℝ}
    {refined coarse : ActualSelectedHeightFiniteStripProfile}
    (certificate : refined.Refines beta coarse) :
    coarse.balancedExponent beta ≤ refined.balancedExponent beta :=
  (ActualSelectedHeightFiniteStripProfile.balancedExponent_le_iff
    beta coarse refined).2
    (ActualSelectedHeightFiniteStripProfileRefinement.effectiveAlphaCeiling_mono
      certificate)

/-- Strict effective-ceiling improvement gives strict balanced-exponent
improvement. -/
theorem
    ActualSelectedHeightFiniteStripProfile.Refines.balancedExponent_lt
    {beta : ℝ}
    {refined coarse : ActualSelectedHeightFiniteStripProfile}
    (_certificate : refined.Refines beta coarse)
    (hstrict :
      coarse.effectiveAlphaCeiling beta <
        refined.effectiveAlphaCeiling beta) :
    coarse.balancedExponent beta < refined.balancedExponent beta :=
  (ActualSelectedHeightFiniteStripProfile.balancedExponent_lt_iff
    beta coarse refined).2 hstrict

/-- Refinement cannot lower the raw polynomial truncation scale on bases at
least one. -/
theorem
    ActualSelectedHeightFiniteStripProfile.Refines.balancedPolynomialScale_mono
    {beta x : ℝ}
    {refined coarse : ActualSelectedHeightFiniteStripProfile}
    (certificate : refined.Refines beta coarse)
    (hx : 1 ≤ x) :
    coarse.balancedPolynomialScale beta x ≤
      refined.balancedPolynomialScale beta x :=
  Real.rpow_le_rpow_of_exponent_le hx certificate.balancedExponent_mono

/-- Strict ceiling improvement strictly raises the raw polynomial truncation
scale on bases greater than one. -/
theorem
    ActualSelectedHeightFiniteStripProfile.Refines.balancedPolynomialScale_lt
    {beta x : ℝ}
    {refined coarse : ActualSelectedHeightFiniteStripProfile}
    (certificate : refined.Refines beta coarse)
    (hx : 1 < x)
    (hstrict :
      coarse.effectiveAlphaCeiling beta <
        refined.effectiveAlphaCeiling beta) :
    coarse.balancedPolynomialScale beta x <
      refined.balancedPolynomialScale beta x :=
  Real.rpow_lt_rpow_of_exponent_lt hx
    (certificate.balancedExponent_lt hstrict)

end PrimeNumberTheorem
