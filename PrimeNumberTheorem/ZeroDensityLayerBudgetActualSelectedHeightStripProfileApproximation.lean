import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileOptimalExponent

/-!
# Approximation guarantees for finite strip-profile search

A finite candidate family need not contain a globally optimal profile.  This
module gives a quantitative comparison with any benchmark profile: an
`epsilon` approximation to its effective Carlson ceiling yields an
`epsilon / 2` approximation to both the balanced exponent and robust margin.
-/

namespace PrimeNumberTheorem

/-- Balanced-exponent differences are exactly half the corresponding
effective-ceiling differences. -/
theorem
    ActualSelectedHeightFiniteStripProfile.balancedExponent_sub_eq_half_ceiling_sub
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    right.balancedExponent beta - left.balancedExponent beta =
      (right.effectiveAlphaCeiling beta -
        left.effectiveAlphaCeiling beta) / 2 := by
  change
    (1 - beta +
          actualSelectedHeightFiniteStripEffectiveAlphaCeiling
            beta right.sigma right.tau) / 2 -
        (1 - beta +
          actualSelectedHeightFiniteStripEffectiveAlphaCeiling
            beta left.sigma left.tau) / 2 =
      (actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta right.sigma right.tau -
        actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta left.sigma left.tau) / 2
  ring

/-- Optimal-margin differences are exactly half the corresponding
effective-ceiling differences. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_sub_eq_half_ceiling_sub
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    right.optimalRobustMargin beta - left.optimalRobustMargin beta =
      (right.effectiveAlphaCeiling beta -
        left.effectiveAlphaCeiling beta) / 2 := by
  rw [right.optimalRobustMargin_eq_half_ceiling_gap,
    left.optimalRobustMargin_eq_half_ceiling_gap]
  ring

/-- Balanced-exponent regret and optimal-margin regret coincide exactly. -/
theorem
    ActualSelectedHeightFiniteStripProfile.balancedExponent_sub_eq_optimalRobustMargin_sub
    (beta : ℝ)
    (left right : ActualSelectedHeightFiniteStripProfile) :
    right.balancedExponent beta - left.balancedExponent beta =
      right.optimalRobustMargin beta - left.optimalRobustMargin beta := by
  rw [
    ActualSelectedHeightFiniteStripProfile.balancedExponent_sub_eq_half_ceiling_sub
      beta left right,
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_sub_eq_half_ceiling_sub
      beta left right]

/-- If one candidate approximates a benchmark effective ceiling within
`epsilon`, the selected profile approximates the benchmark balanced exponent
within `epsilon / 2`. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_balancedExponent_approximation
    (beta epsilon : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (benchmark : ActualSelectedHeightFiniteStripProfile)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon) :
    benchmark.balancedExponent beta ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).balancedExponent beta + epsilon / 2 := by
  let chosen :=
    optimalActualSelectedHeightFiniteStripProfile beta candidates hne
  have hcandidateChosen :
      candidate.effectiveAlphaCeiling beta ≤
        chosen.effectiveAlphaCeiling beta := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_effectiveAlphaCeiling_ge
        beta candidates hne hcandidate
  have hbenchmarkChosen :
      benchmark.effectiveAlphaCeiling beta ≤
        chosen.effectiveAlphaCeiling beta + epsilon := by
    linarith
  have hdifference :=
    ActualSelectedHeightFiniteStripProfile.balancedExponent_sub_eq_half_ceiling_sub
      beta chosen benchmark
  linarith

/-- The same ceiling approximation gives an `epsilon / 2` robust-margin
guarantee. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_approximation
    (beta epsilon : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (benchmark : ActualSelectedHeightFiniteStripProfile)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon) :
    benchmark.optimalRobustMargin beta ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).optimalRobustMargin beta + epsilon / 2 := by
  let chosen :=
    optimalActualSelectedHeightFiniteStripProfile beta candidates hne
  have hcandidateChosen :
      candidate.effectiveAlphaCeiling beta ≤
        chosen.effectiveAlphaCeiling beta := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_effectiveAlphaCeiling_ge
        beta candidates hne hcandidate
  have hbenchmarkChosen :
      benchmark.effectiveAlphaCeiling beta ≤
        chosen.effectiveAlphaCeiling beta + epsilon := by
    linarith
  have hdifference :=
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_sub_eq_half_ceiling_sub
      beta chosen benchmark
  linarith

/-- On bases at least one, the selected polynomial scale dominates the
benchmark scale after paying the exponent loss `epsilon / 2`. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_balancedPolynomialScale_approximation
    (beta epsilon x : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (benchmark : ActualSelectedHeightFiniteStripProfile)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon)
    (hx : 1 ≤ x) :
    x ^ (benchmark.balancedExponent beta - epsilon / 2) ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).balancedPolynomialScale beta x := by
  apply Real.rpow_le_rpow_of_exponent_le hx
  have hexponent :=
    optimalActualSelectedHeightFiniteStripProfile_balancedExponent_approximation
      beta epsilon candidates hne benchmark hcandidate happrox
  linarith

end PrimeNumberTheorem
