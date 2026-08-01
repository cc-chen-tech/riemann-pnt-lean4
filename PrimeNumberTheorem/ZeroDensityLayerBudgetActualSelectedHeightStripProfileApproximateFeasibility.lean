import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileApproximation

/-!
# Feasibility radius for approximate finite strip profiles

A benchmark profile with positive balanced robust margin remains analytically
usable after finite discretization, provided the effective-ceiling error is
smaller than twice that margin.  This turns an approximation certificate into
the existential feasible-candidate input required by the unified transfer.
-/

namespace PrimeNumberTheorem

/-- Effective-ceiling approximation gives the same `epsilon / 2` lower bound
for the approximating candidate's robust margin. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_approximation
    (beta epsilon : ℝ)
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile)
    (happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon) :
    benchmark.optimalRobustMargin beta ≤
      candidate.optimalRobustMargin beta + epsilon / 2 := by
  have hdifference :=
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_sub_eq_half_ceiling_sub
      beta candidate benchmark
  linarith

/-- If the ceiling approximation error is smaller than twice the benchmark
margin, the approximating candidate still has positive margin. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_pos_of_approximation
    (beta epsilon : ℝ)
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile)
    (happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon)
    (hepsilon :
      epsilon < 2 * benchmark.optimalRobustMargin beta) :
    0 < candidate.optimalRobustMargin beta := by
  have hmargin :=
    benchmark.optimalRobustMargin_approximation
      beta epsilon candidate happrox
  linarith

/-- A sufficiently accurate approximation to a positive-margin benchmark is
a feasible finite strip profile. -/
theorem
    ActualSelectedHeightFiniteStripProfile.isFeasible_of_approximation
    (beta epsilon : ℝ)
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile)
    (hcandidateSigma : ∀ i, 1 / 2 < candidate.sigma i)
    (hcandidateSigmaOne : ∀ i, candidate.sigma i < 1)
    (happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon)
    (hepsilon :
      epsilon < 2 * benchmark.optimalRobustMargin beta) :
    candidate.IsFeasible beta :=
  candidate.isFeasible_of_optimalRobustMargin_pos
    hcandidateSigma hcandidateSigmaOne
    (benchmark.optimalRobustMargin_pos_of_approximation
      beta epsilon candidate happrox hepsilon)

/-- A finite candidate family containing a sufficiently accurate approximation
to a positive-margin benchmark contains a feasible profile.  This is the
existential certificate consumed by
`unified_actualBalancedHeight_of_optimalFiniteStripProfile_of_exists_feasible`.
-/
theorem
    exists_feasibleActualSelectedHeightFiniteStripProfile_of_approximation
    (beta epsilon : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (benchmark : ActualSelectedHeightFiniteStripProfile)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon)
    (hepsilon :
      epsilon < 2 * benchmark.optimalRobustMargin beta) :
    ∃ profile ∈ candidates, profile.IsFeasible beta :=
  ⟨candidate, hcandidate,
    benchmark.isFeasible_of_approximation
      beta epsilon candidate
      (hsigma candidate hcandidate)
      (hsigmaOne candidate hcandidate)
      happrox hepsilon⟩

/-- Under the same approximation radius, the finite optimizer selects a
feasible profile. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_feasible_of_approximation
    {beta epsilon : ℝ} (hbeta : 0 < beta)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (benchmark : ActualSelectedHeightFiniteStripProfile)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon)
    (hepsilon :
      epsilon < 2 * benchmark.optimalRobustMargin beta) :
    (optimalActualSelectedHeightFiniteStripProfile
      beta candidates hne).IsFeasible beta :=
  optimalActualSelectedHeightFiniteStripProfile_feasible_of_exists
    hbeta candidates hne hsigma hsigmaOne
    (exists_feasibleActualSelectedHeightFiniteStripProfile_of_approximation
      beta epsilon candidates benchmark hcandidate hsigma hsigmaOne
      happrox hepsilon)

end PrimeNumberTheorem
