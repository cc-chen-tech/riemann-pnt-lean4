import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileApproximateFeasibility

/-!
# Unified transfer from an approximate finite strip profile

A finite family need not contain the benchmark profile itself.  It is enough
to contain one profile whose effective alpha ceiling approximates the
benchmark within a radius smaller than twice the benchmark robust margin.
The finite optimizer then supports the existing Pintz--Carlson--explicit
formula transfer while losing at most `epsilon / 2` in balanced exponent and
robust margin.
-/

namespace PrimeNumberTheorem

/-- A sufficiently accurate finite approximation to a benchmark profile
simultaneously supplies:

* the full conditional upper/lower unified transfer for the selected profile;
* optimal robust margin inside the finite candidate family;
* `epsilon / 2` approximation guarantees for the benchmark exponent and
  robust margin;
* the corresponding lower bound for the selected polynomial scale.

The oscillation input `hmain` remains an explicit hypothesis. -/
theorem
    unified_actualBalancedHeight_of_approximateOptimalFiniteStripProfile
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
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
      epsilon < 2 * benchmark.optimalRobustMargin beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripBalancedHeight
            beta
            (optimalActualSelectedHeightFiniteStripProfile
              beta candidates hne).sigma
            (optimalActualSelectedHeightFiniteStripProfile
              beta candidates hne).tau
            selection x)
          S
          ((optimalActualSelectedHeightFiniteStripProfile
              beta candidates hne).stripCount + 1))
    (kappa :
      Fin ((optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).stripCount + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma :
      ∀ i x,
        (input x).sigma i =
          (optimalActualSelectedHeightFiniteStripProfile
            beta candidates hne).sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i,
        rho.re ≤
          (optimalActualSelectedHeightFiniteStripProfile
            beta candidates hne).tau i)
    (hreal :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripBalancedHeight
              beta
              (optimalActualSelectedHeightFiniteStripProfile
                beta candidates hne).sigma
              (optimalActualSelectedHeightFiniteStripProfile
                beta candidates hne).tau
              selection)
            S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    let chosen :=
      optimalActualSelectedHeightFiniteStripProfile beta candidates hne
    (chosen ∈ candidates ∧
        (∀ profile ∈ candidates,
          profile.optimalRobustMargin beta ≤
            chosen.optimalRobustMargin beta) ∧
        chosen.HasUnifiedTransferResult beta) ∧
      benchmark.balancedExponent beta ≤
        chosen.balancedExponent beta + epsilon / 2 ∧
      benchmark.optimalRobustMargin beta ≤
        chosen.optimalRobustMargin beta + epsilon / 2 ∧
      ∀ x : ℝ, 1 ≤ x →
        x ^ (benchmark.balancedExponent beta - epsilon / 2) ≤
          chosen.balancedPolynomialScale beta x := by
  let chosen :=
    optimalActualSelectedHeightFiniteStripProfile beta candidates hne
  have hexistsFeasible :
      ∃ profile ∈ candidates, profile.IsFeasible beta :=
    exists_feasibleActualSelectedHeightFiniteStripProfile_of_approximation
      beta epsilon candidates benchmark hcandidate hsigma hsigmaOne
      happrox hepsilon
  have htransfer :
      chosen ∈ candidates ∧
        (∀ profile ∈ candidates,
          profile.optimalRobustMargin beta ≤
            chosen.optimalRobustMargin beta) ∧
        chosen.HasUnifiedTransferResult beta := by
    simpa [chosen] using
      unified_actualBalancedHeight_of_optimalFiniteStripProfile_of_exists_feasible
        threshold hhalf hlt hbeta hbetaOne candidates hne
        hsigma hsigmaOne hexistsFeasible selection input kappa hS
        hfixedSigma hkappa hnorm hre hreal hmain
  have hexponent :
      benchmark.balancedExponent beta ≤
        chosen.balancedExponent beta + epsilon / 2 := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_balancedExponent_approximation
        beta epsilon candidates hne benchmark hcandidate happrox
  have hmargin :
      benchmark.optimalRobustMargin beta ≤
        chosen.optimalRobustMargin beta + epsilon / 2 := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_approximation
        beta epsilon candidates hne benchmark hcandidate happrox
  have hscale :
      ∀ x : ℝ, 1 ≤ x →
        x ^ (benchmark.balancedExponent beta - epsilon / 2) ≤
          chosen.balancedPolynomialScale beta x := by
    intro x hx
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_balancedPolynomialScale_approximation
        beta epsilon x candidates hne benchmark hcandidate happrox hx
  exact ⟨htransfer, hexponent, hmargin, hscale⟩

end PrimeNumberTheorem
