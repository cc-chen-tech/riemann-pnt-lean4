import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileCoverageTransfer

/-!
# Zero-loss transfer under monotone strip-parameter rounding

For an admissible Carlson strip, the selected-height alpha ceiling is

`(beta - tau) / (4 * sigma * (1 - sigma))`.

On the interval `1 / 2 < sigma < 1`, increasing `sigma` decreases the
positive denominator, while decreasing `tau` increases the nonnegative
numerator.  Thus a one-sided finite-grid rounding can improve every local
ceiling rather than merely approximate it.  This produces a zero-error
stripwise coverage certificate and therefore a zero-loss unified transfer.
-/

namespace PrimeNumberTheorem

/-- Increasing `sigma` and decreasing `tau` cannot lower the local alpha
ceiling in the admissible right half-strip, provided `tau ≤ beta`. -/
theorem actualSelectedHeightStripAlphaCeiling_mono_of_monotoneRounding
    (beta benchmarkSigma benchmarkTau candidateSigma candidateTau : ℝ)
    (hbenchmarkHalf : 1 / 2 < benchmarkSigma)
    (hsigma : benchmarkSigma ≤ candidateSigma)
    (hcandidateOne : candidateSigma < 1)
    (htau : candidateTau ≤ benchmarkTau)
    (hbenchmarkTau : benchmarkTau ≤ beta) :
    actualSelectedHeightStripAlphaCeiling
        beta benchmarkSigma benchmarkTau ≤
      actualSelectedHeightStripAlphaCeiling
        beta candidateSigma candidateTau := by
  have hcandidateSigmaPos : 0 < candidateSigma := by
    linarith
  have hcandidateGapPos : 0 < 1 - candidateSigma := by
    linarith
  have hcandidateDenominator :
      0 < 4 * candidateSigma * (1 - candidateSigma) := by
    positivity
  have hdenominatorMono :
      4 * candidateSigma * (1 - candidateSigma) ≤
        4 * benchmarkSigma * (1 - benchmarkSigma) := by
    nlinarith
  have hcandidateNumerator : 0 ≤ beta - candidateTau := by
    linarith
  have hnumeratorMono :
      beta - benchmarkTau ≤ beta - candidateTau := by
    linarith
  unfold actualSelectedHeightStripAlphaCeiling
  exact
    div_le_div₀ hcandidateNumerator hnumeratorMono
      hcandidateDenominator hdenominatorMono

/-- A candidate profile monotonically rounds a benchmark when every
candidate strip is obtained from some benchmark strip by moving `sigma`
rightward and `tau` downward.  Strip counts may differ. -/
def
    ActualSelectedHeightFiniteStripProfile.MonotoneRoundingCovers
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile) : Prop :=
  ∀ j, ∃ i,
    benchmark.sigma i ≤ candidate.sigma j ∧
      candidate.tau j ≤ benchmark.tau i

/-- Monotone parameter rounding is reflexive. -/
theorem monotoneRoundingCovers_refl
    (profile : ActualSelectedHeightFiniteStripProfile) :
    profile.MonotoneRoundingCovers profile := by
  intro j
  exact ⟨j, le_rfl, le_rfl⟩

/-- Monotone parameter rounding composes across profiles with unrelated
strip counts. -/
theorem monotoneRoundingCovers_trans
    {benchmark middle candidate :
      ActualSelectedHeightFiniteStripProfile}
    (hleft : benchmark.MonotoneRoundingCovers middle)
    (hright : middle.MonotoneRoundingCovers candidate) :
    benchmark.MonotoneRoundingCovers candidate := by
  intro j
  obtain ⟨i, hsigmaRight, htauRight⟩ := hright j
  obtain ⟨k, hsigmaLeft, htauLeft⟩ := hleft i
  exact
    ⟨k, le_trans hsigmaLeft hsigmaRight,
      le_trans htauRight htauLeft⟩

/-- Admissible monotone parameter rounding gives a zero-error stripwise
alpha-ceiling coverage certificate. -/
theorem
    stripAlphaCeilingCoversWithin_zero_of_monotoneRoundingCovers
    (beta : ℝ)
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile)
    (hbenchmarkHalf : ∀ i, 1 / 2 < benchmark.sigma i)
    (hcandidateOne : ∀ j, candidate.sigma j < 1)
    (hbenchmarkTau : ∀ i, benchmark.tau i ≤ beta)
    (hrounding : benchmark.MonotoneRoundingCovers candidate) :
    benchmark.StripAlphaCeilingCoversWithin candidate beta 0 := by
  intro j
  obtain ⟨i, hsigma, htau⟩ := hrounding j
  refine ⟨i, ?_⟩
  simpa using
    actualSelectedHeightStripAlphaCeiling_mono_of_monotoneRounding
      beta (benchmark.sigma i) (benchmark.tau i)
      (candidate.sigma j) (candidate.tau j)
      (hbenchmarkHalf i) hsigma (hcandidateOne j) htau
      (hbenchmarkTau i)

/-- A finite family containing an admissible monotone rounding of a
positive-margin benchmark contains a feasible profile. -/
theorem
    exists_feasibleActualSelectedHeightFiniteStripProfile_of_monotoneRounding
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (benchmark : ActualSelectedHeightFiniteStripProfile)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (hbenchmarkHalf : ∀ i, 1 / 2 < benchmark.sigma i)
    (hbenchmarkTau : ∀ i, benchmark.tau i ≤ beta)
    (hrounding : benchmark.MonotoneRoundingCovers candidate)
    (hbenchmarkMargin :
      0 < benchmark.optimalRobustMargin beta) :
    ∃ profile ∈ candidates, profile.IsFeasible beta := by
  have hcoverage :
      benchmark.StripAlphaCeilingCoversWithin candidate beta 0 :=
    stripAlphaCeilingCoversWithin_zero_of_monotoneRoundingCovers
      beta benchmark candidate hbenchmarkHalf
      (hsigmaOne candidate hcandidate) hbenchmarkTau hrounding
  have hradius :
      (0 : ℝ) < 2 * benchmark.optimalRobustMargin beta := by
    linarith
  exact
    exists_feasibleActualSelectedHeightFiniteStripProfile_of_stripAlphaCeilingCoverage
      beta 0 candidates benchmark hcandidate hsigma hsigmaOne
      le_rfl hcoverage hradius

/-- One-sided finite-grid rounding gives the selected profile the full
benchmark exponent, robust margin, and polynomial scale with no
approximation loss, while running the existing conditional unified
Pintz--Carlson--explicit-formula transfer.

The target-cluster witness `hmain` remains an explicit hypothesis. -/
theorem unified_actualBalancedHeight_of_monotoneRoundedStripProfile
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (benchmark : ActualSelectedHeightFiniteStripProfile)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (hbenchmarkHalf : ∀ i, 1 / 2 < benchmark.sigma i)
    (hbenchmarkTau : ∀ i, benchmark.tau i ≤ beta)
    (hrounding : benchmark.MonotoneRoundingCovers candidate)
    (hbenchmarkMargin :
      0 < benchmark.optimalRobustMargin beta)
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
        chosen.balancedExponent beta ∧
      benchmark.optimalRobustMargin beta ≤
        chosen.optimalRobustMargin beta ∧
      ∀ x : ℝ, 1 ≤ x →
        benchmark.balancedPolynomialScale beta x ≤
          chosen.balancedPolynomialScale beta x := by
  have hcoverage :
      benchmark.StripAlphaCeilingCoversWithin candidate beta 0 :=
    stripAlphaCeilingCoversWithin_zero_of_monotoneRoundingCovers
      beta benchmark candidate hbenchmarkHalf
      (hsigmaOne candidate hcandidate) hbenchmarkTau hrounding
  have hradius :
      (0 : ℝ) < 2 * benchmark.optimalRobustMargin beta := by
    linarith
  dsimp only
  obtain ⟨hresult, hbalanced, hmargin, hscale⟩ :=
    unified_actualBalancedHeight_of_stripAlphaCeilingCoverage
      (beta := beta) (epsilon := 0)
      threshold hhalf hlt hbeta hbetaOne candidates hne benchmark
      hcandidate hsigma hsigmaOne le_rfl hcoverage hradius
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal hmain
  refine ⟨hresult, ?_, ?_, ?_⟩
  · simpa only [zero_div, add_zero] using hbalanced
  · simpa only [zero_div, add_zero] using hmargin
  intro x hx
  change x ^ benchmark.balancedExponent beta ≤ _
  simpa only [zero_div, sub_zero] using hscale x hx

end PrimeNumberTheorem
