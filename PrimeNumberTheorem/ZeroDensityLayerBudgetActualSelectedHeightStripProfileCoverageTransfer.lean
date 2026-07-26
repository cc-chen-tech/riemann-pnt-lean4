import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileApproximateTransfer

/-!
# Stripwise coverage certificates for approximate unified transfer

The effective alpha ceiling of a finite strip profile is a finite minimum.
Consequently, a global approximation certificate can be generated from a
local directed coverage condition, even when the benchmark and candidate
profiles have different numbers of strips.

Each candidate strip must be covered by some benchmark strip whose local
alpha ceiling is no larger than the candidate ceiling plus `epsilon`.  The
candidate's minimizing strip then supplies the global approximation needed
by the finite-profile unified transfer.
-/

namespace PrimeNumberTheorem

/-- Directed stripwise coverage within additive alpha-ceiling error.

The direction is chosen so that every candidate strip, including its
minimizing strip, has a benchmark witness.  The two profiles may have
different strip counts. -/
def
    ActualSelectedHeightFiniteStripProfile.StripAlphaCeilingCoversWithin
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile)
    (beta epsilon : ℝ) : Prop :=
  ∀ j, ∃ i,
    actualSelectedHeightStripAlphaCeiling
        beta (benchmark.sigma i) (benchmark.tau i) ≤
      actualSelectedHeightStripAlphaCeiling
          beta (candidate.sigma j) (candidate.tau j) +
        epsilon

/-- Stripwise coverage is reflexive at zero error. -/
theorem stripAlphaCeilingCoversWithin_refl
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) :
    profile.StripAlphaCeilingCoversWithin profile beta 0 := by
  intro j
  exact ⟨j, by simp⟩

/-- A stripwise coverage certificate remains valid after increasing its
allowed error. -/
theorem stripAlphaCeilingCoversWithin_mono
    {beta epsilon delta : ℝ}
    {benchmark candidate : ActualSelectedHeightFiniteStripProfile}
    (hcoverage :
      benchmark.StripAlphaCeilingCoversWithin candidate beta epsilon)
    (herror : epsilon ≤ delta) :
    benchmark.StripAlphaCeilingCoversWithin candidate beta delta := by
  intro j
  obtain ⟨i, hi⟩ := hcoverage j
  refine ⟨i, ?_⟩
  linarith

/-- Directed stripwise coverage composes, with additive errors, across
profiles of unrelated cardinalities. -/
theorem stripAlphaCeilingCoversWithin_trans
    {beta epsilon delta : ℝ}
    {benchmark middle candidate :
      ActualSelectedHeightFiniteStripProfile}
    (hleft :
      benchmark.StripAlphaCeilingCoversWithin middle beta epsilon)
    (hright :
      middle.StripAlphaCeilingCoversWithin candidate beta delta) :
    benchmark.StripAlphaCeilingCoversWithin
      candidate beta (epsilon + delta) := by
  intro j
  obtain ⟨i, hi⟩ := hright j
  obtain ⟨k, hk⟩ := hleft i
  refine ⟨k, ?_⟩
  linarith

/-- Directed stripwise coverage controls the finite minimum defining the
unclipped profile alpha ceiling. -/
theorem alphaCeiling_approximation_of_stripAlphaCeilingCoverage
    (beta epsilon : ℝ)
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile)
    (hcoverage :
      benchmark.StripAlphaCeilingCoversWithin candidate beta epsilon) :
    benchmark.alphaCeiling beta ≤
      candidate.alphaCeiling beta + epsilon := by
  classical
  let benchmarkCeilings : Finset ℝ :=
    Finset.image
      (fun i =>
        actualSelectedHeightStripAlphaCeiling
          beta (benchmark.sigma i) (benchmark.tau i))
      Finset.univ
  let candidateCeilings : Finset ℝ :=
    Finset.image
      (fun j =>
        actualSelectedHeightStripAlphaCeiling
          beta (candidate.sigma j) (candidate.tau j))
      Finset.univ
  have hbenchmarkNonempty : benchmarkCeilings.Nonempty := by
    simp [benchmarkCeilings]
  have hcandidateNonempty : candidateCeilings.Nonempty := by
    simp [candidateCeilings]
  have hcandidateMinMem :
      candidateCeilings.min' hcandidateNonempty ∈ candidateCeilings :=
    Finset.min'_mem candidateCeilings hcandidateNonempty
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hcandidateMinMem
  obtain ⟨i, hi⟩ := hcoverage j
  have hbenchmarkMin :
      benchmarkCeilings.min' hbenchmarkNonempty ≤
        actualSelectedHeightStripAlphaCeiling
          beta (benchmark.sigma i) (benchmark.tau i) := by
    apply Finset.min'_le
    simp [benchmarkCeilings]
  have hcandidateEq :
      actualSelectedHeightStripAlphaCeiling
          beta (candidate.sigma j) (candidate.tau j) =
        candidateCeilings.min' hcandidateNonempty := by
    simpa [candidateCeilings] using hj
  have hminimumApproximation :
      benchmarkCeilings.min' hbenchmarkNonempty ≤
        candidateCeilings.min' hcandidateNonempty + epsilon := by
    linarith
  simpa [ActualSelectedHeightFiniteStripProfile.alphaCeiling,
    actualSelectedHeightFiniteStripAlphaCeiling,
    benchmarkCeilings, candidateCeilings] using hminimumApproximation

/-- For nonnegative error, stripwise coverage also controls the effective
alpha ceiling obtained by clipping the finite minimum at one. -/
theorem effectiveAlphaCeiling_approximation_of_stripAlphaCeilingCoverage
    (beta epsilon : ℝ)
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile)
    (hepsilonNonneg : 0 ≤ epsilon)
    (hcoverage :
      benchmark.StripAlphaCeilingCoversWithin candidate beta epsilon) :
    benchmark.effectiveAlphaCeiling beta ≤
      candidate.effectiveAlphaCeiling beta + epsilon := by
  have hraw :=
    alphaCeiling_approximation_of_stripAlphaCeilingCoverage
      beta epsilon benchmark candidate hcoverage
  change min 1 (benchmark.alphaCeiling beta) ≤
    min 1 (candidate.alphaCeiling beta) + epsilon
  by_cases hcandidate : 1 ≤ candidate.alphaCeiling beta
  · rw [min_eq_left hcandidate]
    have hclipped : min 1 (benchmark.alphaCeiling beta) ≤ 1 :=
      min_le_left _ _
    linarith
  · have hcandidateOne : candidate.alphaCeiling beta ≤ 1 :=
      le_of_not_ge hcandidate
    rw [min_eq_right hcandidateOne]
    exact le_trans (min_le_right _ _) hraw

/-- A stripwise approximation inside the benchmark feasibility radius
produces the existential feasible candidate required by the optimizer. -/
theorem
    exists_feasibleActualSelectedHeightFiniteStripProfile_of_stripAlphaCeilingCoverage
    (beta epsilon : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (benchmark : ActualSelectedHeightFiniteStripProfile)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (hepsilonNonneg : 0 ≤ epsilon)
    (hcoverage :
      benchmark.StripAlphaCeilingCoversWithin candidate beta epsilon)
    (hradius :
      epsilon < 2 * benchmark.optimalRobustMargin beta) :
    ∃ profile ∈ candidates, profile.IsFeasible beta :=
  exists_feasibleActualSelectedHeightFiniteStripProfile_of_approximation
    beta epsilon candidates benchmark hcandidate hsigma hsigmaOne
    (effectiveAlphaCeiling_approximation_of_stripAlphaCeilingCoverage
      beta epsilon benchmark candidate hepsilonNonneg hcoverage)
    hradius

/-- Local stripwise coverage is sufficient to run the approximate optimal
finite-profile Pintz--Carlson--explicit-formula transfer.

The target-cluster oscillation witness remains the explicit hypothesis
`hmain`; this theorem does not assert an unconditional omega result. -/
theorem unified_actualBalancedHeight_of_stripAlphaCeilingCoverage
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
    (hepsilonNonneg : 0 ≤ epsilon)
    (hcoverage :
      benchmark.StripAlphaCeilingCoversWithin candidate beta epsilon)
    (hradius :
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
  have happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + epsilon :=
    effectiveAlphaCeiling_approximation_of_stripAlphaCeilingCoverage
      beta epsilon benchmark candidate hepsilonNonneg hcoverage
  exact
    unified_actualBalancedHeight_of_approximateOptimalFiniteStripProfile
      threshold hhalf hlt hbeta hbetaOne candidates hne benchmark
      hcandidate hsigma hsigmaOne happrox hradius selection input kappa hS
      hfixedSigma hkappa hnorm hre hreal hmain

end PrimeNumberTheorem
