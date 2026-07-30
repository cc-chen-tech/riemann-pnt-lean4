import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileFiniteGridTransfer

/-!
# Automatic directional selection from finite strip grids

A finite grid can support one-sided monotone rounding without exposing the
rounded coordinate functions.  It is enough to certify that every benchmark
`sigma` has a grid value above it and every benchmark `tau` has a grid value
below it.  Classical finite choice then constructs the rounded profile and
feeds it into the zero-loss finite-grid transfer.
-/

namespace PrimeNumberTheorem

/-- Every benchmark `sigma` coordinate has an upper rounding value in the
finite `sigma` grid. -/
def ActualSelectedHeightFiniteStripGrid.SigmaUpperCovers
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma : Fin (grid.stripCount + 1) → ℝ) : Prop :=
  ∀ i, ∃ sigma ∈ grid.sigmaValues, benchmarkSigma i ≤ sigma

/-- Every benchmark `tau` coordinate has a lower rounding value in the
finite `tau` grid. -/
def ActualSelectedHeightFiniteStripGrid.TauLowerCovers
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkTau : Fin (grid.stripCount + 1) → ℝ) : Prop :=
  ∀ i, ∃ tau ∈ grid.tauValues, tau ≤ benchmarkTau i

/-- Select an upper grid rounding for every benchmark `sigma` coordinate. -/
noncomputable def ActualSelectedHeightFiniteStripGrid.upperRoundedSigma
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma : Fin (grid.stripCount + 1) → ℝ)
    (hcoverage : grid.SigmaUpperCovers benchmarkSigma) :
    Fin (grid.stripCount + 1) → ℝ :=
  fun i => Classical.choose (hcoverage i)

/-- The selected upper `sigma` rounding lies in the finite grid. -/
theorem ActualSelectedHeightFiniteStripGrid.upperRoundedSigma_mem
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma : Fin (grid.stripCount + 1) → ℝ)
    (hcoverage : grid.SigmaUpperCovers benchmarkSigma)
    (i : Fin (grid.stripCount + 1)) :
    grid.upperRoundedSigma benchmarkSigma hcoverage i ∈
      grid.sigmaValues :=
  (Classical.choose_spec (hcoverage i)).1

/-- The selected upper `sigma` rounding is no smaller than the benchmark
coordinate. -/
theorem ActualSelectedHeightFiniteStripGrid.le_upperRoundedSigma
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma : Fin (grid.stripCount + 1) → ℝ)
    (hcoverage : grid.SigmaUpperCovers benchmarkSigma)
    (i : Fin (grid.stripCount + 1)) :
    benchmarkSigma i ≤
      grid.upperRoundedSigma benchmarkSigma hcoverage i :=
  (Classical.choose_spec (hcoverage i)).2

/-- Select a lower grid rounding for every benchmark `tau` coordinate. -/
noncomputable def ActualSelectedHeightFiniteStripGrid.lowerRoundedTau
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkTau : Fin (grid.stripCount + 1) → ℝ)
    (hcoverage : grid.TauLowerCovers benchmarkTau) :
    Fin (grid.stripCount + 1) → ℝ :=
  fun i => Classical.choose (hcoverage i)

/-- The selected lower `tau` rounding lies in the finite grid. -/
theorem ActualSelectedHeightFiniteStripGrid.lowerRoundedTau_mem
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkTau : Fin (grid.stripCount + 1) → ℝ)
    (hcoverage : grid.TauLowerCovers benchmarkTau)
    (i : Fin (grid.stripCount + 1)) :
    grid.lowerRoundedTau benchmarkTau hcoverage i ∈ grid.tauValues :=
  (Classical.choose_spec (hcoverage i)).1

/-- The selected lower `tau` rounding is no larger than the benchmark
coordinate. -/
theorem ActualSelectedHeightFiniteStripGrid.lowerRoundedTau_le
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkTau : Fin (grid.stripCount + 1) → ℝ)
    (hcoverage : grid.TauLowerCovers benchmarkTau)
    (i : Fin (grid.stripCount + 1)) :
    grid.lowerRoundedTau benchmarkTau hcoverage i ≤ benchmarkTau i :=
  (Classical.choose_spec (hcoverage i)).2

/-- Directional grid coverage automatically constructs a profile that is a
member of the finite family and monotonically covers the benchmark. -/
theorem
    ActualSelectedHeightFiniteStripGrid.selectedRoundedProfile_mem_and_covers
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma benchmarkTau :
      Fin (grid.stripCount + 1) → ℝ)
    (hsigmaCoverage : grid.SigmaUpperCovers benchmarkSigma)
    (htauCoverage : grid.TauLowerCovers benchmarkTau) :
    grid.profile
        (grid.upperRoundedSigma benchmarkSigma hsigmaCoverage)
        (grid.lowerRoundedTau benchmarkTau htauCoverage) ∈
        grid.profiles ∧
      (grid.profile benchmarkSigma benchmarkTau).MonotoneRoundingCovers
        (grid.profile
          (grid.upperRoundedSigma benchmarkSigma hsigmaCoverage)
          (grid.lowerRoundedTau benchmarkTau htauCoverage)) :=
  grid.roundedProfile_mem_and_covers
    benchmarkSigma benchmarkTau
    (grid.upperRoundedSigma benchmarkSigma hsigmaCoverage)
    (grid.lowerRoundedTau benchmarkTau htauCoverage)
    (grid.upperRoundedSigma_mem benchmarkSigma hsigmaCoverage)
    (grid.lowerRoundedTau_mem benchmarkTau htauCoverage)
    (grid.le_upperRoundedSigma benchmarkSigma hsigmaCoverage)
    (grid.lowerRoundedTau_le benchmarkTau htauCoverage)

/-- A directionally covering finite grid runs the zero-loss optimal unified
transfer without explicit rounded coordinate functions.

The target-cluster witness `hmain` and the actual analytic bucket input for
the selected profile remain explicit hypotheses. -/
theorem
    unified_actualBalancedHeight_of_directionallyCoveringFiniteStripGrid
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma benchmarkTau :
      Fin (grid.stripCount + 1) → ℝ)
    (hsigmaCoverage : grid.SigmaUpperCovers benchmarkSigma)
    (htauCoverage : grid.TauLowerCovers benchmarkTau)
    (hbenchmarkHalf : ∀ i, 1 / 2 < benchmarkSigma i)
    (hbenchmarkTau : ∀ i, benchmarkTau i ≤ beta)
    (hbenchmarkMargin :
      0 <
        (grid.profile benchmarkSigma benchmarkTau).optimalRobustMargin beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripBalancedHeight
            beta
            (optimalActualSelectedHeightFiniteStripProfile
              beta grid.profiles grid.profiles_nonempty).sigma
            (optimalActualSelectedHeightFiniteStripProfile
              beta grid.profiles grid.profiles_nonempty).tau
            selection x)
          S
          ((optimalActualSelectedHeightFiniteStripProfile
              beta grid.profiles grid.profiles_nonempty).stripCount + 1))
    (kappa :
      Fin ((optimalActualSelectedHeightFiniteStripProfile
        beta grid.profiles grid.profiles_nonempty).stripCount + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma :
      ∀ i x,
        (input x).sigma i =
          (optimalActualSelectedHeightFiniteStripProfile
            beta grid.profiles grid.profiles_nonempty).sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i,
        rho.re ≤
          (optimalActualSelectedHeightFiniteStripProfile
            beta grid.profiles grid.profiles_nonempty).tau i)
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
                beta grid.profiles grid.profiles_nonempty).sigma
              (optimalActualSelectedHeightFiniteStripProfile
                beta grid.profiles grid.profiles_nonempty).tau
              selection)
            S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    let benchmark := grid.profile benchmarkSigma benchmarkTau
    let chosen :=
      optimalActualSelectedHeightFiniteStripProfile
        beta grid.profiles grid.profiles_nonempty
    (chosen ∈ grid.profiles ∧
        (∀ profile ∈ grid.profiles,
          profile.optimalRobustMargin beta ≤
            chosen.optimalRobustMargin beta) ∧
        chosen.HasUnifiedTransferResult beta) ∧
      benchmark.balancedExponent beta ≤
        chosen.balancedExponent beta ∧
      benchmark.optimalRobustMargin beta ≤
        chosen.optimalRobustMargin beta ∧
      ∀ x : ℝ, 1 ≤ x →
        benchmark.balancedPolynomialScale beta x ≤
          chosen.balancedPolynomialScale beta x :=
  unified_actualBalancedHeight_of_finiteMonotoneStripGrid
    threshold hhalf hlt hbeta hbetaOne grid
    benchmarkSigma benchmarkTau
    (grid.upperRoundedSigma benchmarkSigma hsigmaCoverage)
    (grid.lowerRoundedTau benchmarkTau htauCoverage)
    (grid.upperRoundedSigma_mem benchmarkSigma hsigmaCoverage)
    (grid.lowerRoundedTau_mem benchmarkTau htauCoverage)
    hbenchmarkHalf hbenchmarkTau
    (grid.le_upperRoundedSigma benchmarkSigma hsigmaCoverage)
    (grid.lowerRoundedTau_le benchmarkTau htauCoverage)
    hbenchmarkMargin selection input kappa hS hfixedSigma
    hkappa hnorm hre hreal hmain

end PrimeNumberTheorem
