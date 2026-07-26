import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileFiniteGridDirectionalSelection

/-!
# Extremal directional selection from finite strip grids

Nonempty finite grids have an actual maximum `sigma` and minimum `tau`.
These two elements provide uniform one-sided rounding witnesses for every
benchmark strip whose coordinates lie between the corresponding bounds.
Thus the existential directional coverage inputs can be replaced by direct
inequalities against computable finite-grid extrema.
-/

namespace PrimeNumberTheorem

/-- The largest available `sigma` grid value. -/
noncomputable def ActualSelectedHeightFiniteStripGrid.maxSigma
    (grid : ActualSelectedHeightFiniteStripGrid) : ℝ :=
  grid.sigmaValues.max' grid.sigmaValues_nonempty

/-- The smallest available `tau` grid value. -/
noncomputable def ActualSelectedHeightFiniteStripGrid.minTau
    (grid : ActualSelectedHeightFiniteStripGrid) : ℝ :=
  grid.tauValues.min' grid.tauValues_nonempty

/-- The maximum `sigma` is an actual grid value. -/
theorem ActualSelectedHeightFiniteStripGrid.maxSigma_mem
    (grid : ActualSelectedHeightFiniteStripGrid) :
    grid.maxSigma ∈ grid.sigmaValues :=
  Finset.max'_mem grid.sigmaValues grid.sigmaValues_nonempty

/-- The minimum `tau` is an actual grid value. -/
theorem ActualSelectedHeightFiniteStripGrid.minTau_mem
    (grid : ActualSelectedHeightFiniteStripGrid) :
    grid.minTau ∈ grid.tauValues :=
  Finset.min'_mem grid.tauValues grid.tauValues_nonempty

/-- A coordinatewise upper bound by the grid maximum produces the required
`sigma` directional coverage. -/
theorem ActualSelectedHeightFiniteStripGrid.sigmaUpperCovers_of_le_maxSigma
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma : Fin (grid.stripCount + 1) → ℝ)
    (hbound : ∀ i, benchmarkSigma i ≤ grid.maxSigma) :
    grid.SigmaUpperCovers benchmarkSigma := by
  intro i
  exact ⟨grid.maxSigma, grid.maxSigma_mem, hbound i⟩

/-- A coordinatewise lower bound by the grid minimum produces the required
`tau` directional coverage. -/
theorem ActualSelectedHeightFiniteStripGrid.tauLowerCovers_of_minTau_le
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkTau : Fin (grid.stripCount + 1) → ℝ)
    (hbound : ∀ i, grid.minTau ≤ benchmarkTau i) :
    grid.TauLowerCovers benchmarkTau := by
  intro i
  exact ⟨grid.minTau, grid.minTau_mem, hbound i⟩

/-- Finite-grid extremal bounds run the zero-loss optimal unified transfer.
No candidate family, rounded coordinate function, or existential directional
coverage witness is supplied externally.

The target-cluster witness `hmain` and the actual analytic bucket input for
the selected profile remain explicit hypotheses. -/
theorem
    unified_actualBalancedHeight_of_extremalFiniteStripGridBounds
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma benchmarkTau :
      Fin (grid.stripCount + 1) → ℝ)
    (hbenchmarkSigmaMax : ∀ i, benchmarkSigma i ≤ grid.maxSigma)
    (hminTauBenchmark : ∀ i, grid.minTau ≤ benchmarkTau i)
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
  unified_actualBalancedHeight_of_directionallyCoveringFiniteStripGrid
    threshold hhalf hlt hbeta hbetaOne grid
    benchmarkSigma benchmarkTau
    (grid.sigmaUpperCovers_of_le_maxSigma
      benchmarkSigma hbenchmarkSigmaMax)
    (grid.tauLowerCovers_of_minTau_le
      benchmarkTau hminTauBenchmark)
    hbenchmarkHalf hbenchmarkTau hbenchmarkMargin
    selection input kappa hS hfixedSigma hkappa hnorm hre hreal hmain

end PrimeNumberTheorem
