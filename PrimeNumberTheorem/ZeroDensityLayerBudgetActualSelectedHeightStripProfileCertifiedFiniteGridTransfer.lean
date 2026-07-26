import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileCertifiedMonotoneTransfer

/-!
# Certified optimization over concrete finite strip grids

The canonical extremal grid profile uses the largest available `sigma` and
smallest available `tau` in every strip.  It is automatically a member of
the finite grid family and monotonically covers every benchmark satisfying
the corresponding extremal bounds.

One actual analytic certificate for this canonical profile is therefore
enough to make the certified grid family nonempty.  Optimization then takes
place only among grid profiles with complete certificates.
-/

namespace PrimeNumberTheorem

/-- The canonical profile using the most favorable one-sided grid extrema
in every strip. -/
noncomputable def ActualSelectedHeightFiniteStripGrid.extremalProfile
    (grid : ActualSelectedHeightFiniteStripGrid) :
    ActualSelectedHeightFiniteStripProfile :=
  grid.profile (fun _ => grid.maxSigma) (fun _ => grid.minTau)

/-- The canonical extremal profile is an actual member of the finite grid
family. -/
theorem ActualSelectedHeightFiniteStripGrid.extremalProfile_mem
    (grid : ActualSelectedHeightFiniteStripGrid) :
    grid.extremalProfile ∈ grid.profiles := by
  apply
    (grid.profile_mem_profiles_iff
      (fun _ => grid.maxSigma) (fun _ => grid.minTau)).2
  exact ⟨fun _ => grid.maxSigma_mem, fun _ => grid.minTau_mem⟩

/-- Benchmark bounds by the grid extrema imply monotone coverage by the
canonical extremal profile. -/
theorem
    ActualSelectedHeightFiniteStripGrid.monotoneRoundingCovers_extremalProfile
    (grid : ActualSelectedHeightFiniteStripGrid)
    (benchmarkSigma benchmarkTau :
      Fin (grid.stripCount + 1) → ℝ)
    (hbenchmarkSigmaMax : ∀ i, benchmarkSigma i ≤ grid.maxSigma)
    (hminTauBenchmark : ∀ i, grid.minTau ≤ benchmarkTau i) :
    (grid.profile benchmarkSigma benchmarkTau).MonotoneRoundingCovers
      grid.extremalProfile := by
  intro j
  exact ⟨j, hbenchmarkSigmaMax j, hminTauBenchmark j⟩

/-- A single actual certificate for the canonical extremal grid profile
starts certified optimization over the whole finite grid.

The selected profile is optimal among all certified grid profiles, carries
the full unified transfer result, and preserves the benchmark exponent,
robust margin, and polynomial scale without discretization loss. -/
theorem
    unified_actualBalancedHeight_of_certifiedExtremalFiniteStripGrid
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (grid : ActualSelectedHeightFiniteStripGrid)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ)
    (benchmarkSigma benchmarkTau :
      Fin (grid.stripCount + 1) → ℝ)
    (hbenchmarkSigmaMax : ∀ i, benchmarkSigma i ≤ grid.maxSigma)
    (hminTauBenchmark : ∀ i, grid.minTau ≤ benchmarkTau i)
    (hbenchmarkHalf : ∀ i, 1 / 2 < benchmarkSigma i)
    (hbenchmarkTau : ∀ i, benchmarkTau i ≤ beta)
    (extremalCertificate :
      grid.extremalProfile.AnalyticTransferCertificate
        beta selection S) :
    let benchmark := grid.profile benchmarkSigma benchmarkTau
    let candidate := grid.extremalProfile
    let certified :=
      analyticTransferCertifiedProfiles
        beta selection S grid.profiles
    let hexists :
        ∃ profile ∈ grid.profiles,
          profile.HasAnalyticTransferCertificate beta selection S :=
      ⟨candidate, grid.extremalProfile_mem, ⟨extremalCertificate⟩⟩
    let hne :=
      analyticTransferCertifiedProfiles_nonempty
        beta selection S grid.profiles hexists
    let chosen :=
      optimalActualSelectedHeightFiniteStripProfile beta certified hne
    (chosen ∈ grid.profiles ∧
        chosen.HasAnalyticTransferCertificate beta selection S ∧
        (∀ profile ∈ grid.profiles,
          profile.HasAnalyticTransferCertificate beta selection S →
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
  let benchmark := grid.profile benchmarkSigma benchmarkTau
  let candidate := grid.extremalProfile
  have hrounding :
      benchmark.MonotoneRoundingCovers candidate := by
    simpa [benchmark, candidate] using
      grid.monotoneRoundingCovers_extremalProfile
        benchmarkSigma benchmarkTau
        hbenchmarkSigmaMax hminTauBenchmark
  have hbenchmarkHalf' : ∀ i, 1 / 2 < benchmark.sigma i := by
    simpa [benchmark] using hbenchmarkHalf
  have hbenchmarkTau' : ∀ i, benchmark.tau i ≤ beta := by
    simpa [benchmark] using hbenchmarkTau
  simpa [benchmark, candidate] using
    unified_actualBalancedHeight_of_optimalCertifiedMonotoneStripProfile
      threshold hhalf hlt hbeta hbetaOne
      grid.profiles selection S benchmark candidate
      grid.extremalProfile_mem extremalCertificate
      hbenchmarkHalf' hbenchmarkTau' hrounding

end PrimeNumberTheorem
