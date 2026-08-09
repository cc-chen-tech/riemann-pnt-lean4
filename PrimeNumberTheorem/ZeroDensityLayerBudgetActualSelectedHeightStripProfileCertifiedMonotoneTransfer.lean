import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileCertifiedOptimization

/-!
# Zero-loss benchmark transfer through certified optimization

If one analytically certified candidate monotonically rounds a benchmark,
then the certified finite optimizer is nonempty and cannot perform worse
than that candidate.  The zero-error ceiling comparison therefore preserves
the benchmark balanced exponent, robust margin, and polynomial scale while
the selected profile automatically carries a complete actual transfer
certificate.
-/

namespace PrimeNumberTheorem

/-- Optimize only among analytically certified profiles while retaining the
full performance of a benchmark monotonically covered by one certified
candidate.

Unlike the earlier unconstrained optimizer, no analytic data is requested
after the selected profile is known. -/
theorem
    unified_actualBalancedHeight_of_optimalCertifiedMonotoneStripProfile
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ)
    (benchmark candidate : ActualSelectedHeightFiniteStripProfile)
    (hcandidate : candidate ∈ candidates)
    (candidateCertificate :
      candidate.AnalyticTransferCertificate beta selection S)
    (hbenchmarkHalf : ∀ i, 1 / 2 < benchmark.sigma i)
    (hbenchmarkTau : ∀ i, benchmark.tau i ≤ beta)
    (hrounding : benchmark.MonotoneRoundingCovers candidate) :
    let certified :=
      analyticTransferCertifiedProfiles beta selection S candidates
    let hexists :
        ∃ profile ∈ candidates,
          profile.HasAnalyticTransferCertificate beta selection S :=
      ⟨candidate, hcandidate, ⟨candidateCertificate⟩⟩
    let hne :=
      analyticTransferCertifiedProfiles_nonempty
        beta selection S candidates hexists
    let chosen :=
      optimalActualSelectedHeightFiniteStripProfile beta certified hne
    (chosen ∈ candidates ∧
        chosen.HasAnalyticTransferCertificate beta selection S ∧
        (∀ profile ∈ candidates,
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
  let certified :=
    analyticTransferCertifiedProfiles beta selection S candidates
  let hexists :
      ∃ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S :=
    ⟨candidate, hcandidate, ⟨candidateCertificate⟩⟩
  let hne : certified.Nonempty :=
    analyticTransferCertifiedProfiles_nonempty
      beta selection S candidates hexists
  let chosen :=
    optimalActualSelectedHeightFiniteStripProfile beta certified hne
  have hcertifiedTransfer :
      chosen ∈ candidates ∧
        chosen.HasAnalyticTransferCertificate beta selection S ∧
        (∀ profile ∈ candidates,
          profile.HasAnalyticTransferCertificate beta selection S →
            profile.optimalRobustMargin beta ≤
              chosen.optimalRobustMargin beta) ∧
        chosen.HasUnifiedTransferResult beta := by
    simpa [certified, hexists, hne, chosen] using
      unified_actualBalancedHeight_of_optimalCertifiedFiniteStripProfile
        threshold hhalf hlt hbeta hbetaOne
        candidates selection S hexists
  have hcandidateCertified : candidate ∈ certified := by
    simpa [certified] using
      (mem_analyticTransferCertifiedProfiles_iff
        beta selection S candidates candidate).2
        ⟨hcandidate, ⟨candidateCertificate⟩⟩
  have hcoverage :
      benchmark.StripAlphaCeilingCoversWithin candidate beta 0 :=
    stripAlphaCeilingCoversWithin_zero_of_monotoneRoundingCovers
      beta benchmark candidate hbenchmarkHalf
      candidateCertificate.sigma_one hbenchmarkTau hrounding
  have happrox :
      benchmark.effectiveAlphaCeiling beta ≤
        candidate.effectiveAlphaCeiling beta + 0 :=
    effectiveAlphaCeiling_approximation_of_stripAlphaCeilingCoverage
      beta 0 benchmark candidate le_rfl hcoverage
  have hexponent :
      benchmark.balancedExponent beta ≤
        chosen.balancedExponent beta := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_balancedExponent_approximation
        beta 0 certified hne benchmark hcandidateCertified happrox
  have hmargin :
      benchmark.optimalRobustMargin beta ≤
        chosen.optimalRobustMargin beta := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_approximation
        beta 0 certified hne benchmark hcandidateCertified happrox
  have hscale :
      ∀ x : ℝ, 1 ≤ x →
        benchmark.balancedPolynomialScale beta x ≤
          chosen.balancedPolynomialScale beta x := by
    intro x hx
    simpa [chosen,
      ActualSelectedHeightFiniteStripProfile.balancedPolynomialScale] using
      optimalActualSelectedHeightFiniteStripProfile_balancedPolynomialScale_approximation
        beta 0 x certified hne benchmark hcandidateCertified happrox hx
  exact ⟨hcertifiedTransfer, hexponent, hmargin, hscale⟩

end PrimeNumberTheorem
