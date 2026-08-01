import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileFiniteGridExtremalSelection

/-!
# Certificate-aware finite strip-profile optimization

An unconstrained finite optimizer may select a profile before anyone proves
that the actual zeta-zero buckets and oscillation witness required by that
profile exist.  This module reverses that order.

An `AnalyticTransferCertificate` packages the full profile-dependent input
to the existing Pintz--Carlson--explicit-formula transfer.  A finite family
is filtered to profiles for which such a certificate exists, and only then
is the robust-margin optimizer run.  Membership of the selected profile
therefore recovers a real certificate automatically.
-/

namespace PrimeNumberTheorem

/-- Full profile-dependent analytic data needed to run the existing unified
transfer at a fixed dynamic strip profile. -/
structure
    ActualSelectedHeightFiniteStripProfile.AnalyticTransferCertificate
    (profile : ActualSelectedHeightFiniteStripProfile)
    (beta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) where
  sigma_half : ∀ i, 1 / 2 < profile.sigma i
  sigma_one : ∀ i, profile.sigma i < 1
  bottleneck_lt : profile.bottleneck < beta
  input :
    (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput
        (actualSelectedHeightFiniteStripBalancedHeight
          beta profile.sigma profile.tau selection x)
        S (profile.stripCount + 1)
  kappa : Fin (profile.stripCount + 1) → ℝ
  conjugation_invariant : IsConjugationInvariantCluster S
  fixed_sigma :
    ∀ i x, (input x).sigma i = profile.sigma i
  kappa_pos : ∀ i, 0 < kappa i
  norm_lower :
    ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖
  real_part_upper :
    ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ profile.tau i
  real_ordinate_upper :
    ∀ rho ∈
      realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta
  main_witness :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m : ℕ =>
        dynamicVisibleClusterPNTMain
          (actualSelectedHeightFiniteStripBalancedHeight
            beta profile.sigma profile.tau selection)
          S (m : ℝ))
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))

/-- A profile is analytically certified when the complete transfer input is
inhabited. -/
def
    ActualSelectedHeightFiniteStripProfile.HasAnalyticTransferCertificate
    (profile : ActualSelectedHeightFiniteStripProfile)
    (beta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) : Prop :=
  Nonempty (profile.AnalyticTransferCertificate beta selection S)

/-- A complete analytic certificate produces the existing unified upper and
lower transfer result for its profile. -/
theorem
    ActualSelectedHeightFiniteStripProfile.AnalyticTransferCertificate.hasUnifiedTransferResult
    {profile : ActualSelectedHeightFiniteStripProfile}
    {beta : ℝ}
    {selection : UniformNaturalPointGoodHeightSelection}
    {S : Finset ℂ}
    (certificate :
      profile.AnalyticTransferCertificate beta selection S)
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    (hbeta : 0 < beta) (hbetaOne : beta < 1) :
    profile.HasUnifiedTransferResult beta := by
  unfold ActualSelectedHeightFiniteStripProfile.HasUnifiedTransferResult
  exact
    unified_actualBalancedHeight_of_profileRefinement
      threshold hhalf hlt
      profile.sigma profile.tau profile.sigma profile.tau
      hbeta hbetaOne certificate.sigma_half certificate.sigma_one
      (ActualSelectedHeightFiniteStripProfile.Refines.refl beta profile)
      certificate.bottleneck_lt selection certificate.input
      certificate.kappa certificate.conjugation_invariant
      certificate.fixed_sigma certificate.kappa_pos
      certificate.norm_lower certificate.real_part_upper
      certificate.real_ordinate_upper certificate.main_witness

/-- Filter a finite candidate family to profiles carrying complete analytic
transfer certificates. -/
noncomputable def analyticTransferCertifiedProfiles
    (beta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile) :
    Finset ActualSelectedHeightFiniteStripProfile := by
  classical
  exact candidates.filter
    (fun profile =>
      profile.HasAnalyticTransferCertificate beta selection S)

/-- Membership in the certified family records both original membership and
the existence of a complete analytic certificate. -/
theorem mem_analyticTransferCertifiedProfiles_iff
    (beta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (profile : ActualSelectedHeightFiniteStripProfile) :
    profile ∈
        analyticTransferCertifiedProfiles beta selection S candidates ↔
      profile ∈ candidates ∧
        profile.HasAnalyticTransferCertificate beta selection S := by
  classical
  simp [analyticTransferCertifiedProfiles]

/-- One certified candidate makes the filtered finite family nonempty. -/
theorem analyticTransferCertifiedProfiles_nonempty
    (beta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hexists :
      ∃ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S) :
    (analyticTransferCertifiedProfiles
      beta selection S candidates).Nonempty := by
  obtain ⟨profile, hprofile, hcertificate⟩ := hexists
  exact
    ⟨profile,
      (mem_analyticTransferCertifiedProfiles_iff
        beta selection S candidates profile).2
        ⟨hprofile, hcertificate⟩⟩

/-- Optimize robust margin only after filtering to profiles with complete
actual analytic transfer certificates.

The selected profile is certified, belongs to the original family, dominates
every other certified candidate, and carries the full unified transfer
result. -/
theorem unified_actualBalancedHeight_of_optimalCertifiedFiniteStripProfile
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ)
    (hexists :
      ∃ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S) :
    let certified :=
      analyticTransferCertifiedProfiles beta selection S candidates
    let hne :=
      analyticTransferCertifiedProfiles_nonempty
        beta selection S candidates hexists
    let chosen :=
      optimalActualSelectedHeightFiniteStripProfile beta certified hne
    chosen ∈ candidates ∧
      chosen.HasAnalyticTransferCertificate beta selection S ∧
      (∀ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S →
          profile.optimalRobustMargin beta ≤
            chosen.optimalRobustMargin beta) ∧
      chosen.HasUnifiedTransferResult beta := by
  let certified :=
    analyticTransferCertifiedProfiles beta selection S candidates
  let hne :
      certified.Nonempty :=
    analyticTransferCertifiedProfiles_nonempty
      beta selection S candidates hexists
  let chosen :=
    optimalActualSelectedHeightFiniteStripProfile beta certified hne
  have hchosenCertified : chosen ∈ certified := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_mem
        beta certified hne
  have hchosenData :
      chosen ∈ candidates ∧
        chosen.HasAnalyticTransferCertificate beta selection S := by
    simpa [certified] using
      (mem_analyticTransferCertifiedProfiles_iff
        beta selection S candidates chosen).1 hchosenCertified
  let certificate :
      chosen.AnalyticTransferCertificate beta selection S :=
    Classical.choice hchosenData.2
  have htransfer : chosen.HasUnifiedTransferResult beta :=
    certificate.hasUnifiedTransferResult
      threshold hhalf hlt hbeta hbetaOne
  refine ⟨hchosenData.1, hchosenData.2, ?_, htransfer⟩
  intro profile hprofile hcertificate
  have hprofileCertified : profile ∈ certified := by
    simpa [certified] using
      (mem_analyticTransferCertifiedProfiles_iff
        beta selection S candidates profile).2
        ⟨hprofile, hcertificate⟩
  simpa [chosen] using
    optimalActualSelectedHeightFiniteStripProfile_score_ge
      beta certified hne hprofileCertified

end PrimeNumberTheorem
