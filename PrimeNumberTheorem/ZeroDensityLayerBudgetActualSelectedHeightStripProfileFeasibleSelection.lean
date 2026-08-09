import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileOptimalTransfer

/-!
# Feasibility of the profile selected from a mixed candidate family

The finite optimizer need not be restricted to an already-filtered family.
Under the standard strip hypotheses, one feasible candidate has positive
balanced robust margin.  Maximality transfers positivity to the selected
profile, and positivity forces that selected profile to be feasible.
-/

namespace PrimeNumberTheorem

/-- Positive balanced robust margin forces finite-strip feasibility. -/
theorem
    ActualSelectedHeightFiniteStripProfile.isFeasible_of_optimalRobustMargin_pos
    {beta : ℝ}
    (profile : ActualSelectedHeightFiniteStripProfile)
    (hsigma : ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne : ∀ i, profile.sigma i < 1)
    (hmargin : 0 < profile.optimalRobustMargin beta) :
    profile.IsFeasible beta := by
  have hmargin' :
      0 <
        actualSelectedHeightFiniteStripRobustMargin
          beta profile.sigma profile.tau
          (actualSelectedHeightFiniteStripBalancedExponent
            beta profile.sigma profile.tau) := by
    exact hmargin
  rw [actualSelectedHeightFiniteStripBalancedExponent_robustMargin] at hmargin'
  have heffective :
      1 - beta <
        actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta profile.sigma profile.tau := by
    linarith
  have halpha :
      1 - beta <
        actualSelectedHeightFiniteStripAlphaCeiling
          beta profile.sigma profile.tau :=
    lt_of_lt_of_le heffective (min_le_right _ _)
  have hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold
          (profile.sigma i) (profile.tau i) < beta :=
    (contourTransition_lt_finiteStripAlphaCeiling_iff
      profile.sigma profile.tau hsigma hsigmaOne).1 halpha
  exact
    (actualSelectedHeightFiniteStripBottleneck_lt_iff
      profile.sigma profile.tau beta).2 hthreshold

/-- One feasible member gives the selected profile positive robust margin. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_pos_of_exists_feasible
    {beta : ℝ} (hbeta : 0 < beta)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (hexistsFeasible :
      ∃ profile ∈ candidates, profile.IsFeasible beta) :
    0 <
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).optimalRobustMargin beta := by
  rcases hexistsFeasible with ⟨profile, hprofileMem, hprofileFeasible⟩
  have hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold
          (profile.sigma i) (profile.tau i) < beta :=
    (actualSelectedHeightFiniteStripBottleneck_lt_iff
      profile.sigma profile.tau beta).1 hprofileFeasible
  have hprofileMargin :
      0 < profile.optimalRobustMargin beta := by
    exact
      actualSelectedHeightFiniteStripBalancedExponent_robustMargin_pos
        profile.sigma profile.tau hbeta
        (hsigma profile hprofileMem)
        (hsigmaOne profile hprofileMem)
        hthreshold
  exact
    lt_of_lt_of_le hprofileMargin
      (optimalActualSelectedHeightFiniteStripProfile_score_ge
        beta candidates hne hprofileMem)

/-- If at least one candidate is feasible, the profile selected by balanced
robust margin is feasible. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_feasible_of_exists
    {beta : ℝ} (hbeta : 0 < beta)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (hexistsFeasible :
      ∃ profile ∈ candidates, profile.IsFeasible beta) :
    (optimalActualSelectedHeightFiniteStripProfile
      beta candidates hne).IsFeasible beta := by
  let chosen :=
    optimalActualSelectedHeightFiniteStripProfile beta candidates hne
  have hchosenMem : chosen ∈ candidates := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_mem
        beta candidates hne
  apply
    ActualSelectedHeightFiniteStripProfile.isFeasible_of_optimalRobustMargin_pos
  · exact hsigma chosen hchosenMem
  · exact hsigmaOne chosen hchosenMem
  · simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_pos_of_exists_feasible
        hbeta candidates hne hsigma hsigmaOne hexistsFeasible

/-- Run the full optimal finite-profile transfer when the candidate family
contains at least one feasible profile.  Infeasible candidates need not be
removed in advance. -/
theorem
    unified_actualBalancedHeight_of_optimalFiniteStripProfile_of_exists_feasible
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (hexistsFeasible :
      ∃ profile ∈ candidates, profile.IsFeasible beta)
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
    chosen ∈ candidates ∧
      (∀ candidate ∈ candidates,
        candidate.optimalRobustMargin beta ≤
          chosen.optimalRobustMargin beta) ∧
      chosen.HasUnifiedTransferResult beta := by
  let chosen :=
    optimalActualSelectedHeightFiniteStripProfile beta candidates hne
  have hchosenMem : chosen ∈ candidates := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_mem
        beta candidates hne
  have hchosenFeasible : chosen.IsFeasible beta := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_feasible_of_exists
        hbeta candidates hne hsigma hsigmaOne hexistsFeasible
  have hchosenTransfer : chosen.HasUnifiedTransferResult beta := by
    unfold ActualSelectedHeightFiniteStripProfile.HasUnifiedTransferResult
    exact
      unified_actualBalancedHeight_of_profileRefinement
        threshold hhalf hlt
        chosen.sigma chosen.tau chosen.sigma chosen.tau
        hbeta hbetaOne
        (hsigma chosen hchosenMem)
        (hsigmaOne chosen hchosenMem)
        (ActualSelectedHeightFiniteStripProfile.Refines.refl beta chosen)
        hchosenFeasible selection input kappa hS hfixedSigma
        hkappa hnorm hre hreal hmain
  refine ⟨hchosenMem, ?_, hchosenTransfer⟩
  intro candidate hcandidate
  simpa [chosen] using
    optimalActualSelectedHeightFiniteStripProfile_score_ge
      beta candidates hne hcandidate

end PrimeNumberTheorem
