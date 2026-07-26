import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileFeasibleSelection

/-!
# Exact feasibility characterization for finite strip-profile search

Under the standard strip hypotheses, feasibility is equivalent to positivity
of the balanced robust margin.  Consequently, the finite optimizer selects a
feasible profile exactly when its candidate family contains one.
-/

namespace PrimeNumberTheorem

/-- A finite strip profile is feasible exactly when its balanced robust margin
is positive. -/
theorem
    ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_pos_iff_isFeasible
    {beta : ℝ} (hbeta : 0 < beta)
    (profile : ActualSelectedHeightFiniteStripProfile)
    (hsigma : ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne : ∀ i, profile.sigma i < 1) :
    0 < profile.optimalRobustMargin beta ↔
      profile.IsFeasible beta := by
  constructor
  · exact
      profile.isFeasible_of_optimalRobustMargin_pos
        hsigma hsigmaOne
  · intro hfeasible
    have hthreshold :
        ∀ i,
          carlsonStripEndpointTargetThreshold
            (profile.sigma i) (profile.tau i) < beta :=
      (actualSelectedHeightFiniteStripBottleneck_lt_iff
        profile.sigma profile.tau beta).1 hfeasible
    exact
      actualSelectedHeightFiniteStripBalancedExponent_robustMargin_pos
        profile.sigma profile.tau hbeta hsigma hsigmaOne hthreshold

/-- The optimizer selects a feasible profile exactly when at least one
candidate is feasible. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_feasible_iff_exists
    {beta : ℝ} (hbeta : 0 < beta)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1) :
    (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).IsFeasible beta ↔
      ∃ profile ∈ candidates, profile.IsFeasible beta := by
  constructor
  · intro hselected
    exact
      ⟨optimalActualSelectedHeightFiniteStripProfile
          beta candidates hne,
        optimalActualSelectedHeightFiniteStripProfile_mem
          beta candidates hne,
        hselected⟩
  · intro hexists
    exact
      optimalActualSelectedHeightFiniteStripProfile_feasible_of_exists
        hbeta candidates hne hsigma hsigmaOne hexists

/-- The selected robust margin is positive exactly when the candidate family
contains a feasible profile. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_pos_iff_exists
    {beta : ℝ} (hbeta : 0 < beta)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1) :
    0 <
        (optimalActualSelectedHeightFiniteStripProfile
          beta candidates hne).optimalRobustMargin beta ↔
      ∃ profile ∈ candidates, profile.IsFeasible beta := by
  let chosen :=
    optimalActualSelectedHeightFiniteStripProfile beta candidates hne
  have hchosenMem : chosen ∈ candidates := by
    simpa [chosen] using
      optimalActualSelectedHeightFiniteStripProfile_mem
        beta candidates hne
  exact
    (ActualSelectedHeightFiniteStripProfile.optimalRobustMargin_pos_iff_isFeasible
      hbeta chosen
      (hsigma chosen hchosenMem)
      (hsigmaOne chosen hchosenMem)).trans
      (optimalActualSelectedHeightFiniteStripProfile_feasible_iff_exists
        hbeta candidates hne hsigma hsigmaOne)

/-- If no candidate is feasible, the best certified balanced robust margin is
nonpositive, and conversely. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_nonpos_iff
    {beta : ℝ} (hbeta : 0 < beta)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1) :
    (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).optimalRobustMargin beta ≤ 0 ↔
      ∀ profile ∈ candidates, ¬ profile.IsFeasible beta := by
  constructor
  · intro hnonpos profile hprofileMem hprofileFeasible
    have hpos :
        0 <
          (optimalActualSelectedHeightFiniteStripProfile
            beta candidates hne).optimalRobustMargin beta :=
      (optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_pos_iff_exists
        hbeta candidates hne hsigma hsigmaOne).2
        ⟨profile, hprofileMem, hprofileFeasible⟩
    exact (not_lt_of_ge hnonpos) hpos
  · intro hnone
    apply le_of_not_gt
    intro hpos
    rcases
        (optimalActualSelectedHeightFiniteStripProfile_optimalRobustMargin_pos_iff_exists
          hbeta candidates hne hsigma hsigmaOne).1 hpos with
      ⟨profile, hprofileMem, hprofileFeasible⟩
    exact hnone profile hprofileMem hprofileFeasible

end PrimeNumberTheorem
