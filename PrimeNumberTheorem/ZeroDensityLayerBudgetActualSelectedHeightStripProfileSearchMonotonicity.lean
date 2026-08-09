import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileOptimization

/-!
# Monotonicity of finite dynamic-strip profile search

These order lemmas make the finite profile optimizer usable as a certified
dynamic search: enlarging the candidate family cannot lower the best robust
margin, and a refinement candidate transfers its margin improvement to the
selected optimum.
-/

namespace PrimeNumberTheorem

/-- Enlarging a nonempty finite candidate family cannot lower the robust
margin selected by the optimizer. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_score_mono_of_subset
    (beta : ℝ)
    (candidates largerCandidates :
      Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hlargerNe : largerCandidates.Nonempty)
    (hsubset : candidates ⊆ largerCandidates) :
    (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).optimalRobustMargin beta ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta largerCandidates hlargerNe).optimalRobustMargin beta := by
  exact
    optimalActualSelectedHeightFiniteStripProfile_score_ge
      beta largerCandidates hlargerNe
      (hsubset
        (optimalActualSelectedHeightFiniteStripProfile_mem
          beta candidates hne))

/-- If a refined profile is among the candidates, the selected optimum has
margin at least that of the coarse profile. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_score_ge_of_refinement
    {beta : ℝ}
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    {refined coarse : ActualSelectedHeightFiniteStripProfile}
    (certificate : refined.Refines beta coarse)
    (hrefined : refined ∈ candidates) :
    coarse.optimalRobustMargin beta ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).optimalRobustMargin beta := by
  exact
    le_trans
      (ActualSelectedHeightFiniteStripProfile.Refines.optimalRobustMargin_mono
        certificate)
      (optimalActualSelectedHeightFiniteStripProfile_score_ge
        beta candidates hne hrefined)

/-- A profile with strictly smaller margin than an available candidate cannot
be the profile selected by the optimizer. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_ne_of_strictly_better
    {beta : ℝ}
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    {better profile : ActualSelectedHeightFiniteStripProfile}
    (hbetter : better ∈ candidates)
    (hstrict :
      profile.optimalRobustMargin beta <
        better.optimalRobustMargin beta) :
    optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne ≠ profile := by
  intro heq
  have hdominates :=
    optimalActualSelectedHeightFiniteStripProfile_score_ge
      beta candidates hne hbetter
  rw [heq] at hdominates
  exact (not_lt_of_ge hdominates) hstrict

/-- A strictly margin-improving refinement present in the candidate family
forces the optimizer away from the coarse profile. -/
theorem
    optimalActualSelectedHeightFiniteStripProfile_ne_coarse_of_strict_refinement
    {beta : ℝ}
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    {refined coarse : ActualSelectedHeightFiniteStripProfile}
    (_certificate : refined.Refines beta coarse)
    (hrefined : refined ∈ candidates)
    (hstrict :
      coarse.optimalRobustMargin beta <
        refined.optimalRobustMargin beta) :
    optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne ≠ coarse :=
  optimalActualSelectedHeightFiniteStripProfile_ne_of_strictly_better
    candidates hne hrefined hstrict

end PrimeNumberTheorem
