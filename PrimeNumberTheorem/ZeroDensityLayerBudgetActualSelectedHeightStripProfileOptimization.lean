import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileRefinement

/-!
# Finite-candidate optimization of dynamic strip profiles

Different real-part decompositions may have different numbers of strips.  This
module packages them into one type and chooses, from a supplied nonempty finite
candidate family, a profile maximizing the certified balanced robustness
margin.

Optimality is exact only within the supplied finite candidate family.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- A nonempty finite strip profile with an arbitrary number of strips. -/
structure ActualSelectedHeightFiniteStripProfile where
  stripCount : ℕ
  sigma : Fin (stripCount + 1) → ℝ
  tau : Fin (stripCount + 1) → ℝ

/-- Endpoint bottleneck of a packaged strip profile. -/
noncomputable def ActualSelectedHeightFiniteStripProfile.bottleneck
    (profile : ActualSelectedHeightFiniteStripProfile) : ℝ :=
  actualSelectedHeightFiniteStripBottleneck profile.sigma profile.tau

/-- Common alpha ceiling of a packaged strip profile. -/
noncomputable def ActualSelectedHeightFiniteStripProfile.alphaCeiling
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) : ℝ :=
  actualSelectedHeightFiniteStripAlphaCeiling
    beta profile.sigma profile.tau

/-- Explicit balanced exponent of a packaged strip profile. -/
noncomputable def ActualSelectedHeightFiniteStripProfile.balancedExponent
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) : ℝ :=
  actualSelectedHeightFiniteStripBalancedExponent
    beta profile.sigma profile.tau

/-- Certified optimal two-sided robustness value of a packaged profile. -/
noncomputable def ActualSelectedHeightFiniteStripProfile.optimalRobustMargin
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) : ℝ :=
  actualSelectedHeightFiniteStripRobustMargin
    beta profile.sigma profile.tau
    (profile.balancedExponent beta)

/-- Feasibility of a packaged profile for a target real part. -/
def ActualSelectedHeightFiniteStripProfile.IsFeasible
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) : Prop :=
  profile.bottleneck < beta

/-- Cross-cardinality refinement relation on packaged profiles. -/
def ActualSelectedHeightFiniteStripProfile.Refines
    (beta : ℝ)
    (refined coarse : ActualSelectedHeightFiniteStripProfile) : Prop :=
  ActualSelectedHeightFiniteStripProfileRefinement beta
    refined.sigma refined.tau coarse.sigma coarse.tau

/-- Packaged profile refinement is reflexive. -/
theorem ActualSelectedHeightFiniteStripProfile.Refines.refl
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) :
    profile.Refines beta profile :=
  ActualSelectedHeightFiniteStripProfileRefinement.refl
    beta profile.sigma profile.tau

/-- Packaged profile refinement is transitive. -/
theorem ActualSelectedHeightFiniteStripProfile.Refines.trans
    {beta : ℝ}
    {fine middle coarse : ActualSelectedHeightFiniteStripProfile}
    (fineMiddle : fine.Refines beta middle)
    (middleCoarse : middle.Refines beta coarse) :
    fine.Refines beta coarse :=
  ActualSelectedHeightFiniteStripProfileRefinement.trans
    fineMiddle middleCoarse

/-- Refinement preserves feasibility. -/
theorem ActualSelectedHeightFiniteStripProfile.Refines.feasible
    {beta : ℝ}
    {refined coarse : ActualSelectedHeightFiniteStripProfile}
    (certificate : refined.Refines beta coarse)
    (hcoarse : coarse.IsFeasible beta) :
    refined.IsFeasible beta :=
  ActualSelectedHeightFiniteStripProfileRefinement.feasible
    certificate hcoarse

/-- Refinement cannot decrease the packaged optimal robustness score. -/
theorem ActualSelectedHeightFiniteStripProfile.Refines.optimalRobustMargin_mono
    {beta : ℝ}
    {refined coarse : ActualSelectedHeightFiniteStripProfile}
    (certificate : refined.Refines beta coarse) :
    coarse.optimalRobustMargin beta ≤ refined.optimalRobustMargin beta :=
  certificate.robustMargin_mono

/-- A candidate maximizes the packaged robustness score over a finite family. -/
structure IsOptimalActualSelectedHeightFiniteStripProfile
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (candidate : ActualSelectedHeightFiniteStripProfile) : Prop where
  mem : candidate ∈ candidates
  maximal :
    ∀ other ∈ candidates,
      other.optimalRobustMargin beta ≤
        candidate.optimalRobustMargin beta

/-- Every nonempty finite family of dynamic strip profiles has a robustness
maximizer. -/
theorem exists_optimalActualSelectedHeightFiniteStripProfile
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty) :
    ∃ candidate,
      IsOptimalActualSelectedHeightFiniteStripProfile
        beta candidates candidate := by
  classical
  obtain ⟨candidate, hcandidate, hmaximal⟩ :=
    Finset.exists_max_image candidates
      (ActualSelectedHeightFiniteStripProfile.optimalRobustMargin beta)
      hne
  exact ⟨candidate, hcandidate, hmaximal⟩

/-- Canonical finite-candidate dynamic strip profile optimizer. -/
noncomputable def optimalActualSelectedHeightFiniteStripProfile
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty) :
    ActualSelectedHeightFiniteStripProfile :=
  Classical.choose
    (exists_optimalActualSelectedHeightFiniteStripProfile
      beta candidates hne)

/-- Full specification of the canonical finite-candidate profile optimizer. -/
theorem optimalActualSelectedHeightFiniteStripProfile_spec
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty) :
    IsOptimalActualSelectedHeightFiniteStripProfile beta candidates
      (optimalActualSelectedHeightFiniteStripProfile beta candidates hne) :=
  Classical.choose_spec
    (exists_optimalActualSelectedHeightFiniteStripProfile
      beta candidates hne)

/-- The canonical optimizer belongs to the supplied candidate family. -/
theorem optimalActualSelectedHeightFiniteStripProfile_mem
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty) :
    optimalActualSelectedHeightFiniteStripProfile beta candidates hne ∈
      candidates :=
  (optimalActualSelectedHeightFiniteStripProfile_spec
    beta candidates hne).mem

/-- The canonical optimizer dominates every supplied profile's certified
robustness score. -/
theorem optimalActualSelectedHeightFiniteStripProfile_score_ge
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    {candidate : ActualSelectedHeightFiniteStripProfile}
    (hcandidate : candidate ∈ candidates) :
    candidate.optimalRobustMargin beta ≤
      (optimalActualSelectedHeightFiniteStripProfile
        beta candidates hne).optimalRobustMargin beta :=
  (optimalActualSelectedHeightFiniteStripProfile_spec
    beta candidates hne).maximal candidate hcandidate

/-- If every supplied profile is feasible, then the canonical robustness
optimizer is feasible. -/
theorem optimalActualSelectedHeightFiniteStripProfile_feasible
    (beta : ℝ)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hfeasible : ∀ profile ∈ candidates, profile.IsFeasible beta) :
    (optimalActualSelectedHeightFiniteStripProfile
      beta candidates hne).IsFeasible beta :=
  hfeasible _
    (optimalActualSelectedHeightFiniteStripProfile_mem
      beta candidates hne)

end PrimeNumberTheorem
