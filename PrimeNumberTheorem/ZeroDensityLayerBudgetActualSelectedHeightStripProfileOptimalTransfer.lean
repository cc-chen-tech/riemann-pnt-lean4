import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightAutomaticNaturalTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileOptimization

/-!
# Unified transfer at the best profile in a finite candidate family

This module connects the finite dynamic-strip profile optimizer to the existing
Pintz--Carlson--explicit-formula transfer.  The optimization is exact inside
the supplied finite nonempty family; no claim of continuous partition
optimality is made.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

/-- The upper/lower/optimal-height conclusion attached to one finite strip
profile.  This packages exactly the conclusion already produced by
`unified_actualBalancedHeight_of_profileRefinement`. -/
def ActualSelectedHeightFiniteStripProfile.HasUnifiedTransferResult
    (beta : ℝ) (profile : ActualSelectedHeightFiniteStripProfile) : Prop :=
  ((∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2)) ∧
  0 <
    actualSelectedHeightFiniteStripRobustMargin
      beta profile.sigma profile.tau
      (actualSelectedHeightFiniteStripBalancedExponent
        beta profile.sigma profile.tau) ∧
  (∀ alpha : ℝ,
    actualSelectedHeightFiniteStripRobustMargin
        beta profile.sigma profile.tau alpha ≤
      actualSelectedHeightFiniteStripRobustMargin
        beta profile.sigma profile.tau
        (actualSelectedHeightFiniteStripBalancedExponent
          beta profile.sigma profile.tau)) ∧
  (∀ alpha : ℝ,
    actualSelectedHeightFiniteStripRobustMargin
        beta profile.sigma profile.tau
        (actualSelectedHeightFiniteStripBalancedExponent
          beta profile.sigma profile.tau) ≤
      actualSelectedHeightFiniteStripRobustMargin
        beta profile.sigma profile.tau alpha →
    alpha =
      actualSelectedHeightFiniteStripBalancedExponent
        beta profile.sigma profile.tau)

/-- Select the profile with the largest certified balanced robust margin from a
finite nonempty candidate family, then run the full unified PNT transfer at
that profile.

The analytic data are indexed by the selected profile because different
candidates may have different strip counts.  The theorem additionally returns
membership of the selected profile and score dominance over every candidate.
-/
theorem
    unified_actualBalancedHeight_of_optimalFiniteStripProfile
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (candidates : Finset ActualSelectedHeightFiniteStripProfile)
    (hne : candidates.Nonempty)
    (hsigma :
      ∀ profile ∈ candidates, ∀ i, 1 / 2 < profile.sigma i)
    (hsigmaOne :
      ∀ profile ∈ candidates, ∀ i, profile.sigma i < 1)
    (hfeasible :
      ∀ profile ∈ candidates, profile.IsFeasible beta)
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
      optimalActualSelectedHeightFiniteStripProfile_feasible
        beta candidates hne hfeasible
  have hchosenSigma : ∀ i, 1 / 2 < chosen.sigma i :=
    hsigma chosen hchosenMem
  have hchosenSigmaOne : ∀ i, chosen.sigma i < 1 :=
    hsigmaOne chosen hchosenMem
  have hchosenTransfer : chosen.HasUnifiedTransferResult beta := by
    unfold ActualSelectedHeightFiniteStripProfile.HasUnifiedTransferResult
    exact
      unified_actualBalancedHeight_of_profileRefinement
        threshold hhalf hlt
        chosen.sigma chosen.tau chosen.sigma chosen.tau
        hbeta hbetaOne hchosenSigma hchosenSigmaOne
        (ActualSelectedHeightFiniteStripProfile.Refines.refl beta chosen)
        hchosenFeasible selection input kappa hS hfixedSigma
        hkappa hnorm hre hreal hmain
  refine ⟨hchosenMem, ?_, hchosenTransfer⟩
  intro candidate hcandidate
  simpa [chosen] using
    optimalActualSelectedHeightFiniteStripProfile_score_ge
      beta candidates hne hcandidate

end PrimeNumberTheorem
