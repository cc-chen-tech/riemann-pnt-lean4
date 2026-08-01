import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualSelectedHeightSharpTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTReverseClusterExclusion

/-!
# Actual Carlson selected-height bidirectional PNT transfer

This file packages the coefficient-exposed Carlson residual theorem into a
single transfer certificate for the genuine relative Chebyshev error.

* An empty visible cluster makes the actual PNT error negligible at the target
  zero-power scale.
* A nonempty cluster carrying a natural-point witness with constant `c`
  transfers every strict positive threshold `q < c` to the actual PNT error.
* Negligibility of the actual PNT error forces the cluster to be empty.
* The same selected height retains its certified optimal power scale.

The finite outside-cluster bucket input, real-ordinate gap, and external
cluster witness remain explicit hypotheses.  In particular, this theorem is
not an unconditional PNT error estimate, Omega theorem, or RH statement.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/--
Bidirectional actual-PNT transfer certificate for the coefficient-exposed
Carlson selected-height chain.

Unlike the earlier fixed-threshold facade, the lower field preserves every
strict positive constant below the supplied cluster constant.
-/
structure ActualCarlsonSelectedHeightPNTBidirectionalTransferCertificate
    {beta c : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) : Prop where
  empty_cluster_iff_error_negligible :
    S = ∅ ↔
      NaturalPointTargetAmplitudeNegligible
        (fun m => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
  nonempty_cluster_all_strict_positive_oscillation :
    S.Nonempty →
      ∀ q : ℝ, 0 < q → q < c →
        HasFarTargetAmplitudeWitness
          relativeChebyshevPsi0Error
          (fun x => q * targetZeroPowerAmplitude beta x)
  selected_height_ratio :
    Tendsto
      (fun x =>
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection x /
          x ^ actualSelectedHeightFiniteStripWeightedBalancedExponent
            beta sigma tau)
      atTop
      (nhds 1)
  selected_height_log_growth :
    Tendsto
      (fun x =>
        Real.log
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection x) /
          Real.log x)
      atTop
      (nhds
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau))

/--
The coefficient-exposed Carlson chain gives a bidirectional transfer theorem
for the same actual relative PNT error and the same optimized selected height.
-/
theorem actualCarlsonSelectedHeightPNTBidirectionalTransfer
    {beta c : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hc : 0 < c)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      ∀ x,
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm : ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre : ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      S.Nonempty →
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              S
              (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    ActualCarlsonSelectedHeightPNTBidirectionalTransferCertificate
      (beta := beta) (c := c) sigma tau selection S := by
  refine
    { empty_cluster_iff_error_negligible := ?_
      nonempty_cluster_all_strict_positive_oscillation := ?_
      selected_height_ratio :=
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_div_optimalScale_tendsto_one
          sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      selected_height_log_growth :=
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_logGrowth_tendsto_optimalExponent
          sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection }
  · constructor
    · intro hEmpty
      subst S
      have hEmptyInvariant :
          IsConjugationInvariantCluster (∅ : Finset ℂ) := by
        simp [IsConjugationInvariantCluster]
      have hresidual :=
        actualSelectedHeightWeightedBalancedClusterResidual_targetNegligible
          hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
          input kappa hEmptyInvariant hfixedSigma hkappa hnorm hre hreal
      simpa [dynamicVisibleClusterPNTMain,
        dynamicVisibleClusterPNTZeroSum] using hresidual
    · intro herror
      exact
        actualWeightedBalancedGoodHeightPNTErrorNegligible_forces_emptyCluster
          hbeta hbetaOne hc sigma tau hsigma hsigmaOne htau hthreshold
          selection input kappa hS hfixedSigma hkappa hnorm hre hreal
          herror hmain
  · intro hNonempty q hq hqc
    exact
      actualSelectedHeightWeightedBalancedClusterWitness_transfer_lt
        hbeta hbetaOne hq hqc sigma tau hsigma hsigmaOne htau hthreshold
        selection input kappa hS hfixedSigma hkappa hnorm hre hreal
        (hmain hNonempty)

end PrimeNumberTheorem
