import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTReverseClusterExclusion

/-!
# Bidirectional Pintz--Carlson--explicit-formula transfer for the actual PNT error

This file closes the forward and reverse transfer statements proved by the
dynamic layer-budget development into one certificate for the same actual
relative Chebyshev error.

Under explicit Carlson strip inputs and an external positive visible-cluster
oscillation witness:

* the visible cluster is empty if and only if the actual PNT error is negligible
  at the target zero-power scale;
* every strict oscillation threshold below the cluster constant transfers to
  the actual PNT error when the cluster is nonempty;
* the common selected truncation height has the certified optimal power-scale
  ratio and logarithmic growth.

Thus the upper, lower, reverse, and height-optimization outputs no longer live
in parallel interfaces.  The theorem remains conditional on the bucket input
and on the external cluster witness; it does not assert an unconditional
zero-free region or an unconditional Omega theorem.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/--
The bidirectional actual-PNT transfer certificate at target exponent `beta`.

The first field is the upper/reverse equivalence.  The second is the
constant-sensitive lower transfer in the nonempty case.  The final two fields
certify the common dynamically selected truncation height.
-/
structure ActualWeightedBalancedGoodHeightPNTBidirectionalTransferCertificate
    {beta c q : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) : Prop where
  empty_cluster_iff_error_negligible :
    S = ∅ ↔
      NaturalPointTargetAmplitudeNegligible
        (fun m => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
  nonempty_cluster_strict_oscillation :
    S.Nonempty →
      q < (c + q) / 2 ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => (c + q) / 2 * targetZeroPowerAmplitude beta x)
  selected_height_ratio :
    Tendsto
      (fun x =>
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x /
          x ^ actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau)
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
      (nhds (actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau))

/--
Unified bidirectional transfer for the actual relative Chebyshev error.

The same visible-cluster decomposition and dynamically selected good height
prove all four outputs.  In particular, the reverse implication reuses the
positive natural-point witness supplied by `hmain`; no conversion from an
arbitrary real witness back to a natural point is assumed.
-/
theorem actualWeightedBalancedGoodHeightPNTBidirectionalTransfer
    {beta c q : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hc : 0 < c)
    (hq : 0 ≤ q)
    (hqC : q < c)
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
    ActualWeightedBalancedGoodHeightPNTBidirectionalTransferCertificate
      (beta := beta) (c := c) (q := q) sigma tau selection S := by
  refine
    { empty_cluster_iff_error_negligible := ?_
      nonempty_cluster_strict_oscillation := ?_
      selected_height_ratio :=
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_div_optimalScale_tendsto_one
          sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      selected_height_log_growth :=
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_logGrowth_tendsto_optimalExponent
          sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection }
  · constructor
    · intro hEmpty
      subst S
      exact
        actualWeightedBalancedGoodHeightEmptyClusterPNTError_targetAmplitudeNegligible
          hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
          input kappa hfixedSigma hkappa hnorm hre hreal
    · intro herror
      exact
        actualWeightedBalancedGoodHeightPNTErrorNegligible_forces_emptyCluster
          hbeta hbetaOne hc sigma tau hsigma hsigmaOne htau hthreshold selection
          input kappa hS hfixedSigma hkappa hnorm hre hreal herror hmain
  · intro hNonempty
    exact
      actualWeightedBalancedGoodHeightPNTPreservesStrictOscillationThreshold
        hbeta hbetaOne hq hqC sigma tau hsigma hsigmaOne htau hthreshold
        selection input kappa hS hfixedSigma hkappa hnorm hre hreal
        (hmain hNonempty)

end PrimeNumberTheorem
