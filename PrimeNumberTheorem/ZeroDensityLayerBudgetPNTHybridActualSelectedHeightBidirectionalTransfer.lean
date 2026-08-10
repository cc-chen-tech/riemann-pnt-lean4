import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualSelectedHeightSharpTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTReverseClusterExclusion

/-!
# Bidirectional actual-PNT transfer at the optimized hybrid height

This certificate packages the mixed global/Carlson upper and lower transfer
around the same genuine relative Chebyshev error:

* an empty visible cluster is equivalent to target-scale negligibility;
* a nonempty cluster carrying a witness with coefficient `c` transfers every
  strict positive coefficient below `c`;
* the same selected height realizes the certified mixed affine optimum.

The bucket profile, real-ordinate gap, and cluster witness remain explicit
hypotheses.  No unconditional oscillation or zero-free theorem is asserted.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/-- Bidirectional actual-PNT transfer certificate for the optimized hybrid
global/Carlson selected-height chain. -/
structure ActualHybridSelectedHeightPNTBidirectionalTransferCertificate
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
        pntHybridAffineSelectedGoodHeight beta sigma tau selection x /
          x ^ pntHybridAffineBalancedExponent beta sigma tau)
      atTop (nhds 1)
  selected_height_log_growth :
    Tendsto
      (fun x =>
        Real.log
              (pntHybridAffineSelectedGoodHeight
                beta sigma tau selection x) /
          Real.log x)
      atTop
      (nhds (pntHybridAffineBalancedExponent beta sigma tau))

/-- The optimized hybrid chain gives a bidirectional transfer theorem for
the genuine relative PNT error and one common selected height. -/
theorem actualHybridSelectedHeightPNTBidirectionalTransfer
    {beta c : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hc : 0 < c)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (htau : ∀ i, 0 ≤ tau i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (pntHybridAffineSelectedGoodHeight
            beta sigma tau selection x)
          S (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      S.Nonempty →
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (pntHybridAffineSelectedGoodHeight
                beta sigma tau selection)
              S (m : ℝ))
          (fun m =>
            c * targetZeroPowerAmplitude beta (m : ℝ))) :
    ActualHybridSelectedHeightPNTBidirectionalTransferCertificate
      (beta := beta) (c := c) sigma tau selection S := by
  refine
    { empty_cluster_iff_error_negligible := ?_
      nonempty_cluster_all_strict_positive_oscillation := ?_
      selected_height_ratio :=
        pntHybridAffineSelectedGoodHeight_div_optimalScale_tendsto_one
          sigma tau hbetaOne hsigmaOneHigh hbudget selection
      selected_height_log_growth :=
        pntHybridAffineSelectedGoodHeight_logGrowth_tendsto_optimalExponent
          sigma tau hbetaOne hsigmaOneHigh hbudget selection }
  · constructor
    · intro hEmpty
      subst S
      have hEmptyInvariant :
          IsConjugationInvariantCluster (∅ : Finset ℂ) := by
        simp [IsConjugationInvariantCluster]
      have hresidual :=
        actualHybridSelectedHeightClusterResidual_targetNegligible
          hbeta hbetaOne sigma tau htau hsigmaOneHigh hbudget selection
          input kappa hEmptyInvariant hfixedSigma hkappa hnorm hre hreal
      simpa [dynamicVisibleClusterPNTMain,
        dynamicVisibleClusterPNTZeroSum] using hresidual
    · intro herror
      by_contra hEmpty
      have hNonempty : S.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hhalfPos : 0 < c / 2 := half_pos hc
      have hhalfLt : c / 2 < c := half_lt_self hc
      have happrox :=
        eventually_actualHybridSelectedHeightClusterResidual_lt_mul
          hbeta hbetaOne hhalfPos sigma tau htau hsigmaOneHigh hbudget
          selection input kappa hS hfixedSigma hkappa hnorm hre hreal
      have hwitness :
          HasFarNaturalPointTargetAmplitudeWitness
            (fun m => relativeChebyshevPsi0Error (m : ℝ))
            (fun m =>
              (c - c / 2) *
                targetZeroPowerAmplitude beta (m : ℝ)) :=
        (hmain hNonempty).transfer_eventually_sub_lt happrox
      exact
        (herror.not_hasFarNaturalPoint_mul
          (eventually_targetZeroPowerAmplitude_natural_pos beta)
          (sub_pos.mpr hhalfLt))
          hwitness
  · intro hNonempty q hq hqc
    exact
      actualHybridSelectedHeightClusterWitness_transfer_lt
        hbeta hbetaOne hq hqc sigma tau htau hsigmaOneHigh hbudget
        selection input kappa hS hfixedSigma hkappa hnorm hre hreal
        (hmain hNonempty)

end PrimeNumberTheorem
