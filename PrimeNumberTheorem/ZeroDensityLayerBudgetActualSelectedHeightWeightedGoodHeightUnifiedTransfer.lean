import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightOptimality
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightSameFormulaUpper

/-!
# Actual weighted good-height unified transfer

This file packages the outputs proved for the same selected explicit-formula
height:

* a quantitative upper bound for the relative PNT error;
* convergence of that relative error to zero;
* a target-amplitude oscillation witness supplied by the visible zero cluster;
* asymptotic equivalence of the selected height to the balanced power scale;
* convergence of its logarithmic growth exponent to the balanced exponent.

The cluster anti-cancellation input remains the explicit hypothesis `hmain`.
Thus this certificate is a transfer theorem, not an unconditional oscillation
theorem.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
The complete same-formula output at the selected weighted balanced good height.

The upper and lower conclusions concern the same relative Chebyshev error and
the same target amplitude.  The two height conclusions certify that the
explicit-formula truncation used by the transfer has the balanced asymptotic
scale, rather than merely lying in an unspecified admissible range.
-/
structure ActualWeightedBalancedGoodHeightUnifiedTransferCertificate
    {beta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) : Prop where
  eventual_pnt_upper :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        (finiteVisibleClusterPNTAmplitudeCoefficient S + 1 / 2) *
          targetZeroPowerAmplitude beta (m : ℝ)
  pnt_relative_decay :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop
      (nhds 0)
  oscillation_lower :
    HasFarTargetAmplitudeWitness
      relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2)
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
The actual Pintz--Carlson--explicit-formula transfer at the selected weighted
balanced good height.

Once the finite visible cluster supplies `hmain`, the same dynamic-height
decomposition simultaneously yields the PNT upper bound, relative decay, and
the target-scale lower witness.  The selected truncation height is moreover
asymptotic to the balanced power scale and has the corresponding logarithmic
growth exponent.
-/
theorem
    unified_actualWeightedBalancedGoodHeightSameFormulaTransfer
    {beta : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (hclusterRe : ∀ rho ∈ S, rho.re ≤ beta)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S
            (m : ℝ))
        (fun m => targetZeroPowerAmplitude beta (m : ℝ))) :
    ActualWeightedBalancedGoodHeightUnifiedTransferCertificate
      (beta := beta) sigma tau selection S := by
  have htransfer :=
    unified_actualWeightedBalancedGoodHeightSameFormulaUpperLower
      hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
      hclusterRe input kappa hS hfixedSigma hkappa hnorm hre hreal hmain
  exact
    { eventual_pnt_upper := htransfer.1
      pnt_relative_decay := htransfer.2.1
      oscillation_lower := htransfer.2.2
      selected_height_ratio :=
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_div_optimalScale_tendsto_one
          sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      selected_height_log_growth :=
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_logGrowth_tendsto_optimalExponent
          sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection }

end PrimeNumberTheorem
