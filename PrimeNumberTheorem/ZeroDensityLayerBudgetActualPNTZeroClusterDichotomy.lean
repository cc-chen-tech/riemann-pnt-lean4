import PrimeNumberTheorem.ZeroDensityLayerBudgetEmptyClusterPNTUpper
import PrimeNumberTheorem.ZeroDensityLayerBudgetArbitrarilySharpSameFormulaBounds
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightUnifiedTransfer

/-!
# Actual PNT zero-cluster dichotomy

This file packages the two directions of the dynamic-height transfer machine for
the same actual relative Chebyshev error.

* If the visible cluster is empty, the actual PNT error is negligible relative
  to the target zero-power amplitude.
* If the visible cluster is nonempty and an external cluster oscillation witness
  is supplied, every strict threshold below its constant survives transfer to
  the actual PNT error.

Both alternatives use the same Carlson strip budget and the same selected
height, whose ratio and logarithmic growth have the certified optimal exponent.
The nonempty alternative deliberately does not construct the cluster witness;
that is the responsibility of the separate sharp-oscillation development.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/--
A two-sided transfer certificate for the actual relative PNT error.

The `cluster_case` field is a genuine dichotomy.  Its empty branch is an upper
transfer statement, while its nonempty branch preserves a strict oscillation
constant.  The remaining fields certify the common dynamic truncation height.
-/
structure ActualWeightedBalancedGoodHeightPNTZeroClusterDichotomyCertificate
    {beta c q : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (S : Finset ℂ) : Prop where
  cluster_case :
    (S = ∅ ∧
      NaturalPointTargetAmplitudeNegligible
        (fun m => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m => relativeChebyshevPsi0Error (m : ℝ))) ∨
    (S.Nonempty ∧
      q < (c + q) / 2 ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => (c + q) / 2 * targetZeroPowerAmplitude beta x))
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
The actual PNT zero-cluster dichotomy under explicit dynamic Carlson bucket
inputs.

The hypothesis `hmain` is conditional on `S.Nonempty`, so the empty-cluster
upper transfer requires no artificial oscillation witness.  Conversely, the
nonempty branch uses exactly the externally supplied visible-cluster witness
and loses only an arbitrarily chosen strict margin from `c` to `q`.
-/
theorem actualWeightedBalancedGoodHeightPNTZeroClusterDichotomy
    {beta c q : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
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
    ActualWeightedBalancedGoodHeightPNTZeroClusterDichotomyCertificate
      (beta := beta) (c := c) (q := q) sigma tau selection S := by
  refine
    { selected_height_ratio :=
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_div_optimalScale_tendsto_one
          sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      selected_height_log_growth :=
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_logGrowth_tendsto_optimalExponent
          sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      cluster_case := ?_ }
  by_cases hEmpty : S = ∅
  · left
    refine ⟨hEmpty, ?_⟩
    subst S
    exact
      actualWeightedBalancedGoodHeightEmptyClusterPNTError_targetAmplitudeNegligible
        hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
        input kappa hfixedSigma hkappa hnorm hre hreal
  · have hNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    right
    refine ⟨hNonempty, ?_⟩
    exact
      actualWeightedBalancedGoodHeightPNTPreservesStrictOscillationThreshold
        hbeta hbetaOne hq hqC sigma tau hsigma hsigmaOne htau hthreshold
        selection input kappa hS hfixedSigma hkappa hnorm hre hreal
        (hmain hNonempty)

end PrimeNumberTheorem
