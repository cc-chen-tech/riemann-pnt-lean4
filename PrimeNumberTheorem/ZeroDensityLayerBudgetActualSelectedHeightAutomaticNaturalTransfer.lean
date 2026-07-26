import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStripCertificateChoice
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightBalancedCertificateChoice
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightBalancedExponentOptimality

/-!
# Automatic selected-height natural-point lower transfer

This module closes the analytic remainder side of the selected-height transfer
at natural points.  One uniform good-height selector is used simultaneously
for:

* the actual Carlson finite-strip complement certificate;
* the actual truncated explicit-formula remainder;
* the visible finite zero-cluster main term.

The only remaining lower-bound input is a natural-point witness for that main
cluster.  In particular, this theorem does not manufacture a cluster witness
and does not assert an unconditional oscillation theorem.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace PrimeNumberTheorem

/-- At one uniform polynomial good-height function, the Carlson outside-cluster
certificate and the automatic actual explicit-formula remainder certificate
transfer a natural-point main-cluster witness to the genuine relative
Chebyshev error.  The output retains half of the target zero-power amplitude.

The strict exponent margin `1 - beta < alpha` is exactly the condition used to
make the selected-height contour remainder negligible relative to
`x^(beta - 1)`. -/
theorem
    selectedUniformGoodHeight_actualNaturalPointRemainder_lowerTransfer
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x) S n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha S n
        (selectedUniformGoodHeight alpha selection) input)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) :=
  actualSelectedHeight_naturalPointRemainder_lowerTransfer
    hbeta certificate
    (selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hmargin selection)
    hmain

/-- Bidirectional automatic selected-height transfer on the genuine relative
Chebyshev error.

The upper component is the parametric Pintz--Carlson PNT decay theorem.  The
lower component uses the same selected height in the finite-strip complement,
the actual explicit-formula remainder, and the visible cluster.  Thus this is
one public interface for upper and lower transfer, while the mathematically
separate anti-cancellation statement remains the explicit hypothesis `hmain`.
-/
theorem
    unified_parametricPNTUpper_selectedUniformGoodHeight_actualNaturalPointLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x) S n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha S n
        (selectedUniformGoodHeight alpha selection) input)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) :=
  ⟨exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
      threshold hhalf hlt,
    selectedUniformGoodHeight_actualNaturalPointRemainder_lowerTransfer
      hbeta halpha halphaOne hmargin selection certificate hmain⟩

/-- Fully selected finite-strip bidirectional transfer.

Endpoint thresholds choose one shared polynomial exponent.  That exponent
chooses the uniform good-height schedule and automatic positive strip slacks.
The resulting actual Carlson certificate and actual explicit-formula remainder
certificate are then consumed by the bidirectional transfer.  The remaining
inputs are precisely the genuine zero-layer geometry and the independent
natural-point main-cluster witness.
-/
theorem
    unified_parametricPNTUpper_actualSelectedHeightThresholdsNaturalPointLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} {n : ℕ} (sigma tau : Fin n → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripChosenHeight beta sigma tau
            hbeta hbetaOne hsigma hsigmaOne hthreshold selection x)
          S n)
    (kappa : Fin n → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripChosenHeight beta sigma tau
              hbeta hbetaOne hsigma hsigmaOne hthreshold selection)
            S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hspec :=
    actualSelectedHeightFiniteStripExponent_spec beta sigma tau
      hbeta hbetaOne hsigma hsigmaOne hthreshold
  let certificate :=
    actualCarlsonOutsideClusterGoodHeightFiniteStripCertificate_of_thresholds
      sigma tau hbeta hbetaOne hsigma hsigmaOne hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  simpa [actualSelectedHeightFiniteStripChosenHeight,
    actualSelectedHeightFiniteStripChosenExponent] using
    (unified_parametricPNTUpper_selectedUniformGoodHeight_actualNaturalPointLower
      threshold hhalf hlt hbeta hspec.1 hspec.2.1 hspec.2.2.1
      selection certificate hmain)

/-- Explicit balanced-height version of the threshold-driven bidirectional
transfer.

The polynomial exponent is the concrete midpoint between `1 - beta` and the
minimum finite-strip Carlson ceiling (capped by `1`).  Thus the truncation
height is an explicit function of the target real part and strip endpoints,
not an opaque feasible choice.
-/
theorem
    unified_parametricPNTUpper_actualBalancedHeightThresholdsNaturalPointLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripBalancedHeight
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
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripBalancedHeight
              beta sigma tau selection)
            S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hspec :=
    actualSelectedHeightFiniteStripBalancedExponent_spec
      sigma tau hbeta hbetaOne hsigma hsigmaOne hthreshold
  let certificate :=
    actualCarlsonOutsideClusterBalancedGoodHeightFiniteStripCertificate
      sigma tau hbeta hbetaOne hsigma hsigmaOne hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  simpa [actualSelectedHeightFiniteStripBalancedHeight] using
    (unified_parametricPNTUpper_selectedUniformGoodHeight_actualNaturalPointLower
      threshold hhalf hlt hbeta hspec.1 hspec.2.1.le hspec.2.2.1
      selection certificate hmain)

/-- One theorem returning the three coordinated outputs of the explicit
balanced transfer:

* parametric Pintz--Carlson PNT upper decay;
* conditional target-scale oscillation of the genuine relative PNT error;
* positive, globally maximal, uniquely maximizing truncation robustness.

The optimality claim is exactly for the two-sided exponent safety margin, not
for every possible analytic cost functional.
-/
theorem
    unified_actualBalancedHeight_PNTUpper_naturalPointLower_optimalTruncation
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripBalancedHeight
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
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripBalancedHeight
              beta sigma tau selection)
            S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    ((∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
        Tendsto
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          atTop (nhds 0)) ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x => targetZeroPowerAmplitude beta x / 2)) ∧
    0 <
      actualSelectedHeightFiniteStripRobustMargin beta sigma tau
        (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau) ∧
    (∀ alpha : ℝ,
      actualSelectedHeightFiniteStripRobustMargin beta sigma tau alpha ≤
        actualSelectedHeightFiniteStripRobustMargin beta sigma tau
          (actualSelectedHeightFiniteStripBalancedExponent
            beta sigma tau)) ∧
    (∀ alpha : ℝ,
      actualSelectedHeightFiniteStripRobustMargin beta sigma tau
          (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau) ≤
        actualSelectedHeightFiniteStripRobustMargin beta sigma tau alpha →
      alpha =
        actualSelectedHeightFiniteStripBalancedExponent beta sigma tau) := by
  refine
    ⟨unified_parametricPNTUpper_actualBalancedHeightThresholdsNaturalPointLower
        threshold hhalf hlt sigma tau hbeta hbetaOne
        hsigma hsigmaOne hthreshold selection input kappa
        hS hfixedSigma hkappa hnorm hre hreal hmain,
      actualSelectedHeightFiniteStripBalancedExponent_robustMargin_pos
        sigma tau hbeta hsigma hsigmaOne hthreshold,
      ?_, ?_⟩
  · intro alpha
    exact
      actualSelectedHeightFiniteStripBalancedExponent_maximizes
        beta sigma tau alpha
  · intro alpha halpha
    exact
      actualSelectedHeightFiniteStripBalancedExponent_unique_maximizer
        beta sigma tau alpha halpha

end PrimeNumberTheorem
