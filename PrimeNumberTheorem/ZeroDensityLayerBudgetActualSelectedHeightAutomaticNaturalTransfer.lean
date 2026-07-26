import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer

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

end PrimeNumberTheorem
