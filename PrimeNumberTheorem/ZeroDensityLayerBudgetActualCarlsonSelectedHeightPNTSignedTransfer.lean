import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSelectedHeightPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSharpSignedOmega

/-!
# Conditional signed PNT transfer for pointwise Carlson gaps

This module transfers external positive and negative visible-cluster witnesses
through the actual PNT residual proved target-negligible by the pointwise-gap
Carlson chain.  It does not construct the cluster witnesses.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Positive and negative natural-point witnesses for the selected visible
cluster survive in the actual relative Chebyshev error at every smaller
coefficient `q < c`. -/
theorem selectedUniformGoodHeightActualCarlsonPNTSharpSignedTransfer
    {n : ℕ} {S : Finset ℂ}
    {sigma beta alpha kappa epsilon c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hkappa : 0 < kappa)
    (hnorm : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hreLow : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ (x : ℝ),
        ∀ rho ∈
            positiveNontrivialZerosOutsideClusterFinset
              (selectedUniformGoodHeight alpha selection x) S,
          rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (hepsilon : 0 < epsilon)
    (hlowMargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ))) ∧
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  have hresidual :=
    selectedUniformGoodHeightActualCarlsonPNTClusterResidual_targetNegligible
      selection input i hS hbeta hhalf hone hkappa hnorm hreLow
      hlowCover halpha halphaOne hcontourMargin hepsilon hlowMargin
      hreHigh hreReal
  have hloss : 0 < c - q := sub_pos.mpr hqC
  have happrox :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hresidual hloss
  constructor
  · have htransfer :=
      hmainPos.transfer_eventually_sub_lt
        (f := fun m => relativeChebyshevPsi0Error (m : ℝ))
        (loss := c - q) happrox
    convert htransfer using 1 <;> funext m <;> ring
  · have htransfer :=
      hmainNeg.transfer_eventually_sub_lt
        (f := fun m => relativeChebyshevPsi0Error (m : ℝ))
        (loss := c - q) happrox
    convert htransfer using 1 <;> funext m <;> ring

end PrimeNumberTheorem
