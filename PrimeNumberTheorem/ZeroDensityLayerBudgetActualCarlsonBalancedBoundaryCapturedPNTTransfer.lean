import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassClusterCapture
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTLowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTSignedTransfer

/-!
# Balanced PNT transfer after capturing the Carlson boundary

If the visible finite cluster contains every indexed positive zero on
`Re rho = beta`, the explicit Carlson boundary coefficient vanishes.  The
boundary-mass residual is then arbitrarily small on the target scale, and every
strict coefficient `q < c` transfers from external cluster witnesses to the
actual relative Chebyshev error.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Capturing every indexed positive boundary zero removes the Carlson boundary
coefficient from the balanced actual-PNT residual. -/
theorem
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPNTClusterResidual_lt_automatic
    {S : Finset ℂ} {sigma beta delta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hcapture :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index = beta →
          actualCarlsonPositiveZero index ∈ S)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ)| <
        delta * targetZeroPowerAmplitude beta (m : ℝ) := by
  have hboundary :=
    actualCarlsonOutsideClusterBoundaryMass_eq_zero_of_boundary_captured
      S hcapture
  have hresidual :=
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hdelta
  simpa [hboundary] using hresidual

/-- Once every boundary zero is captured, every nonnegative coefficient
strictly below an external unsigned cluster coefficient survives in the actual
PNT error. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPNTHasFarNaturalPoint_belowClusterConstant
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hcapture :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index = beta →
          actualCarlsonPositiveZero index ∈ S)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m => relativeChebyshevPsi0Error (m : ℝ))
      (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  have hboundary :=
    actualCarlsonOutsideClusterBoundaryMass_eq_zero_of_boundary_captured
      S hcapture
  apply
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint_belowNetClusterConstant
      selection hS hhalf hone hbalance hreHigh hreReal hq
  · simpa [hboundary] using hqC
  · exact hmain

/-- Once every boundary zero is captured, positive and negative external
cluster witnesses transfer at every nonnegative coefficient `q < c`. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPNTSharpSignedTransfer_automatic
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hcapture :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index = beta →
          actualCarlsonPositiveZero index ∈ S)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ))) ∧
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  have hboundary :=
    actualCarlsonOutsideClusterBoundaryMass_eq_zero_of_boundary_captured
      S hcapture
  apply
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedTransfer_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hq
  · simpa [hboundary] using hqC
  · exact hmainPos
  · exact hmainNeg

end PrimeNumberTheorem
