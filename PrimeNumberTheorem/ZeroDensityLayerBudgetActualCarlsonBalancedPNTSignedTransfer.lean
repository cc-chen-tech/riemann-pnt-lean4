import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedHeight
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSelectedHeightPNTSignedTransfer

/-!
# Conditional signed PNT transfer at the balanced Carlson height

The midpoint height exponent makes the actual Carlson complementary residual
target-negligible without abstract layer or norm-bound inputs.  External
positive and negative witnesses for the finite visible cluster therefore
survive in the actual relative Chebyshev error at every strictly smaller
coefficient.

This module does not construct those finite-cluster witnesses.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Balanced automatic signed transfer from a finite visible zeta cluster to
the actual relative Chebyshev error. -/
theorem selectedUniformGoodHeightActualCarlsonBalancedPNTSharpSignedTransfer_automatic
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
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
  have hresidual :=
    selectedUniformGoodHeightActualCarlsonBalancedPNTClusterResidual_automatic
      selection hS hhalf hone hbalance hreHigh hreReal
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
