import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedHeight
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSelectedHeightPNTLowerTransfer

/-!
# Conditional lower transfer at the balanced Carlson height

This module specializes the actual Carlson-explicit-formula lower transfer to
the midpoint height exponent.  The balanced choice removes the abstract layer
input, the norm lower bound, and the free height and epsilon parameters.

The finite-cluster witness remains an explicit hypothesis.  In particular,
this module does not prove a cluster anti-cancellation theorem.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A far natural-point witness for the visible finite zeta cluster at the
balanced selected height transfers to the actual relative Chebyshev error.
The conclusion loses only the standard factor `1 / 2` used to absorb the
target-negligible complementary residual. -/
theorem selectedUniformGoodHeightActualCarlsonBalancedPNTLowerTransfer_automatic
    {S : Finset ℂ} {sigma beta : ℝ}
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
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hbeta : 0 < beta := by
    linarith
  have hresidual :=
    selectedUniformGoodHeightActualCarlsonBalancedPNTClusterResidual_automatic
      selection hS hhalf hone hbalance hreHigh hreReal
  have hnatural :=
    hasFarNaturalPointTargetAmplitudeWitness_of_difference_negligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hresidual hmain
  exact HasFarNaturalPointTargetAmplitudeWitness.toReal hnatural

end PrimeNumberTheorem
