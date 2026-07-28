import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedHeight

/-!
# Balanced Carlson zero-free transfer to the actual PNT error

Taking the visible cluster to be empty turns the balanced complementary
residual theorem into an upper-bound transfer.  A strict real-part gap for all
actual nontrivial zeros then gives an `o(x^(beta - 1))` bound for the genuine
relative Chebyshev error along natural points.

The real-part gap is an explicit hypothesis.  Carlson density controls the
summation after that gap is supplied; it does not itself prove the gap.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Balanced automatic transfer from a global strict zero real-part gap to an
actual relative PNT error bound along natural points. -/
theorem selectedUniformGoodHeightActualCarlsonBalancedPNTUpperTransfer_automatic
    {sigma beta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m => relativeChebyshevPsi0Error (m : ℝ)) := by
  have hresidual :=
    selectedUniformGoodHeightActualCarlsonBalancedPNTClusterResidual_automatic
      (S := ∅) selection (by simp) hhalf hone hbalance
      (by
        intro index _
        exact hreHigh index)
      hreReal
  simpa [dynamicVisibleClusterPNTMain, dynamicVisibleClusterPNTZeroSum]
    using hresidual

end PrimeNumberTheorem
