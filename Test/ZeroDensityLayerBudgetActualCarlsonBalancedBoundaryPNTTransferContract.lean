import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTTransfer

open scoped Topology

open Complex Filter

namespace PrimeNumberTheorem

example
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
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ)| <
        (2 * actualCarlsonOutsideClusterBoundaryMass
              (sigma := sigma) beta S +
            delta) *
          targetZeroPowerAmplitude beta (m : ℝ) :=
  eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
    selection hS hhalf hone hbalance hreHigh hreReal hdelta

end PrimeNumberTheorem
