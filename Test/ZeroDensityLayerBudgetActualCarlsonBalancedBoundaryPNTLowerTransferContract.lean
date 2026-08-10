import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTLowerTransfer

open scoped Topology

open Complex Filter

namespace PrimeNumberTheorem

example
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
    (hq : 0 ≤ q)
    (hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S)
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
      (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) :=
  selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint_belowNetClusterConstant
    selection hS hhalf hone hbalance hreHigh hreReal hq hqNet hmain

end PrimeNumberTheorem
