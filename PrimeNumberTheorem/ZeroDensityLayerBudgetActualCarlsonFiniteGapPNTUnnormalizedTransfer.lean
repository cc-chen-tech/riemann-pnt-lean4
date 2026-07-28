import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteGapTransferCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTLowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Finite-gap Carlson transfer to the unnormalized PNT error

This module selects a finite conjugation-stable cluster satisfying every
Carlson-side structural condition for a prescribed strict coefficient gap.
The only remaining input is the visible-cluster oscillation witness for that
selected cluster.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Under a global `Re rho <= beta` bound, every nonnegative `q < c` admits a
finite conjugation-stable cluster for which the balanced Carlson transfer
reduces the unnormalized `psi0(x) - x` oscillation to the visible-cluster
witness alone. -/
theorem exists_actualCarlsonFiniteGapClusterAndPsi0ErrorSharpRealTransfer
    {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q ∧
      (HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x => q * x ^ beta)) := by
  rcases
      exists_actualCarlsonFiniteGapTransferCluster
        hhalf hone hqC hre with
    ⟨S, hS, hreHigh, hreReal, hgap⟩
  refine ⟨S, hS, hreHigh, hreReal, hgap, ?_⟩
  intro hmain
  have hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S := by
    linarith
  have hwitnessNatural :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) :=
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint_belowNetClusterConstant
      selection hS hhalf hone hbalance hreHigh hreReal hq hqNet hmain
  have hwitnessReal :
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x) :=
    hwitnessNatural.toReal
  exact hwitnessReal.relativeChebyshevPsi0Error_to_unnormalized

end PrimeNumberTheorem
