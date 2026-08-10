import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteGapTransferCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTSignedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Finite-gap signed Carlson transfer to the unnormalized PNT error

This module selects one finite conjugation-stable cluster for a prescribed
coefficient gap and transfers external positive and negative visible-cluster
witnesses to a common unnormalized `psi0(x) - x` scale.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Under a global `Re rho <= beta` bound, every nonnegative `q < c` admits one
finite cluster for which positive and negative visible-cluster witnesses imply
a common signed `q * x^beta` certificate for `psi0(x) - x`. -/
theorem exists_actualCarlsonFiniteGapClusterAndPsi0ErrorSharpSignedRealTransfer
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
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarSignedTargetAmplitudeWitnesses
          chebyshevPsi0Error
          (fun x => q * x ^ beta)) := by
  rcases
      exists_actualCarlsonFiniteGapTransferCluster
        hhalf hone hqC hre with
    ⟨S, hS, hreHigh, hreReal, hgap⟩
  refine ⟨S, hS, hreHigh, hreReal, hgap, ?_⟩
  intro hmainPos hmainNeg
  have hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S := by
    linarith
  have hwitnessNatural :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m => relativeChebyshevPsi0Error (m : ℝ))
          (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) ∧
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m => relativeChebyshevPsi0Error (m : ℝ))
          (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) :=
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedTransfer_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hq hqNet
        hmainPos hmainNeg
  have hwitnessReal :
      HasFarSignedTargetAmplitudeWitnesses
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x) :=
    ⟨hwitnessNatural.1.toReal, hwitnessNatural.2.toReal⟩
  exact hwitnessReal.relativeChebyshevPsi0Error_to_unnormalized

end PrimeNumberTheorem
