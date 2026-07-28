import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteGapPNTUnnormalizedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteGapPNTSignedUnnormalizedTransfer

/-!
# Canonical finite-gap Carlson transfer constants

For a positive visible-cluster coefficient `c`, this module fixes the surviving
unnormalized PNT coefficient to the explicit value `c / 2`.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A positive visible-cluster coefficient admits an automatically selected
finite cluster and the canonical surviving unnormalized coefficient `c / 2`. -/
theorem exists_actualCarlsonFiniteGapClusterAndPsi0ErrorCanonicalSharpRealTransfer
    {sigma beta c : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hc : 0 < c)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) :
    ∃ S : Finset ℂ,
      0 < c / 2 ∧
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - c / 2 ∧
      (HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x => (c / 2) * x ^ beta)) := by
  have hq : 0 ≤ c / 2 := by positivity
  have hqC : c / 2 < c := by linarith
  rcases
      exists_actualCarlsonFiniteGapClusterAndPsi0ErrorSharpRealTransfer
        selection hhalf hone hbalance hq hqC hre with
    ⟨S, hS, hreHigh, hreReal, hgap, htransfer⟩
  exact ⟨S, by linarith, hS, hreHigh, hreReal, hgap, htransfer⟩

/-- The same automatically selected finite cluster construction transfers
positive and negative visible-cluster witnesses at the common canonical
coefficient `c / 2`. -/
theorem exists_actualCarlsonFiniteGapClusterAndPsi0ErrorCanonicalSharpSignedRealTransfer
    {sigma beta c : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hc : 0 < c)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) :
    ∃ S : Finset ℂ,
      0 < c / 2 ∧
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - c / 2 ∧
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
          (fun x => (c / 2) * x ^ beta)) := by
  have hq : 0 ≤ c / 2 := by positivity
  have hqC : c / 2 < c := by linarith
  rcases
      exists_actualCarlsonFiniteGapClusterAndPsi0ErrorSharpSignedRealTransfer
        selection hhalf hone hbalance hq hqC hre with
    ⟨S, hS, hreHigh, hreReal, hgap, htransfer⟩
  exact ⟨S, by linarith, hS, hreHigh, hreReal, hgap, htransfer⟩

end PrimeNumberTheorem
