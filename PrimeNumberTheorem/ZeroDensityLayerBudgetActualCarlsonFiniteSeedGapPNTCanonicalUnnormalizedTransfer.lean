import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapPNTUnnormalizedTransfer

/-!
# Canonical finite seeded Carlson transfer constants

For a positive visible-cluster coefficient `c`, the finite seeded transfer
retains the prescribed seed and fixes the surviving PNT coefficient to `c / 2`.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A positive finite-seed visible-cluster coefficient admits a finite
extension and the canonical surviving unnormalized coefficient `c / 2`. -/
theorem exists_actualCarlsonFiniteSeedGapClusterAndPsi0ErrorCanonicalSharpRealTransfer
    {S₀ : Finset ℂ} {sigma beta c : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hc : 0 < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ S : Finset ℂ,
      (∀ rho ∈ S₀, rho ∈ S) ∧
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
      exists_actualCarlsonFiniteSeedGapClusterAndPsi0ErrorSharpRealTransfer
        selection hS₀ hhalf hone hbalance hq hqC hcap with
    ⟨S, hseed, hS, hreHigh, hreReal, hgap, htransfer⟩
  exact
    ⟨S, hseed, by linarith, hS, hreHigh, hreReal, hgap, htransfer⟩

/-- Positive and negative finite-seed visible-cluster witnesses transfer at
the same canonical coefficient `c / 2`. -/
theorem exists_actualCarlsonFiniteSeedGapClusterAndPsi0ErrorCanonicalSharpSignedRealTransfer
    {S₀ : Finset ℂ} {sigma beta c : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hc : 0 < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ S : Finset ℂ,
      (∀ rho ∈ S₀, rho ∈ S) ∧
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
      exists_actualCarlsonFiniteSeedGapClusterAndPsi0ErrorSharpSignedRealTransfer
        selection hS₀ hhalf hone hbalance hq hqC hcap with
    ⟨S, hseed, hS, hreHigh, hreReal, hgap, htransfer⟩
  exact
    ⟨S, hseed, by linarith, hS, hreHigh, hreReal, hgap, htransfer⟩

end PrimeNumberTheorem
