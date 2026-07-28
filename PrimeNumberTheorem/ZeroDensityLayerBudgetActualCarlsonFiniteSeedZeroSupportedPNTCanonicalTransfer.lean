import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedZeroSupportedPNTUnnormalizedTransfer

/-!
# Canonical zero-supported finite-seed PNT transfer

The zero-supported actual-PNT transfer is specialized to the canonical
surviving coefficient `c / 2`.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Canonical unsigned zero-supported actual-PNT transfer. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedCanonicalSharpRealTransfer
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
      OutsideClusterRealPartCap S beta ∧
      (∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho) ∧
      (∀ rho ∈ S,
        rho ∉ S₀ →
          rho ∉ realOrdinateNontrivialZerosFinset 0 →
            rho.re = beta) ∧
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
      exists_zeroSupportedActualCarlsonFiniteSeedGapClusterAndPsi0ErrorSharpRealTransfer
        selection hS₀ hhalf hone hbalance hq hqC hcap with
    ⟨S, hseed, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap, htransfer⟩
  exact
    ⟨S, hseed, by linarith, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap, htransfer⟩

/-- Canonical signed zero-supported actual-PNT transfer. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedCanonicalSharpSignedRealTransfer
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
      OutsideClusterRealPartCap S beta ∧
      (∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho) ∧
      (∀ rho ∈ S,
        rho ∉ S₀ →
          rho ∉ realOrdinateNontrivialZerosFinset 0 →
            rho.re = beta) ∧
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
      exists_zeroSupportedActualCarlsonFiniteSeedGapClusterAndPsi0ErrorSharpSignedRealTransfer
        selection hS₀ hhalf hone hbalance hq hqC hcap with
    ⟨S, hseed, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap, htransfer⟩
  exact
    ⟨S, hseed, by linarith, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap, htransfer⟩

end PrimeNumberTheorem
