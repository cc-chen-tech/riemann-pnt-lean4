import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedZeroSupportedSelector
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTLowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTSignedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Zero-supported finite-seed transfer to the unnormalized PNT error

The finite seeded Carlson transfer is rebuilt with the zero-supported
selector.  Its selected extension now publicly certifies that every newly
adjoined member is a nontrivial zeta zero.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Unsigned actual-PNT transfer retaining zero support on the selected
extension. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedGapClusterAndPsi0ErrorSharpRealTransfer
    {S₀ : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ S : Finset ℂ,
      (∀ rho ∈ S₀, rho ∈ S) ∧
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
      exists_zeroSupportedExtension_actualCarlsonFiniteSeedGapTransferCluster
        hS₀ hhalf hone hqC hcap with
    ⟨S, hseed, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap⟩
  refine
    ⟨S, hseed, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap, ?_⟩
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
      selection hstable hhalf hone hbalance hreHigh hreReal hq hqNet hmain
  have hwitnessReal :
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x) :=
    hwitnessNatural.toReal
  exact hwitnessReal.relativeChebyshevPsi0Error_to_unnormalized

/-- Signed actual-PNT transfer retaining the same zero-support certificate. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedGapClusterAndPsi0ErrorSharpSignedRealTransfer
    {S₀ : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ S : Finset ℂ,
      (∀ rho ∈ S₀, rho ∈ S) ∧
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
      exists_zeroSupportedExtension_actualCarlsonFiniteSeedGapTransferCluster
        hS₀ hhalf hone hqC hcap with
    ⟨S, hseed, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap⟩
  refine
    ⟨S, hseed, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap, ?_⟩
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
      selection hstable hhalf hone hbalance hreHigh hreReal hq hqNet
        hmainPos hmainNeg
  have hwitnessReal :
      HasFarSignedTargetAmplitudeWitnesses
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x) :=
    ⟨hwitnessNatural.1.toReal, hwitnessNatural.2.toReal⟩
  exact hwitnessReal.relativeChebyshevPsi0Error_to_unnormalized

end PrimeNumberTheorem
