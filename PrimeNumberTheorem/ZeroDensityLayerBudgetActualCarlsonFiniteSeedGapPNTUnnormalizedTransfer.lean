import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapTransferCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTLowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTSignedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Finite seeded Carlson transfer to the unnormalized PNT error

A finite rightmost or exceptional seed cluster is retained while the Carlson
boundary tail is captured automatically.  The only remaining input is the
visible-cluster oscillation witness for the resulting finite extension.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A conjugation-stable finite seed with an outside real-part cap extends to
a finite cluster that transfers its visible main-term witness to the actual
unnormalized `psi0(x) - x` error at every prescribed `0 <= q < c`. -/
theorem exists_actualCarlsonFiniteSeedGapClusterAndPsi0ErrorSharpRealTransfer
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
      exists_actualCarlsonFiniteSeedGapTransferCluster
        hS₀ hhalf hone hqC hcap with
    ⟨S, hseed, hS, hcapS, hreHigh, hreReal, hgap⟩
  refine ⟨S, hseed, hS, hcapS, hreHigh, hreReal, hgap, ?_⟩
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

/-- The same finite seeded construction transfers positive and negative
visible-cluster witnesses to a common signed `q * x^beta` certificate for the
actual unnormalized PNT error. -/
theorem exists_actualCarlsonFiniteSeedGapClusterAndPsi0ErrorSharpSignedRealTransfer
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
      exists_actualCarlsonFiniteSeedGapTransferCluster
        hS₀ hhalf hone hqC hcap with
    ⟨S, hseed, hS, hcapS, hreHigh, hreReal, hgap⟩
  refine ⟨S, hseed, hS, hcapS, hreHigh, hreReal, hgap, ?_⟩
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
