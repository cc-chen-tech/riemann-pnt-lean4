import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryCapturedPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTUnnormalizedCanonicalOscillation

/-!
# Unnormalized Carlson oscillation after boundary capture

If the visible finite cluster contains every indexed positive zero on
`Re rho = beta`, the outside Carlson boundary mass vanishes.  Consequently
every coefficient `q < c` from the visible cluster transfers to the genuine
unnormalized Chebyshev error at scale `q * x^beta`.
-/

namespace PrimeNumberTheorem

/-- Boundary capture transfers every nonnegative coefficient below `c` to an
unsigned real-point witness for `chebyshevPsi0 x - x`. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPsi0ErrorHasFarRealPoint_belowClusterConstant
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
    (hcapture :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index = beta →
          actualCarlsonPositiveZero index ∈ S)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarTargetAmplitudeWitness
      chebyshevPsi0Error
      (fun x => q * x ^ beta) := by
  have hrelative :=
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPNTHasFarNaturalPoint_belowClusterConstant
      selection hS hhalf hone hbalance hreHigh hreReal hcapture hq hqC hmain
  exact hrelative.toReal.relativeChebyshevPsi0Error_to_unnormalized

/-- Boundary capture transfers the same `q < c` simultaneously to positive and
negative real-point witnesses for the unnormalized error. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPsi0ErrorSharpSignedRealWitnesses_belowClusterConstant
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
    (hcapture :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index = beta →
          actualCarlsonPositiveZero index ∈ S)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarSignedTargetAmplitudeWitnesses
      chebyshevPsi0Error
      (fun x => q * x ^ beta) := by
  rcases
      selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPNTSharpSignedTransfer_automatic
        selection hS hhalf hone hbalance hreHigh hreReal hcapture hq hqC
          hmainPos hmainNeg with
    ⟨hpositive, hnegative⟩
  have hreal :
      HasFarSignedTargetAmplitudeWitnesses
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x) :=
    hasFarSignedTargetAmplitudeWitnesses_of_naturalPoint hpositive hnegative
  exact hreal.relativeChebyshevPsi0Error_to_unnormalized

/-- If `c` is positive, boundary capture yields the explicit unsigned
coefficient `c / 2` at scale `x^beta`. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPsi0ErrorHasFarRealPoint_halfClusterConstant
    {S : Finset ℂ} {sigma beta c : ℝ}
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
    (hcapture :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index = beta →
          actualCarlsonPositiveZero index ∈ S)
    (hc : 0 < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    0 < c / 2 ∧
      HasFarTargetAmplitudeWitness
        chebyshevPsi0Error
        (fun x => (c / 2) * x ^ beta) := by
  have hqPos : 0 < c / 2 := by linarith
  refine ⟨hqPos, ?_⟩
  apply
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPsi0ErrorHasFarRealPoint_belowClusterConstant
      (c := c) (q := c / 2) selection hS hhalf hone hbalance hreHigh hreReal
        hcapture hqPos.le
  · linarith
  · exact hmain

/-- If `c` is positive, boundary capture yields the explicit signed
coefficient `c / 2` at scale `x^beta`. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPsi0ErrorSharpSignedRealWitnesses_halfClusterConstant
    {S : Finset ℂ} {sigma beta c : ℝ}
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
    (hcapture :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index = beta →
          actualCarlsonPositiveZero index ∈ S)
    (hc : 0 < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    0 < c / 2 ∧
      HasFarSignedTargetAmplitudeWitnesses
        chebyshevPsi0Error
        (fun x => (c / 2) * x ^ beta) := by
  have hqPos : 0 < c / 2 := by linarith
  refine ⟨hqPos, ?_⟩
  apply
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryCapturedPsi0ErrorSharpSignedRealWitnesses_belowClusterConstant
      (c := c) (q := c / 2) selection hS hhalf hone hbalance hreHigh hreReal
        hcapture hqPos.le
  · linarith
  · exact hmainPos
  · exact hmainNeg

end PrimeNumberTheorem
