import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTUnnormalizedOscillation

/-!
# Canonical unnormalized Carlson boundary oscillation constant

When the visible-cluster coefficient `c` strictly dominates twice the Carlson
boundary mass, half of the net coefficient is a canonical positive oscillation
constant.  This removes the existential coefficient from the unnormalized
real-point transfer.
-/

namespace PrimeNumberTheorem

/-- Half the net visible-cluster coefficient is a positive explicit constant
for the unnormalized unsigned PNT-error witness. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPsi0ErrorHasFarRealPoint_halfNet
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
    (hnet : 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    0 <
        (c - 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S) / 2 ∧
      HasFarTargetAmplitudeWitness
        chebyshevPsi0Error
        (fun x =>
          ((c - 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S) / 2) *
            x ^ beta) := by
  let q :=
    (c - 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S) / 2
  have hqPos : 0 < q := by
    dsimp [q]
    linarith
  have hqNet :
      q < c - 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S := by
    dsimp [q]
    linarith
  have hrelative :=
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint_belowNetClusterConstant
      selection hS hhalf hone hbalance hreHigh hreReal hqPos.le hqNet hmain
  exact
    ⟨hqPos,
      hrelative.toReal.relativeChebyshevPsi0Error_to_unnormalized⟩

/-- The same canonical half-net coefficient works simultaneously for positive
and negative unnormalized PNT-error witnesses. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPsi0ErrorSharpSignedRealWitnesses_halfNet
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
    (hnet : 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S < c)
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
    0 <
        (c - 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S) / 2 ∧
      HasFarSignedTargetAmplitudeWitnesses
        chebyshevPsi0Error
        (fun x =>
          ((c - 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S) / 2) *
            x ^ beta) := by
  let q :=
    (c - 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S) / 2
  have hqPos : 0 < q := by
    dsimp [q]
    linarith
  have hqNet :
      q < c - 2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S := by
    dsimp [q]
    linarith
  rcases
      selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedTransfer_automatic
        selection hS hhalf hone hbalance hreHigh hreReal hqPos.le hqNet
          hmainPos hmainNeg with
    ⟨hpositive, hnegative⟩
  have hreal :
      HasFarSignedTargetAmplitudeWitnesses
        relativeChebyshevPsi0Error
        (fun x => q * targetZeroPowerAmplitude beta x) :=
    hasFarSignedTargetAmplitudeWitnesses_of_naturalPoint hpositive hnegative
  exact
    ⟨hqPos,
      hreal.relativeChebyshevPsi0Error_to_unnormalized⟩

end PrimeNumberTheorem
