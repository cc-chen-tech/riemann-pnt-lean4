import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTNontrivialTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetSignedTargetAmplitudeRealTransfer

/-!
# Real-variable nontrivial PNT transfer after Carlson boundary loss

The positive natural-point coefficients supplied by the balanced boundary
transfer are embedded into the standard real-variable far-point interface for
the genuine relative Chebyshev error.

The visible-cluster witnesses remain explicit external hypotheses.
-/

namespace PrimeNumberTheorem

open Complex

/-- Boundary domination plus an external unsigned cluster witness yields a
strictly positive real-variable target-scale witness for the actual PNT error. -/
theorem
    exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarRealPoint
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
    (hnet :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    ∃ q : ℝ,
      0 < q ∧
        HasFarTargetAmplitudeWitness
          relativeChebyshevPsi0Error
          (fun x => q * targetZeroPowerAmplitude beta x) := by
  rcases
      exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint
        selection hS hhalf hone hbalance hreHigh hreReal hnet hmain with
    ⟨q, hq, hwitness⟩
  exact ⟨q, hq, hwitness.toReal⟩

/-- Boundary domination plus external positive and negative cluster witnesses
yields a strictly positive real-variable signed target-scale certificate for
the actual PNT error. -/
theorem
    exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedRealWitnesses
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
    (hnet :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        c)
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
    ∃ q : ℝ,
      0 < q ∧
        HasFarSignedTargetAmplitudeWitnesses
          relativeChebyshevPsi0Error
          (fun x => q * targetZeroPowerAmplitude beta x) := by
  rcases
      exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedWitnesses
        selection hS hhalf hone hbalance hreHigh hreReal hnet
          hmainPos hmainNeg with
    ⟨q, hq, hpositive, hnegative⟩
  exact
    ⟨q, hq,
      hasFarSignedTargetAmplitudeWitnesses_of_naturalPoint
        hpositive hnegative⟩

end PrimeNumberTheorem
