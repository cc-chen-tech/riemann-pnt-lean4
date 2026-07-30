import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Unnormalized PNT oscillation after Carlson boundary loss

The real-variable balanced Carlson transfer is expressed here on the genuine
unnormalized Chebyshev error `psi0(x) - x`, at its correct `x^beta` scale.

The visible-cluster witnesses remain explicit external hypotheses, and their
coefficients retain the multiplicity and reciprocal-zero weights supplied by
the actual zeta kernel.
-/

namespace PrimeNumberTheorem

open Complex

/-- Boundary domination plus an external unsigned visible-cluster witness gives
some positive `q * x^beta` witness for `psi0(x) - x`. -/
theorem
    exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPsi0ErrorHasFarRealPoint
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
          chebyshevPsi0Error
          (fun x => q * x ^ beta) := by
  rcases
      exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarRealPoint
        selection hS hhalf hone hbalance hreHigh hreReal hnet hmain with
    ⟨q, hq, hwitness⟩
  exact
    ⟨q, hq,
      hwitness.relativeChebyshevPsi0Error_to_unnormalized⟩

/-- Boundary domination plus external positive and negative cluster witnesses
gives a common positive `q * x^beta` signed certificate for `psi0(x) - x`. -/
theorem
    exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPsi0ErrorSharpSignedRealWitnesses
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
          chebyshevPsi0Error
          (fun x => q * x ^ beta) := by
  rcases
      exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedRealWitnesses
        selection hS hhalf hone hbalance hreHigh hreReal hnet
          hmainPos hmainNeg with
    ⟨q, hq, hwitness⟩
  exact
    ⟨q, hq,
      hwitness.relativeChebyshevPsi0Error_to_unnormalized⟩

end PrimeNumberTheorem
