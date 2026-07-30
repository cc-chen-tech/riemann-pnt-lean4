import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTLowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTSignedTransfer

/-!
# Nontrivial oscillation criterion after Carlson boundary loss

The quantitative boundary transfer produces a genuinely positive actual-PNT
witness coefficient exactly when the visible-cluster coefficient `c` exceeds
twice the positive-ordinate Carlson boundary mass.

The visible-cluster witnesses remain explicit external hypotheses.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- There exists a positive coefficient below the net cluster coefficient
`c - 2 * boundary` exactly when that net coefficient is positive. -/
theorem exists_pos_lt_cluster_sub_two_mul_boundary_iff
    {c boundary : ℝ} :
    (∃ q : ℝ, 0 < q ∧ q < c - 2 * boundary) ↔
      2 * boundary < c := by
  constructor
  · rintro ⟨q, hq, hqNet⟩
    linarith
  · intro hnet
    refine ⟨(c - 2 * boundary) / 2, ?_, ?_⟩
    · linarith
    · linarith

/-- If the external unsigned visible-cluster coefficient dominates twice the
Carlson boundary mass, the actual relative Chebyshev error has a witness with
some strictly positive coefficient on the target scale. -/
theorem
    exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint
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
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m => relativeChebyshevPsi0Error (m : ℝ))
          (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  rcases
      exists_pos_lt_cluster_sub_two_mul_boundary_iff.mpr hnet with
    ⟨q, hq, hqNet⟩
  refine ⟨q, hq, ?_⟩
  exact
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint_belowNetClusterConstant
      selection hS hhalf hone hbalance hreHigh hreReal hq.le hqNet hmain

/-- If external positive and negative cluster witnesses dominate twice the
Carlson boundary mass, the actual relative Chebyshev error has both signs with
one common strictly positive coefficient. -/
theorem
    exists_pos_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedWitnesses
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
        HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m => relativeChebyshevPsi0Error (m : ℝ))
          (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) ∧
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m => relativeChebyshevPsi0Error (m : ℝ))
          (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  rcases
      exists_pos_lt_cluster_sub_two_mul_boundary_iff.mpr hnet with
    ⟨q, hq, hqNet⟩
  rcases
      selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedTransfer_automatic
        selection hS hhalf hone hbalance hreHigh hreReal hq.le hqNet
          hmainPos hmainNeg with
    ⟨hpos, hneg⟩
  exact ⟨q, hq, hpos, hneg⟩

end PrimeNumberTheorem
