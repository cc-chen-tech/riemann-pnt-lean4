import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedPNTSignedTransfer

/-!
# Quantitative signed transfer with Carlson boundary mass

Positive and negative visible-cluster witnesses survive in the actual relative
Chebyshev error after subtracting the explicit coefficient loss contributed by
zeros on the boundary `Re rho = beta`.

The signed visible-cluster witnesses remain external hypotheses.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Every nonnegative coefficient below the cluster coefficient minus twice the
positive-ordinate Carlson boundary mass survives with both signs. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpSignedTransfer_automatic
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
    (_hq : 0 ≤ q)
    (hqNet :
      q <
        c -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S)
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
    (HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ))) ∧
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  let boundary :=
    actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S
  let delta := c - q - 2 * boundary
  have hdelta : 0 < delta := by
    dsimp [delta, boundary]
    linarith
  have hresidual :=
    eventually_abs_selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTClusterResidual_lt_automatic
      selection hS hhalf hone hbalance hreHigh hreReal hdelta
  have happrox :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ)| <
          (c - q) * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [hresidual] with m hm
    convert hm using 1 <;> dsimp [delta, boundary] <;> ring
  constructor
  · have htransfer :=
      hmainPos.transfer_eventually_sub_lt
        (f := fun m => relativeChebyshevPsi0Error (m : ℝ))
        (loss := c - q) happrox
    convert htransfer using 1 <;> funext m <;> ring
  · have htransfer :=
      hmainNeg.transfer_eventually_sub_lt
        (f := fun m => relativeChebyshevPsi0Error (m : ℝ))
        (loss := c - q) happrox
    convert htransfer using 1 <;> funext m <;> ring

end PrimeNumberTheorem
