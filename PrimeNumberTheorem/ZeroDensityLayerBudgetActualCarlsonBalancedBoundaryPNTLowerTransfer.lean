import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedBoundaryPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedPNTLowerTransfer

/-!
# Quantitative lower transfer with Carlson boundary mass

If high-strip zeros outside the visible cluster may lie on `Re rho = beta`,
their positive-ordinate boundary mass creates an unavoidable coefficient loss.
This module records the exact surviving range: a visible-cluster witness with
coefficient `c` transfers to every coefficient

`q < c - 2 * actualCarlsonOutsideClusterBoundaryMass beta S`.

The visible-cluster witness remains an explicit input.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Every nonnegative coefficient strictly below the visible-cluster
coefficient minus twice the Carlson boundary mass survives in the actual
relative Chebyshev error. -/
theorem
    selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTHasFarNaturalPoint_belowNetClusterConstant
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
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            S (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarNaturalPointTargetAmplitudeWitness
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
  have htransfer :=
    hmain.transfer_eventually_sub_lt
      (f := fun m => relativeChebyshevPsi0Error (m : ℝ))
      (loss := c - q) happrox
  convert htransfer using 1 <;> funext m <;> ring

end PrimeNumberTheorem
