import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedHeight
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTQuantitativeReverseClusterExclusion

/-!
# Quantitative reverse transfer at the balanced Carlson height

The balanced actual Carlson residual also supports the reverse direction.  If
the genuine relative PNT error is eventually bounded by `q A_beta`, while a
nonempty visible cluster would have a `c A_beta` far-point witness with
`q < c`, then the cluster must be empty.

The finite-cluster witness is external; no anti-cancellation theorem is
asserted here.
-/

open scoped Topology
open Filter

namespace PrimeNumberTheorem

open Complex

/-- A quantitative actual-PNT upper bound excludes a stronger nonempty visible
cluster at the balanced selected height. -/
theorem selectedUniformGoodHeightActualCarlsonBalancedPNTEventualUpper_forces_emptyCluster_automatic
    {S : Finset ℂ} {sigma beta c q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hq : 0 ≤ q)
    (hqC : q < c)
    (hupper :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| ≤
          q * targetZeroPowerAmplitude beta (m : ℝ))
    (hmain :
      S.Nonempty →
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    S = ∅ := by
  by_contra hEmpty
  have hNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hresidual :=
    selectedUniformGoodHeightActualCarlsonBalancedPNTClusterResidual_automatic
      selection hS hhalf hone hbalance hreHigh hreReal
  have hlossPos : 0 < (c - q) / 2 := half_pos (sub_pos.mpr hqC)
  have happrox :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hresidual hlossPos
  have hwitness :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (c - q) / 2) *
            targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmain hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (c - q) / 2 := by
    linarith
  exact
    (not_hasFarNaturalPoint_mul_of_eventually_abs_le_mul
      hupper
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

end PrimeNumberTheorem
