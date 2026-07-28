import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBalancedHeight
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSignedReverseClusterExclusion

/-!
# One-sided reverse transfer at the balanced Carlson height

The balanced actual Carlson residual permits one-sided reverse conclusions.
An eventual PNT upper bound excludes a stronger positive finite-cluster
witness, while an eventual PNT lower bound excludes a stronger negative
finite-cluster witness.

The signed cluster witnesses remain explicit external hypotheses.
-/

open scoped Topology
open Filter

namespace PrimeNumberTheorem

open Complex

/-- An eventual one-sided upper bound excludes a stronger positive visible
cluster witness at the balanced selected height. -/
theorem selectedUniformGoodHeightActualCarlsonBalancedPNTEventualUpper_forces_emptyCluster_of_positiveWitness_automatic
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
        relativeChebyshevPsi0Error (m : ℝ) ≤
          q * targetZeroPowerAmplitude beta (m : ℝ))
    (hmainPos :
      S.Nonempty →
        HasFarNaturalPointPositiveTargetAmplitudeWitness
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
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (c - q) / 2) *
            targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmainPos hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (c - q) / 2 := by
    linarith
  exact
    (not_hasFarNaturalPointPositive_mul_of_eventually_le_mul
      hupper
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

/-- An eventual one-sided lower bound excludes a stronger negative visible
cluster witness at the balanced selected height. -/
theorem selectedUniformGoodHeightActualCarlsonBalancedPNTEventualLower_forces_emptyCluster_of_negativeWitness_automatic
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
    (hlower :
      ∀ᶠ m : ℕ in atTop,
        -(q * targetZeroPowerAmplitude beta (m : ℝ)) ≤
          relativeChebyshevPsi0Error (m : ℝ))
    (hmainNeg :
      S.Nonempty →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
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
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (c - q) / 2) *
            targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmainNeg hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (c - q) / 2 := by
    linarith
  exact
    (not_hasFarNaturalPointNegative_mul_of_eventually_neg_mul_le
      hlower
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

end PrimeNumberTheorem
