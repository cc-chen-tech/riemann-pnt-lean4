import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZetaStripEndpointKernel
import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicLogHeightTargetTransfer

/-!
# Actual zeta layers at a dynamic logarithmic height

This module connects the dynamic logarithmic Carlson majorant to the actual
multiplicity-weighted zeta-zero layer norm.  It deliberately keeps visible the
remaining arithmetic comparison between Carlson's raw count-kernel product
and the explicit logarithmic-height majorant.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

open Filter

/-- Finite actual-zeta layers are negligible on the target-zero power scale
once every normalized Carlson count-kernel product is eventually bounded by
its explicit dynamic logarithmic majorant.

The `hproduct` field is the exact remaining Carlson arithmetic bridge.  All
kernel, analytic-multiplicity, layer-domination, finite aggregation, and
target-amplitude transfer steps are automatic. -/
theorem
    actualZetaFiniteStrips_dynamicLogHeight_layerNormSum_negligible
    {n : ℕ} {height : ℝ → ℝ} {beta alpha : ℝ}
    (input : (x : ℝ) → PositiveZeroBucketInput (height x) (n + 1))
    (sigma tau kappa coefficient : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hlogGrowth :
      Tendsto
        (fun x : ℝ => Real.log (height x) / Real.log x)
        atTop (nhds alpha))
    (hmargin :
      ∀ i,
        tau i - beta +
            actualSelectedHeightStripCarlsonSlope (sigma i) * alpha <
          0)
    (hproduct :
      ∀ i,
        ∀ᶠ x in atTop,
          dynamicCarlsonLayerCount (sigma i) height x *
                stripEndpointRelativeKernelBudget (kappa i) (tau i) x /
              targetZeroPowerAmplitude beta x
            ≤
          coefficient i *
            dynamicLogHeightMajorant height
              (tau i - beta)
              (actualSelectedHeightStripCarlsonSlope (sigma i)) x) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        ∑ i,
          dynamicPositivePNTLayerNorm height input i x) := by
  apply
    targetAmplitudeNegligible_finset_sum_of_pintzCarlsonBudgets
      (targetZeroPowerAmplitude_eventually_pos beta)
      (Finset.univ : Finset (Fin (n + 1)))
      (fun i => dynamicPositivePNTLayerNorm height input i)
      (fun i => dynamicCarlsonLayerCount (sigma i) height)
      (fun i => stripEndpointRelativeKernelBudget (kappa i) (tau i))
  intro i hi
  apply
    dynamicPositivePNTLayerNorm_stripEndpointTargetLayerBudget
      input i (sigma i) (tau i) (kappa i)
      (hfixedSigma i) (hkappa i) (hnorm i) (hre i)
  refine squeeze_zero' ?_ (hproduct i) ?_
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta,
        eventually_ge_atTop (0 : ℝ)] with x hxAmplitude hx
    exact
      div_nonneg
        (mul_nonneg
          (dynamicCarlsonLayerCount_nonneg (sigma i) height x)
          (stripEndpointRelativeKernelBudget_nonneg hx (hkappa i).le))
        hxAmplitude.le
  · simpa only [mul_zero] using
      (tendsto_dynamicLogHeightMajorant_zero_of_logGrowth
        hlogGrowth (hmargin i)).const_mul (coefficient i)

end PrimeNumberTheorem
