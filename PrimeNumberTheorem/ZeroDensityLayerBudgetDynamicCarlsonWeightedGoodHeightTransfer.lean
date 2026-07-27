import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonProductComparison
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicReverseZeroFree

/-!
# Dynamic Carlson transfer at the weighted-balanced good height

The general dynamic Carlson theorem requires a cofinal height, its logarithmic
growth exponent, and the elementary window `1 < H(x) ≤ x`.  This module
discharges all three conditions for the actual weighted-balanced good height
shared with the explicit formula.
-/

namespace PrimeNumberTheorem

open Filter

/-- A selected good height below a polynomial scale with exponent at most one
eventually lies strictly between one and the evaluation point. -/
theorem eventually_selectedUniformGoodHeight_gt_one_le_self
    {alpha : ℝ}
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x in atTop,
      1 < selectedUniformGoodHeight alpha selection x ∧
        selectedUniformGoodHeight alpha selection x ≤ x := by
  have hcofinal :=
    selectedUniformGoodHeight_tendsto_atTop halpha selection
  have hlarge :
      ∀ᶠ x in atTop,
        2 ≤ selectedUniformGoodHeight alpha selection x :=
    (tendsto_atTop.1 hcofinal) 2
  filter_upwards
      [hlarge, eventually_selectedUniformGoodHeight_mem halpha selection,
        eventually_ge_atTop (1 : ℝ)] with x hxLarge hxSelected hx
  constructor
  · linarith
  · calc
      selectedUniformGoodHeight alpha selection x ≤ x ^ alpha :=
        hxSelected.2
      _ ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx halphaOne
      _ = x := by simp

/-- At the actual weighted-balanced selected good height, Carlson's proved
density estimate and the endpoint kernel automatically make the complete
finite positive-height zeta-layer norm sum negligible on the target-zero
power scale.

No count coefficient, dynamic-height limit, logarithmic growth, height
window, or strip exponent margin remains as an external hypothesis. -/
theorem
    actualZetaFiniteStrips_weightedBalancedGoodHeight_dynamicCarlson_layerNormSum_negligible
    {beta : ℝ} {n : ℕ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        ∑ i,
          dynamicPositivePNTLayerNorm
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            input i x) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have halpha : 0 < alpha := by
    simpa [alpha] using hspec.2.1
  have halphaOne : alpha ≤ 1 := by
    simpa [alpha] using hspec.2.2.1.le
  have hheight :
      Tendsto
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)
        atTop atTop :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_tendsto_atTop
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
  have hheightWindow :
      ∀ᶠ x in atTop,
        1 <
            actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection x ∧
          actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection x ≤
            x := by
    simpa [actualSelectedHeightFiniteStripWeightedBalancedGoodHeight,
      alpha] using
      eventually_selectedUniformGoodHeight_gt_one_le_self
        halpha halphaOne selection
  have hlogGrowth :
      Tendsto
        (fun x : ℝ =>
          Real.log
                (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                  beta sigma tau selection x) /
            Real.log x)
        atTop (nhds alpha) := by
    simpa [alpha] using
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_logGrowth_tendsto_optimalExponent
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
  have hmargin :
      ∀ i,
        tau i - beta +
            actualSelectedHeightStripCarlsonSlope (sigma i) * alpha <
          0 := by
    intro i
    have hraw := hspec.2.2.2.2 i
    rw [show
      tau i - beta +
            actualSelectedHeightStripCarlsonSlope (sigma i) * alpha =
          targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) by
        simp [targetAmplitudeStripEndpointExponent,
          carlsonClassicalPolynomialDensityExponent,
          carlsonPolynomialHeightDensityExponent,
          actualSelectedHeightStripCarlsonSlope]
        ring]
    simpa [alpha] using hraw
  exact
    actualZetaFiniteStrips_dynamicCarlsonLogHeight_layerNormSum_negligible
      input sigma tau kappa hfixedSigma hsigma hsigmaOne hkappa hnorm hre
      hheight hheightWindow hlogGrowth hmargin

end PrimeNumberTheorem
