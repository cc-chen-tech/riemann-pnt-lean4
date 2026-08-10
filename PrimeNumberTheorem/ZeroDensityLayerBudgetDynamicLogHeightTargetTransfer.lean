import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicLogHeightTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTransfer

namespace PrimeNumberTheorem

open Filter

/-- A normalized nonnegative majorant tending to zero makes the dominated
signed remainder negligible on the target-amplitude scale.  This is the
interface needed after the kernel and density estimates have already been
divided by the target amplitude. -/
theorem targetAmplitudeNegligible_of_eventually_normalized_le_of_tendsto_zero
    {amplitude remainder majorant : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hmajorant : Tendsto majorant atTop (nhds 0))
    (hdominated :
      ∀ᶠ x in atTop, |remainder x| / amplitude x ≤ majorant x) :
    TargetAmplitudeNegligible amplitude remainder := by
  unfold TargetAmplitudeNegligible
  refine squeeze_zero' ?_ hdominated hmajorant
  filter_upwards [hamplitude] with x hx
  exact div_nonneg (abs_nonneg _) hx.le

/-- A finite dynamic Carlson strip budget controls a target-normalized signed
remainder whenever every strip has a strict negative limiting exponent.

The eventual domination hypothesis is deliberately explicit: instantiating it
with an actual zeta-zero layer is the remaining kernel-and-density bridge. -/
theorem
    targetAmplitudeNegligible_of_eventually_normalized_le_dynamicFiniteStripLogMajorant
    {n : ℕ} {height amplitude remainder : ℝ → ℝ}
    {beta alpha : ℝ}
    (sigma tau coefficient : Fin (n + 1) → ℝ)
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hlogGrowth :
      Tendsto
        (fun x : ℝ => Real.log (height x) / Real.log x)
        atTop (nhds alpha))
    (hmargin :
      ∀ i,
        tau i - beta +
            actualSelectedHeightStripCarlsonSlope (sigma i) * alpha <
          0)
    (hdominated :
      ∀ᶠ x in atTop,
        |remainder x| / amplitude x ≤
          dynamicFiniteStripLogMajorant
            height beta sigma tau coefficient x) :
    TargetAmplitudeNegligible amplitude remainder :=
  targetAmplitudeNegligible_of_eventually_normalized_le_of_tendsto_zero
    hamplitude
    (tendsto_dynamicFiniteStripLogMajorant_zero_of_logGrowth
      sigma tau coefficient hlogGrowth hmargin)
    hdominated

/-- The weighted-balanced selected good height automatically discharges every
finite Carlson strip exponent condition.  Only the actual normalized
kernel-density domination remains to be supplied. -/
theorem
    targetAmplitudeNegligible_of_eventually_normalized_le_actualWeightedBalancedGoodHeight_dynamicFiniteStripLogMajorant
    {beta : ℝ} {n : ℕ} {amplitude remainder : ℝ → ℝ}
    (sigma tau coefficient : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hdominated :
      ∀ᶠ x in atTop,
        |remainder x| / amplitude x ≤
          dynamicFiniteStripLogMajorant
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            beta sigma tau coefficient x) :
    TargetAmplitudeNegligible amplitude remainder :=
  targetAmplitudeNegligible_of_eventually_normalized_le_of_tendsto_zero
    hamplitude
    (tendsto_actualWeightedBalancedGoodHeight_dynamicFiniteStripLogMajorant_zero
      sigma tau coefficient hbetaOne hsigma hsigmaOne htau hthreshold
      selection)
    hdominated

end PrimeNumberTheorem
