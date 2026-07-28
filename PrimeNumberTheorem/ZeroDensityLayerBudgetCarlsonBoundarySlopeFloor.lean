import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryGapBudget

/-!
# The positive Carlson slope floor below a fixed boundary zero

For `1 / 2 <= sigma <= beta < 1`, the classical Carlson slope

`4 * sigma * (1 - sigma)`

is bounded below by the positive constant `4 * beta * (1 - beta)`.
Consequently, allowing a strip threshold `sigma` to move upward toward a
fixed target real part `beta` does not make the density cost vanish.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- The classical Carlson slope is antitone on the right half of the critical
strip. -/
theorem carlsonClassicalDensitySlope_le_of_le_on_rightHalf
    {sigma beta : ℝ}
    (hsigmaHalf : 1 / 2 ≤ sigma)
    (hsigmaBeta : sigma ≤ beta) :
    4 * beta * (1 - beta) ≤ 4 * sigma * (1 - sigma) := by
  have hproduct :
      0 ≤ (beta - sigma) * (sigma + beta - 1) :=
    mul_nonneg (sub_nonneg.mpr hsigmaBeta) (by linarith)
  nlinarith

/-- Below a fixed `beta < 1`, endpoint-aware Carlson decay and contour
admissibility force a gap with a uniform positive lower bound independent of
the strip threshold. -/
theorem carlsonClassical_boundaryGap_exceeds_fixedBetaFloor
    {beta gap alpha sigma : ℝ}
    (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 < sigma)
    (hsigmaBeta : sigma ≤ beta)
    (hcontour : 1 - beta < alpha)
    (hdecay :
      targetAmplitudeStripEndpointExponent beta (beta - gap)
        (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0) :
    (4 * beta * (1 - beta)) * (1 - beta) < gap := by
  have hsigmaOne : sigma < 1 :=
    hsigmaBeta.trans_lt hbetaOne
  have hstripFloor :
      (4 * sigma * (1 - sigma)) * (1 - beta) < gap :=
    carlsonClassical_boundaryGap_exceeds_contourFloor
      hsigmaHalf hsigmaOne hcontour hdecay
  have hslope :
      4 * beta * (1 - beta) ≤ 4 * sigma * (1 - sigma) :=
    carlsonClassicalDensitySlope_le_of_le_on_rightHalf
      hsigmaHalf.le hsigmaBeta
  have hscale : 0 ≤ 1 - beta := sub_nonneg.mpr hbetaOne.le
  exact
    (mul_le_mul_of_nonneg_right hslope hscale).trans_lt hstripFloor

/--
The fixed positive slope floor persists for scale-dependent strip thresholds
and polynomial-height exponents.
-/
theorem eventually_fixedBetaGapFloor_of_movingCarlsonBoundaryDecay
    {beta : ℝ} {sigma alpha gap : ℕ → ℝ}
    (hbetaOne : beta < 1)
    (hsigmaHalf : ∀ᶠ m in atTop, 1 / 2 < sigma m)
    (hsigmaBeta : ∀ᶠ m in atTop, sigma m ≤ beta)
    (hcontour : ∀ᶠ m in atTop, 1 - beta < alpha m)
    (hdecay :
      ∀ᶠ m in atTop,
        targetAmplitudeStripEndpointExponent beta (beta - gap m)
          (carlsonClassicalPolynomialDensityExponent
            (alpha m) (sigma m)) < 0) :
    ∀ᶠ m in atTop,
      (4 * beta * (1 - beta)) * (1 - beta) < gap m := by
  filter_upwards
      [hsigmaHalf, hsigmaBeta, hcontour, hdecay] with
      m hsigmaHalfM hsigmaBetaM hcontourM hdecayM
  exact carlsonClassical_boundaryGap_exceeds_fixedBetaFloor
    hbetaOne hsigmaHalfM hsigmaBetaM hcontourM hdecayM

/--
No moving family of classical Carlson strips below a fixed
`1 / 2 < beta < 1` can simultaneously clear the contour threshold, make the
boundary-normalized exponent negative, and accommodate gaps tending to zero.
-/
theorem not_gap_tendsto_zero_of_movingCarlsonBoundaryDecay
    {beta : ℝ} {sigma alpha gap : ℕ → ℝ}
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hsigmaHalf : ∀ᶠ m in atTop, 1 / 2 < sigma m)
    (hsigmaBeta : ∀ᶠ m in atTop, sigma m ≤ beta)
    (hcontour : ∀ᶠ m in atTop, 1 - beta < alpha m)
    (hdecay :
      ∀ᶠ m in atTop,
        targetAmplitudeStripEndpointExponent beta (beta - gap m)
          (carlsonClassicalPolynomialDensityExponent
            (alpha m) (sigma m)) < 0) :
    ¬ Tendsto gap atTop (𝓝 0) := by
  intro hgap
  have hfloor :=
    eventually_fixedBetaGapFloor_of_movingCarlsonBoundaryDecay
      hbetaOne hsigmaHalf hsigmaBeta hcontour hdecay
  have hbetaPos : 0 < beta := by linarith
  have honeMinus : 0 < 1 - beta := sub_pos.mpr hbetaOne
  have hconstant :
      0 < (4 * beta * (1 - beta)) * (1 - beta) := by
    positivity
  have hsmall :
      ∀ᶠ m in atTop,
        gap m < (4 * beta * (1 - beta)) * (1 - beta) :=
    (tendsto_order.mp hgap).2 _ hconstant
  rcases (hfloor.and hsmall).exists with ⟨m, hlarge, hsmallM⟩
  exact lt_asymm hlarge hsmallM

/-- The preceding no-go applies directly to the selected actual-zero
complement gap of a dynamic equal-real-part package. -/
theorem not_dynamicBoundaryGap_tendsto_zero_of_movingCarlsonStrips
    {H : ℝ → ℝ} {beta : ℝ} {sigma alpha : ℕ → ℝ}
    (hright :
      ∀ m : ℕ, ∀ z ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
        z.re ≤ beta)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hsigmaHalf : ∀ᶠ m in atTop, 1 / 2 < sigma m)
    (hsigmaBeta : ∀ᶠ m in atTop, sigma m ≤ beta)
    (hcontour : ∀ᶠ m in atTop, 1 - beta < alpha m)
    (hdecay :
      ∀ᶠ m in atTop,
        targetAmplitudeStripEndpointExponent beta
          (beta - dynamicEqualRealPartOutsideGap H beta hright m)
          (carlsonClassicalPolynomialDensityExponent
            (alpha m) (sigma m)) < 0) :
    ¬ Tendsto
        (dynamicEqualRealPartOutsideGap H beta hright)
        atTop (𝓝 0) := by
  exact not_gap_tendsto_zero_of_movingCarlsonBoundaryDecay
    hbetaHalf hbetaOne hsigmaHalf hsigmaBeta hcontour hdecay

end PrimeNumberTheorem
