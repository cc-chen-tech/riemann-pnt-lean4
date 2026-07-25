import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonPolynomialHeightComposition

/-!
# Carlson target criterion with distinct strip endpoints

Carlson counts a strip from its lower real-part threshold `sigma`, while a
pointwise power-kernel bound must use its upper endpoint `tau`.  Consequently
the normalized exponent is

`densityExponent(sigma) + tau - beta`,

not `densityExponent(sigma) + sigma - beta`.  This file solves the resulting
polynomial-height feasibility inequality exactly and quantifies the cost of
positive strip width.
-/

namespace PrimeNumberTheorem

/-- Target-amplitude exponent for a strip counted at its lower endpoint and
bounded pointwise at its upper endpoint. -/
def targetAmplitudeStripEndpointExponent
    (beta tau densityExponent : ℝ) : ℝ :=
  densityExponent + tau - beta

/-- The endpoint-aware exponent is the zero-width exponent plus the strip
width. -/
theorem targetAmplitudeStripEndpointExponent_eq_base_add_width
    (beta sigma tau densityExponent : ℝ) :
    targetAmplitudeStripEndpointExponent beta tau densityExponent =
      targetAmplitudePintzCarlsonExponent beta sigma densityExponent +
        (tau - sigma) := by
  simp [targetAmplitudeStripEndpointExponent,
    targetAmplitudePintzCarlsonExponent]
  ring

/-- A nonnegative density cost cannot give target-normalized decay if the
strip upper endpoint reaches or passes the target real part. -/
theorem targetAmplitudeStripEndpointExponent_nonneg
    {beta tau densityExponent : ℝ}
    (hdensity : 0 ≤ densityExponent) (hbeta : beta ≤ tau) :
    0 ≤ targetAmplitudeStripEndpointExponent beta tau densityExponent := by
  simp [targetAmplitudeStripEndpointExponent]
  linarith

/-- Carlson target threshold for a strip counted at `sigma` and bounded at
the distinct upper endpoint `tau`. -/
noncomputable def carlsonStripEndpointTargetThreshold
    (sigma tau : ℝ) : ℝ :=
  let q := 4 * sigma * (1 - sigma)
  (tau + q) / (1 + q)

/-- Exact target region in which one polynomial height clears the contour
threshold and makes the endpoint-aware Carlson strip exponent negative. -/
theorem exists_carlsonPolynomialHeight_stripEndpoint_decay_iff
    {beta sigma tau : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0) ↔
      carlsonStripEndpointTargetThreshold sigma tau < beta := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    simpa [q, mul_assoc] using
      (carlsonClassicalDensitySlope_pos hsigma hsigmaOne)
  have hden : 0 < 1 + q := by linarith
  constructor
  · rintro ⟨alpha, hcontour, hdecay⟩
    have hdecay' : alpha * q + tau - beta < 0 := by
      simpa [targetAmplitudeStripEndpointExponent,
        carlsonClassicalPolynomialDensityExponent,
        carlsonPolynomialHeightDensityExponent, q, mul_assoc] using hdecay
    have hwindow : (1 - beta) * q < beta - tau := by
      nlinarith [mul_lt_mul_of_pos_right hcontour hq]
    dsimp [carlsonStripEndpointTargetThreshold]
    rw [div_lt_iff₀ hden]
    dsimp [q] at hwindow ⊢
    nlinarith
  · intro hthreshold
    have hwindow : (1 - beta) * q < beta - tau := by
      dsimp [carlsonStripEndpointTargetThreshold] at hthreshold
      rw [div_lt_iff₀ hden] at hthreshold
      dsimp [q] at hthreshold ⊢
      nlinarith
    have hwindow' : 1 - beta < (beta - tau) / q := by
      exact (lt_div_iff₀ hq).2 hwindow
    obtain ⟨alpha, hcontour, halphaUpper⟩ :=
      exists_between hwindow'
    refine ⟨alpha, hcontour, ?_⟩
    have hdecay : alpha * q < beta - tau :=
      (lt_div_iff₀ hq).1 halphaUpper
    simp [targetAmplitudeStripEndpointExponent,
      carlsonClassicalPolynomialDensityExponent,
      carlsonPolynomialHeightDensityExponent, q, mul_assoc]
    linarith

/-- The endpoint-aware threshold exceeds the zero-width threshold by exactly
the strip width divided by the positive Carlson denominator. -/
theorem carlsonStripEndpointTargetThreshold_sub_classical
    {sigma tau : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    carlsonStripEndpointTargetThreshold sigma tau -
        carlsonClassicalTargetThreshold sigma =
      (tau - sigma) /
        (1 + 4 * sigma * (1 - sigma)) := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    simpa [q, mul_assoc] using
      (carlsonClassicalDensitySlope_pos hsigma hsigmaOne)
  have hden : 1 + q ≠ 0 := ne_of_gt (by linarith)
  dsimp [carlsonStripEndpointTargetThreshold,
    carlsonClassicalTargetThreshold]
  dsimp [q] at hden ⊢
  field_simp
  ring

/-- Every positive strip width strictly raises the target real-part threshold
required by Carlson's classical exponent. -/
theorem carlsonClassicalTargetThreshold_lt_stripEndpoint
    {sigma tau : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hwidth : sigma < tau) :
    carlsonClassicalTargetThreshold sigma <
      carlsonStripEndpointTargetThreshold sigma tau := by
  have hden :
      0 < 1 + 4 * sigma * (1 - sigma) := by
    have hq := carlsonClassicalDensitySlope_pos hsigma hsigmaOne
    linarith
  have hgap :
      0 <
        carlsonStripEndpointTargetThreshold sigma tau -
          carlsonClassicalTargetThreshold sigma := by
    rw [carlsonStripEndpointTargetThreshold_sub_classical
      hsigma hsigmaOne]
    exact div_pos (sub_pos.mpr hwidth) hden
  linarith

end PrimeNumberTheorem
