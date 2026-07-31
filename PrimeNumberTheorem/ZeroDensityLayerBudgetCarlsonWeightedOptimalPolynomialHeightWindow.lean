import PrimeNumberTheorem.ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindow

namespace PrimeNumberTheorem

noncomputable section

/-- The power of the height in Carlson's classical zero-density estimate. -/
noncomputable def carlsonPolynomialDensitySlope (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

/-- The exact real-part threshold above which the Carlson-weighted polynomial
height budget has positive feasibility gap. -/
noncomputable def carlsonWeightedPolynomialCriticalRealPart (sigma : ℝ) : ℝ :=
  (sigma + carlsonPolynomialDensitySlope sigma) /
    (carlsonPolynomialDensitySlope sigma + 1)

/-- Carlson-specialized weighted feasibility gap. -/
noncomputable def carlsonWeightedPolynomialHeightFeasibilityGap
    (beta sigma : ℝ) : ℝ :=
  weightedPolynomialHeightFeasibilityGap beta sigma
    (carlsonPolynomialDensitySlope sigma)

/-- Carlson-specialized minimax common safety margin. -/
noncomputable def carlsonWeightedOptimalPolynomialHeightSafetyMargin
    (beta sigma : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightSafetyMargin beta sigma
    (carlsonPolynomialDensitySlope sigma)

/-- Carlson-specialized minimax inner height exponent. -/
noncomputable def carlsonWeightedOptimalPolynomialHeightInnerExponent
    (beta sigma : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightInnerExponent beta sigma
    (carlsonPolynomialDensitySlope sigma)

/-- Carlson-specialized minimax outer height exponent. -/
noncomputable def carlsonWeightedOptimalPolynomialHeightOuterExponent
    (beta sigma : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightOuterExponent beta sigma
    (carlsonPolynomialDensitySlope sigma)

/-- Carlson-specialized minimax logarithmic slack. -/
noncomputable def carlsonWeightedOptimalPolynomialHeightEpsilon
    (beta sigma : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightEpsilon beta sigma
    (carlsonPolynomialDensitySlope sigma)

theorem carlsonPolynomialDensitySlope_nonneg
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    0 ≤ carlsonPolynomialDensitySlope sigma := by
  unfold carlsonPolynomialDensitySlope
  exact mul_nonneg (mul_nonneg (by norm_num) hsigma) (sub_nonneg.mpr hsigmaOne)

theorem carlsonPolynomialDensitySlope_pos
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    0 < carlsonPolynomialDensitySlope sigma := by
  unfold carlsonPolynomialDensitySlope
  exact mul_pos (mul_pos (by norm_num) hsigma) (sub_pos.mpr hsigmaOne)

/-- The Carlson critical real part lies strictly between the density line and
one throughout the nontrivial strip. -/
theorem carlsonWeightedPolynomialCriticalRealPart_spec
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    sigma < carlsonWeightedPolynomialCriticalRealPart sigma ∧
      carlsonWeightedPolynomialCriticalRealPart sigma < 1 := by
  have hq : 0 < carlsonPolynomialDensitySlope sigma :=
    carlsonPolynomialDensitySlope_pos hsigma hsigmaOne
  have hden : 0 < carlsonPolynomialDensitySlope sigma + 1 := by
    linarith
  unfold carlsonWeightedPolynomialCriticalRealPart
  constructor
  · apply (lt_div_iff₀ hden).2
    have hgain := mul_pos hq (sub_pos.mpr hsigmaOne)
    nlinarith
  · apply (div_lt_iff₀ hden).2
    linarith

/-- Positivity of the Carlson-weighted feasibility gap is exactly the strict
critical-real-part condition. -/
theorem carlsonWeightedPolynomialHeightFeasibilityGap_pos_iff
    {beta sigma : ℝ} (hsigma : 0 ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    0 < carlsonWeightedPolynomialHeightFeasibilityGap beta sigma ↔
      carlsonWeightedPolynomialCriticalRealPart sigma < beta := by
  have hq : 0 ≤ carlsonPolynomialDensitySlope sigma :=
    carlsonPolynomialDensitySlope_nonneg hsigma hsigmaOne
  have hden : 0 < carlsonPolynomialDensitySlope sigma + 1 := by
    linarith
  unfold carlsonWeightedPolynomialHeightFeasibilityGap
    carlsonWeightedPolynomialCriticalRealPart
    weightedPolynomialHeightFeasibilityGap
  rw [div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- On the classical Carlson range, the exact weighted threshold strictly
improves the unit-slope critical half `(1 + sigma) / 2`. -/
theorem carlsonWeightedPolynomialCriticalRealPart_lt_criticalHalf
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    carlsonWeightedPolynomialCriticalRealPart sigma < (1 + sigma) / 2 := by
  have hsigmaPos : 0 < sigma := by
    linarith
  have hq : 0 < carlsonPolynomialDensitySlope sigma :=
    carlsonPolynomialDensitySlope_pos hsigmaPos hsigmaOne
  have hden : 0 < carlsonPolynomialDensitySlope sigma + 1 := by
    linarith
  have htwosigma : 0 < 2 * sigma - 1 := by
    linarith
  have hsquare : 0 < (2 * sigma - 1) * (2 * sigma - 1) :=
    mul_pos htwosigma htwosigma
  have hqOne : carlsonPolynomialDensitySlope sigma < 1 := by
    unfold carlsonPolynomialDensitySlope
    nlinarith
  have hproduct :
      0 < (1 - sigma) * (1 - carlsonPolynomialDensitySlope sigma) :=
    mul_pos (sub_pos.mpr hsigmaOne) (sub_pos.mpr hqOne)
  unfold carlsonWeightedPolynomialCriticalRealPart
  apply (div_lt_iff₀ hden).2
  nlinarith

/-- Complete strict-window specification after specializing the weighted
optimizer to Carlson's classical density slope. -/
theorem carlsonWeightedOptimalPolynomialHeightWindow_spec
    {beta sigma : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hcritical : carlsonWeightedPolynomialCriticalRealPart sigma < beta)
    (hbetaOne : beta < 1) :
    0 < carlsonWeightedOptimalPolynomialHeightSafetyMargin beta sigma ∧
      0 < carlsonWeightedOptimalPolynomialHeightInnerExponent beta sigma ∧
      carlsonWeightedOptimalPolynomialHeightInnerExponent beta sigma <
          carlsonWeightedOptimalPolynomialHeightOuterExponent beta sigma ∧
      1 - beta <
          carlsonWeightedOptimalPolynomialHeightInnerExponent beta sigma ∧
      carlsonPolynomialDensitySlope sigma *
            carlsonWeightedOptimalPolynomialHeightOuterExponent beta sigma +
          carlsonWeightedOptimalPolynomialHeightEpsilon beta sigma <
        beta - sigma ∧
      carlsonWeightedOptimalPolynomialHeightInnerExponent beta sigma ≤ 1 ∧
      0 < carlsonWeightedOptimalPolynomialHeightEpsilon beta sigma ∧
      carlsonPolynomialDensitySlope sigma *
            carlsonWeightedOptimalPolynomialHeightOuterExponent beta sigma +
          carlsonWeightedOptimalPolynomialHeightEpsilon beta sigma +
          carlsonWeightedOptimalPolynomialHeightSafetyMargin beta sigma =
        beta - sigma := by
  have hq : 0 ≤ carlsonPolynomialDensitySlope sigma :=
    (carlsonPolynomialDensitySlope_pos hsigma hsigmaOne).le
  have hcriticalSpec :=
    carlsonWeightedPolynomialCriticalRealPart_spec hsigma hsigmaOne
  have hbeta : 0 < beta := by
    linarith
  have hgap :
      0 < weightedPolynomialHeightFeasibilityGap beta sigma
        (carlsonPolynomialDensitySlope sigma) := by
    exact (carlsonWeightedPolynomialHeightFeasibilityGap_pos_iff
      hsigma.le hsigmaOne.le).2 hcritical
  simpa [carlsonWeightedOptimalPolynomialHeightSafetyMargin,
    carlsonWeightedOptimalPolynomialHeightInnerExponent,
    carlsonWeightedOptimalPolynomialHeightOuterExponent,
    carlsonWeightedOptimalPolynomialHeightEpsilon] using
    (weightedOptimalPolynomialHeightWindow_spec
      hbeta hbetaOne hsigma hq hgap)

/-- Carlson's weighted optimizer produces an actual selected-height growth
statement and natural-point explicit-formula remainder certificate. -/
theorem carlsonWeightedOptimalPolynomialSelectedHeight_spec
    {beta sigma : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hcritical : carlsonWeightedPolynomialCriticalRealPart sigma < beta)
    (hbetaOne : beta < 1)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ (m : ℕ) in Filter.atTop,
        selectedUniformGoodHeight
              (carlsonWeightedOptimalPolynomialHeightInnerExponent beta sigma)
              selection m ≤
          carlsonPolynomialHeight
            (carlsonWeightedOptimalPolynomialHeightOuterExponent beta sigma) m) ∧
      Filter.Tendsto
          (fun m : ℕ =>
            selectedUniformGoodHeight
              (carlsonWeightedOptimalPolynomialHeightInnerExponent beta sigma)
              selection m)
          Filter.atTop Filter.atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate beta
        (selectedUniformGoodHeight
          (carlsonWeightedOptimalPolynomialHeightInnerExponent beta sigma)
          selection) := by
  have hq : 0 ≤ carlsonPolynomialDensitySlope sigma :=
    (carlsonPolynomialDensitySlope_pos hsigma hsigmaOne).le
  have hcriticalSpec :=
    carlsonWeightedPolynomialCriticalRealPart_spec hsigma hsigmaOne
  have hbeta : 0 < beta := by
    linarith
  have hgap :
      0 < weightedPolynomialHeightFeasibilityGap beta sigma
        (carlsonPolynomialDensitySlope sigma) := by
    exact (carlsonWeightedPolynomialHeightFeasibilityGap_pos_iff
      hsigma.le hsigmaOne.le).2 hcritical
  simpa [carlsonWeightedOptimalPolynomialHeightInnerExponent,
    carlsonWeightedOptimalPolynomialHeightOuterExponent] using
    (weightedOptimalPolynomialSelectedHeight_spec
      hbeta hbetaOne hsigma hq hgap selection)

end

end PrimeNumberTheorem
