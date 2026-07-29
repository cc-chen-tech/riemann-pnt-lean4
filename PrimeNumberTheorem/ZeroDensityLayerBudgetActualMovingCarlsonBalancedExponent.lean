import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonPointwiseNormalization

namespace PrimeNumberTheorem

theorem carlsonMovingBalancedCut_pos
    {alpha delta : ℝ} (hdelta : 0 < delta) (hquarter : delta < 1 / 4)
    (halpha : 0 < alpha) :
    0 < carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha := by
  apply carlsonTwoHeightBalancedCut_pos
  · linarith
  · linarith
  · exact halpha

theorem carlsonMovingBalancedCut_lt_alpha
    {alpha delta : ℝ} (hdelta : 0 < delta) (hquarter : delta < 1 / 4)
    (halpha : 0 < alpha) :
    carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha < alpha := by
  apply carlsonTwoHeightBalancedCut_lt_alpha
  · linarith
  · linarith
  · exact halpha

/-- The normalized low-height power is exactly the moving balanced exponent. -/
theorem carlsonMovingLowExponent_eq_balanced
    {alpha delta : ℝ} (hdelta : 0 < delta) (hquarter : delta < 1 / 4) :
    -delta +
        carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha *
          (4 * (1 - 2 * delta) * (1 - (1 - 2 * delta))) =
      carlsonTwoHeightBalancedExponent
        (1 - 2 * delta) (1 - delta) alpha := by
  have hsigma : 1 / 2 < 1 - 2 * delta := by linarith
  have hsigmaOne : 1 - 2 * delta < 1 := by linarith
  have hq :=
    carlsonTwoHeightDensityExponent_pos hsigma hsigmaOne
  have hden :
      carlsonTwoHeightDensityExponent (1 - 2 * delta) + 1 ≠ 0 := by
    linarith
  have hbalanced :=
    carlsonTwoHeightLowExponent_balanced
      (sigma := 1 - 2 * delta) (tau := 1 - delta) (alpha := alpha) hden
  rw [← hbalanced]
  simp only [carlsonTwoHeightLowExponent, carlsonRectangleExponent,
    carlsonClassicalPolynomialDensityExponent,
    carlsonPolynomialHeightDensityExponent,
    carlsonTwoHeightDensityExponent]
  ring

/-- The normalized high-height power is exactly the same moving balanced
exponent. -/
theorem carlsonMovingHighExponent_eq_balanced
    {alpha delta : ℝ} (hdelta : 0 < delta) (hquarter : delta < 1 / 4) :
    -delta -
        carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha +
          alpha * (4 * (1 - 2 * delta) * (1 - (1 - 2 * delta))) =
      carlsonTwoHeightBalancedExponent
        (1 - 2 * delta) (1 - delta) alpha := by
  have hsigma : 1 / 2 < 1 - 2 * delta := by linarith
  have hsigmaOne : 1 - 2 * delta < 1 := by linarith
  have hq :=
    carlsonTwoHeightDensityExponent_pos hsigma hsigmaOne
  have hden :
      carlsonTwoHeightDensityExponent (1 - 2 * delta) + 1 ≠ 0 := by
    linarith
  have hbalanced :=
    carlsonTwoHeightHighExponent_balanced
      (sigma := 1 - 2 * delta) (tau := 1 - delta) (alpha := alpha) hden
  rw [← hbalanced]
  simp only [carlsonTwoHeightHighExponent, carlsonRectangleExponent,
    carlsonClassicalPolynomialDensityExponent,
    carlsonPolynomialHeightDensityExponent,
    carlsonTwoHeightDensityExponent]
  ring

end PrimeNumberTheorem
