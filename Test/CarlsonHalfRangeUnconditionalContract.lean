import PrimeNumberTheorem.CarlsonHalfRangeUnconditional

open Complex Filter MeasureTheory PrimeNumberTheorem CarlsonZeroDensity

-- An unconditional actual product moment, uniform in both centre and
-- mollifier length; no AFE or moment certificate appears as an input.
example : ∃ C > (0 : ℝ), ∀ᶠ V : ℝ in atTop, ∀ (w : ℝ) (X : ℕ),
    2 * V ≤ w → w ≤ 3 * V → 2 ≤ X → (X : ℝ) ≤ V ^ (9 / 20 : ℝ) →
    (∫ t : ℝ, carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
      ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
      C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6 :=
  exists_eventually_integral_gaussian_product_le_halfRange_powerLog

#print axioms exists_eventually_integral_gaussian_product_le_halfRange_powerLog
