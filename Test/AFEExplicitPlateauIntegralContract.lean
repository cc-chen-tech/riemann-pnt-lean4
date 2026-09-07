import HardyTheorem.AFEExplicitPlateauIntegral

open HardyTheorem AFE MeasureTheory

example {C₁ x N p : ℝ} (hx : 1 < x) (hxN : x ≤ N) (hp : 0 ≤ p)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∫ u in (x - 1)..(N + 1), |explicitIntervalPlateauDeriv x N u| * u ^ (-p)) ≤
      4 * C₁ * (x - 1) ^ (-p) :=
  intervalIntegral_abs_plateauDeriv_mul_rpow_le hx hxN hp hC₁0 hC₁

example {C₁ C₂ x N p : ℝ} (hx : 1 < x) (hxN : x ≤ N) (hp : 0 ≤ p)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    (∫ u in (x - 1)..(N + 1), |explicitIntervalPlateauSecondDeriv x N u| * u ^ (-p)) ≤
      2 * (2 * C₂ + 2 * C₁ ^ 2) * (x - 1) ^ (-p) :=
  intervalIntegral_abs_plateauSecondDeriv_mul_rpow_le hx hxN hp hC₁0 hC₂0 hC₁ hC₂

#print axioms intervalIntegral_abs_plateauDeriv_mul_rpow_le
#print axioms intervalIntegral_abs_plateauSecondDeriv_mul_rpow_le
