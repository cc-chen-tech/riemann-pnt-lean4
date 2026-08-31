import PrimeNumberTheorem.CarlsonTwoScaleRightArgument

set_option autoImplicit false

open Complex MeasureTheory
open PrimeNumberTheorem.CarlsonZeroDensity

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re)
      volume a b ∧
    (∫ t in a..b,
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re) =
      (twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (b : ℂ))).arg -
        (twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (a : ℂ))).arg :=
  integral_twoScaleCarlson_rightArgument_eq hY0 hY01 a b

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (a b : ℝ) :
    |∫ t in a..b,
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re| ≤
      Real.pi := abs_integral_twoScaleCarlson_rightArgument_le_pi hY0 hY01 a b

#print axioms integral_twoScaleCarlson_rightArgument_eq
#print axioms abs_integral_twoScaleCarlson_rightArgument_le_pi
