import PrimeNumberTheorem.CarlsonTwoScaleRightLog

set_option autoImplicit false

open Complex Filter MeasureTheory
open PrimeNumberTheorem.CarlsonZeroDensity

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    (8 / 9 : ℝ) ≤ (twoScaleCarlsonZeroDetector Y0 Y1 s).re :=
  eight_ninths_le_re_twoScaleCarlsonZeroDetector hY0 hY01 hs

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    -Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 s‖ ≤ (25 / 2 : ℝ) * (1 / (Y0 : ℝ) ^ 6) :=
  neg_log_norm_twoScaleCarlsonZeroDetector_le_inv_sixth hY0 hY01 hs

example : ∀ᶠ V : ℝ in atTop, ∀ u v : ℝ,
    2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
      IntervalIntegrable (fun t : ℝ => Real.log ‖twoScaleCarlsonZeroDetector
        (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
        ((4 : ℂ) + I * (t : ℂ))‖) volume u v ∧
      -(∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector
        (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
        ((4 : ℂ) + I * (t : ℂ))‖) ≤ 400 * V ^ (-7 / 5 : ℝ) :=
  eventually_halfRange_rightLogIntegral_le

#print axioms eight_ninths_le_re_twoScaleCarlsonZeroDetector
#print axioms neg_log_norm_twoScaleCarlsonZeroDetector_le_inv_sixth
#print axioms eventually_halfRange_rightLogIntegral_le
