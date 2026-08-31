import PrimeNumberTheorem.CarlsonTwoScaleFarRight
import PrimeNumberTheorem.CarlsonHalfRangeParameters

/-! The right logarithmic edge costs a decaying power, not a height-sized
constant.  All detector bounds and interval integrability are proved here. -/

open Complex Filter MeasureTheory
open scoped Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

theorem eight_ninths_le_re_twoScaleCarlsonZeroDetector
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    (8 / 9 : ℝ) ≤ (twoScaleCarlsonZeroDetector Y0 Y1 s).re := by
  let f : ℂ := twoScaleMollifiedZetaError Y0 Y1 s
  have hf : ‖f‖ ≤ (1 / 3 : ℝ) :=
    norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re hY0 hY01 hs
  have hre : (f ^ (2 : ℕ)).re ≤ ‖f‖ ^ 2 := by
    simpa only [norm_pow] using
      (le_abs_self (f ^ (2 : ℕ)).re).trans (Complex.abs_re_le_norm (f ^ (2 : ℕ)))
  change (8 / 9 : ℝ) ≤ (1 - f ^ 2 : ℂ).re
  simp only [Complex.sub_re, Complex.one_re]
  nlinarith [norm_nonneg f]

theorem neg_log_norm_twoScaleCarlsonZeroDetector_le_inv_sixth
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {s : ℂ} (hs : 4 ≤ s.re) :
    -Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 s‖ ≤
      (25 / 2 : ℝ) * (1 / (Y0 : ℝ) ^ 6) := by
  let f : ℂ := twoScaleMollifiedZetaError Y0 Y1 s
  let g : ℂ := twoScaleCarlsonZeroDetector Y0 Y1 s
  have hf : ‖f‖ ≤ (1 / 3 : ℝ) :=
    norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re hY0 hY01 hs
  have hg : (8 / 9 : ℝ) ≤ ‖g‖ :=
    eight_ninths_le_norm_twoScaleCarlsonZeroDetector_of_norm_error_le hf
  have hg0 : 0 < ‖g‖ := by linarith
  have hreverse : 1 - ‖f‖ ^ 2 ≤ ‖g‖ := by
    simpa [g, f, twoScaleCarlsonZeroDetector] using norm_sub_norm_le (1 : ℂ) (f ^ (2 : ℕ))
  have hinv : ‖g‖⁻¹ - 1 ≤ (9 / 8 : ℝ) * ‖f‖ ^ 2 := by
    rw [show ‖g‖⁻¹ - 1 = (1 - ‖g‖) / ‖g‖ by field_simp]
    apply (div_le_iff₀ hg0).mpr
    nlinarith [mul_nonneg (sq_nonneg ‖f‖) (sub_nonneg.mpr hg)]
  have hlog : -Real.log ‖g‖ ≤ (9 / 8 : ℝ) * ‖f‖ ^ 2 := by
    linarith [Real.one_sub_inv_le_log_of_pos hg0]
  have htail := norm_twoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube
    (show 1 ≤ Y0 by omega) hY01 hs
  calc
    _ ≤ (9 / 8 : ℝ) * ‖f‖ ^ 2 := hlog
    _ ≤ (9 / 8 : ℝ) * ((10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg f) htail 2) (by norm_num)
    _ = _ := by simp only [mul_pow, div_pow, one_pow, ← pow_mul]; norm_num; ring

/-- No zero-free premise is needed on the fixed right edge. -/
theorem continuous_twoScaleCarlson_rightLog {Y0 Y1 : ℕ}
    (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) :
    Continuous fun t : ℝ => Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1
      ((4 : ℂ) + I * (t : ℂ))‖ := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs1 : (4 : ℂ) + I * (t : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hnorm : (8 / 9 : ℝ) ≤ ‖twoScaleCarlsonZeroDetector Y0 Y1
      ((4 : ℂ) + I * (t : ℂ))‖ :=
    eight_ninths_le_norm_twoScaleCarlsonZeroDetector_of_norm_error_le
      (norm_twoScaleMollifiedZetaError_le_one_div_three_of_four_le_re hY0 hY01 (by simp))
  have hmap : ContinuousAt (fun u : ℝ => (4 : ℂ) + I * (u : ℂ)) t := by fun_prop
  have hdet : ContinuousAt (fun u : ℝ => twoScaleCarlsonZeroDetector Y0 Y1
      ((4 : ℂ) + I * (u : ℂ))) t := by
    simpa only [Function.comp_def] using
      (analyticAt_twoScaleCarlsonZeroDetector_of_ne_one Y0 Y1 hs1).continuousAt.comp
        (f := fun u : ℝ => (4 : ℂ) + I * (u : ℂ)) hmap
  exact hdet.norm.log (by linarith)

theorem eventually_halfRange_rightLogIntegral_le :
    ∀ᶠ V : ℝ in atTop, ∀ u v : ℝ,
      2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
        IntervalIntegrable (fun t : ℝ => Real.log ‖twoScaleCarlsonZeroDetector
          (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((4 : ℂ) + I * (t : ℂ))‖) volume u v ∧
        -(∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector
          (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((4 : ℂ) + I * (t : ℂ))‖) ≤ 400 * V ^ (-7 / 5 : ℝ) := by
  filter_upwards [eventually_halfRangeCutoff_conditions] with V hparams
  obtain ⟨hV, hY0, hY01, hY0U, hY1U, hY0L, _⟩ := hparams
  intro u v hu hv huv
  let Y0 := halfRangeCoreCutoff V
  let Y1 := halfRangeOuterCutoff V
  let F : ℝ → ℝ := fun t => Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1
    ((4 : ℂ) + I * (t : ℂ))‖
  have hV0 : 0 < V := by linarith
  have hInt : IntervalIntegrable F volume u v :=
    (continuous_twoScaleCarlson_rightLog hY0 hY01).intervalIntegrable u v
  refine ⟨hInt, ?_⟩
  have htail : 1 / (Y0 : ℝ) ^ 6 ≤ 64 * V ^ (-12 / 5 : ℝ) := by
    calc
      _ ≤ 1 / (V ^ (2 / 5 : ℝ) / 2) ^ 6 :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by positivity) hY0L 6)
      _ = 64 / V ^ (12 / 5 : ℝ) := by
        rw [div_pow, div_div_eq_mul_div, ← Real.rpow_mul_natCast hV0.le]
        norm_num
      _ = _ := by
        rw [show (-12 / 5 : ℝ) = -(12 / 5) by ring, Real.rpow_neg hV0.le, div_eq_mul_inv]
  have hpoint (t : ℝ) : -F t ≤ (25 / 2 : ℝ) * (1 / (Y0 : ℝ) ^ 6) :=
    neg_log_norm_twoScaleCarlsonZeroDetector_le_inv_sixth hY0 hY01 (by simp)
  have hbound := intervalIntegral.integral_mono_on huv hInt.neg
    (intervalIntegrable_const (c := (25 / 2 : ℝ) * (1 / (Y0 : ℝ) ^ 6)))
    (fun t _ => hpoint t)
  simp only [Pi.neg_apply] at hbound
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hpower : V * V ^ (-12 / 5 : ℝ) = V ^ (-7 / 5 : ℝ) := by
    calc
      _ = V ^ (1 : ℝ) * V ^ (-12 / 5 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hV0]; norm_num
  calc
    _ ≤ (v - u) * ((25 / 2 : ℝ) * (1 / (Y0 : ℝ) ^ 6)) := hbound
    _ ≤ (V / 2) * ((25 / 2 : ℝ) * (64 * V ^ (-12 / 5 : ℝ))) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left htail (by norm_num))
        (by positivity) (by positivity)
    _ = 400 * (V * V ^ (-12 / 5 : ℝ)) := by ring
    _ = _ := by rw [hpower]

end PrimeNumberTheorem.CarlsonZeroDensity
