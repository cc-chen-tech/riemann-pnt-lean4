import PrimeNumberTheorem.CarlsonTwoScaleRightLog
import PrimeNumberTheorem.LittlewoodRectangle

/-! The fixed right-edge argument variation of the unregularized two-scale
detector is bounded by pi at arbitrary heights. -/

open Complex MeasureTheory
open scoped Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

private theorem right_analytic (Y0 Y1 : ℕ) (t : ℝ) :
    AnalyticAt ℂ (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ)) := by
  apply analyticAt_twoScaleCarlsonZeroDetector_of_ne_one
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

private theorem right_slit {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (t : ℝ) :
    twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (t : ℂ)) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl ((by norm_num : (0 : ℝ) < 8 / 9).trans_le
    (eight_ninths_le_re_twoScaleCarlsonZeroDetector hY0 hY01 (by simp)))

/-- Genuine integrability and the exact argument endpoint formula, with no
choice of an argument branch along the path left as a premise. -/
theorem integral_twoScaleCarlson_rightArgument_eq {Y0 Y1 : ℕ}
    (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re)
      volume a b ∧
    (∫ t in a..b,
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re) =
      (twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (b : ℂ))).arg -
        (twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (a : ℂ))).arg := by
  have hcontinuous : Continuous fun t : ℝ =>
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (t : ℂ)) ≠ 0 := by
      intro hzero
      have hre := eight_ninths_le_re_twoScaleCarlsonZeroDetector hY0 hY01
        (s := (4 : ℂ) + I * (t : ℂ)) (by simp)
      rw [hzero, Complex.zero_re] at hre
      norm_num at hre
    have hlog := ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
      (right_analytic Y0 Y1 t) hne
    have hmap : ContinuousAt (fun u : ℝ => (4 : ℂ) + I * (u : ℂ)) t := by fun_prop
    have hcomp : ContinuousAt (fun u : ℝ =>
        logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (u : ℂ))) t := by
      simpa only [Function.comp_def] using hlog.continuousAt.comp
        (f := fun u : ℝ => (4 : ℂ) + I * (u : ℂ)) hmap
    exact Complex.continuous_re.continuousAt.comp hcomp
  have hInt : IntervalIntegrable (fun t : ℝ =>
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re)
      volume a b := hcontinuous.intervalIntegrable a b
  refine ⟨hInt, ?_⟩
  have hderiv (t : ℝ) : HasDerivAt
      (fun u : ℝ => (Complex.log (twoScaleCarlsonZeroDetector Y0 Y1
        ((4 : ℂ) + I * (u : ℂ)))).im)
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re t := by
    simpa only [Complex.ofReal_ofNat] using
      hasDerivAt_im_log_vertical_of_analyticAt (sigma := (4 : ℝ))
        (right_analytic Y0 Y1 t) (right_slit hY0 hY01 t)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hInt
  simpa only [Complex.log_im] using hFTC

theorem abs_integral_twoScaleCarlson_rightArgument_le_pi {Y0 Y1 : ℕ}
    (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (a b : ℝ) :
    |∫ t in a..b,
      (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re| ≤
      Real.pi := by
  rw [(integral_twoScaleCarlson_rightArgument_eq hY0 hY01 a b).2]
  have harg (t : ℝ) :
      |(twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (t : ℂ))).arg| < Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    exact Or.inl ((by norm_num : (0 : ℝ) < 8 / 9).trans_le
      (eight_ninths_le_re_twoScaleCarlsonZeroDetector hY0 hY01 (by simp)))
  exact le_of_lt ((abs_sub _ _).trans_lt (by linarith [harg a, harg b]))

end PrimeNumberTheorem.CarlsonZeroDensity
