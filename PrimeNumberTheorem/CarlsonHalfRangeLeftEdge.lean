import PrimeNumberTheorem.CarlsonHalfRangeAuxiliaryWindow
import PrimeNumberTheorem.CarlsonTwoScaleRectangle

/-! The left logarithmic edge for the two-scale Carlson detector.  The first
bridge keeps nonvanishing explicit; the final theorem supplies a selected
zero-free line.  All mean-square inputs are supplied unconditionally. -/

open Complex Filter MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

/-- Carlson's quadratic detector converts error energy to logarithmic norm
without a square-root loss. -/
theorem log_norm_twoScaleCarlsonZeroDetector_le_error_sq
    (Y0 Y1 : ℕ) (s : ℂ) :
    Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 s‖ ≤
      ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2 := by
  let f := twoScaleMollifiedZetaError Y0 Y1 s
  by_cases hdet : twoScaleCarlsonZeroDetector Y0 Y1 s = 0
  · rw [hdet, norm_zero, Real.log_zero]
    exact sq_nonneg _
  · have hnorm : ‖twoScaleCarlsonZeroDetector Y0 Y1 s‖ ≤ 1 + ‖f‖ ^ 2 := by
      change ‖1 - f ^ 2‖ ≤ 1 + ‖f‖ ^ 2
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖f ^ 2‖ := norm_sub_le _ _
        _ = _ := by simp
    exact (Real.log_le_log (norm_pos_iff.mpr hdet) hnorm).trans
      (by simpa only [add_sub_cancel_left] using
        Real.log_le_sub_one_of_pos (show 0 < 1 + ‖f‖ ^ 2 by positivity))

private theorem intervalIntegrable_log_detector {x u v : ℝ} {Y0 Y1 : ℕ}
    (hx : x ∈ Icc (1 / 2 : ℝ) (2 / 3)) (huv : u ≤ v)
    (hne : ∀ t ∈ Icc u v,
      twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) ≠ 0) :
    IntervalIntegrable (fun t : ℝ =>
      Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖)
      volume u v := by
  have hdet : Continuous fun t : ℝ =>
      twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hs1 : (x : ℂ) + I * (t : ℂ) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
        sub_self, add_zero, Complex.one_re] at hre
      linarith [hx.2]
    have hpoint : ContinuousAt (fun w : ℝ => (x : ℂ) + I * (w : ℂ)) t := by fun_prop
    simpa only [Function.comp_def] using
      (analyticAt_twoScaleCarlsonZeroDetector_of_ne_one Y0 Y1 hs1).continuousAt.comp
        (f := fun w : ℝ => (x : ℂ) + I * (w : ℂ)) hpoint
  have hlog : ContinuousOn (fun t : ℝ =>
      Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖)
      (Icc u v) := hdet.norm.continuousOn.log fun t ht => norm_ne_zero_iff.mpr (hne t ht)
  exact (show ContinuousOn _ (uIcc u v) by simpa only [uIcc_of_le huv] using hlog).intervalIntegrable

/-- Uniform left-logarithmic-edge bound on any zero-free selected subinterval.
This theorem supplies its own energy estimate and logarithmic integrability. -/
theorem exists_eventually_halfRange_leftEdge_logIntegral_le :
    ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
      ∀ x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
      ∀ u v : ℝ, 2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
        (∀ t ∈ Icc u v, twoScaleCarlsonZeroDetector
          (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ)) ≠ 0) →
        IntervalIntegrable (fun t : ℝ => Real.log ‖twoScaleCarlsonZeroDetector
          (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ))‖) volume u v ∧
        (∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector
          (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ))‖) ≤
          K * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 := by
  obtain ⟨K, hK, hmoment⟩ := exists_eventually_halfRange_auxiliary_subinterval_moment_le
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmoment] with V hmoment
  intro x hx u v hu hv huv hne
  obtain ⟨henergyInt, henergy⟩ := hmoment x hx u v hu hv huv
  have hlogInt := intervalIntegrable_log_detector (halfRangeAuxiliary_bounds hx).1 huv hne
  refine ⟨hlogInt, ?_⟩
  apply (intervalIntegral.integral_mono_on huv hlogInt henergyInt ?_).trans henergy
  intro t ht
  exact log_norm_twoScaleCarlsonZeroDetector_le_error_sq _ _ _

/-- An actual zero-free left line with the power-log bound on every inner
height subinterval.  There is no remaining boundary-selection premise. -/
theorem exists_eventually_halfRange_selectedLeftEdge_logIntegral_le :
    ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
      ∃ x ∈ Ioo halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
        (1 / 20000 : ℝ) ≤ 2 / 3 - x ∧
        (∀ t ∈ Icc (2 * V) (5 * V / 2), twoScaleCarlsonZeroDetector
          (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ)) ≠ 0) ∧
        ∀ u v : ℝ, 2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
          IntervalIntegrable (fun t : ℝ => Real.log ‖twoScaleCarlsonZeroDetector
            (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
            ((x : ℂ) + I * (t : ℂ))‖) volume u v ∧
          (∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector
            (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
            ((x : ℂ) + I * (t : ℂ))‖) ≤
            K * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 := by
  obtain ⟨K, hK, hleft⟩ := exists_eventually_halfRange_leftEdge_logIntegral_le
  refine ⟨K, hK, ?_⟩
  filter_upwards [hleft, eventually_halfRangeCutoff_conditions] with V hleft hparams
  obtain ⟨hV, hY0, hY01, _⟩ := hparams
  obtain ⟨x, hx, hreg⟩ := exists_regularizedTwoScaleCarlson_vertical_ne_zero
    (a := 2 * V) (b := 5 * V / 2) hY0 hY01
    (show 0 < halfRangeAuxiliaryLeft by norm_num [halfRangeAuxiliaryLeft])
    (show halfRangeAuxiliaryLeft < halfRangeAuxiliaryRight by
      norm_num [halfRangeAuxiliaryLeft, halfRangeAuxiliaryRight])
  have hxClosed : x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight := ⟨hx.1.le, hx.2.le⟩
  obtain ⟨hxStrip, hxWeight, hxPower⟩ := halfRangeAuxiliary_bounds hxClosed
  have hne : ∀ t ∈ Icc (2 * V) (5 * V / 2), twoScaleCarlsonZeroDetector
      (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
      ((x : ℂ) + I * (t : ℂ)) ≠ 0 := by
    intro t ht hzero
    let s : ℂ := (x : ℂ) + I * (t : ℂ)
    have hsre : s.re = x := by simp [s]
    have hs0 : s ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hsre, Complex.zero_re] at hre
      linarith [hxStrip.1]
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hsre, Complex.one_re] at hre
      linarith [hxStrip.2]
    apply hreg t ht
    rw [regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hs0 hs1, hzero, mul_zero]
  refine ⟨x, hx, hxWeight, hne, ?_⟩
  intro u v hu hv huv
  apply hleft x hxClosed u v hu hv huv
  intro t ht
  exact hne t ⟨hu.trans ht.1, ht.2.trans hv⟩

end PrimeNumberTheorem.CarlsonZeroDensity
