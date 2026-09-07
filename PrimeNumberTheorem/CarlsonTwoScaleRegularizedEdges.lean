import PrimeNumberTheorem.CarlsonTwoScaleRightArgument
import PrimeNumberTheorem.CarlsonLittlewood

/-! Exact regularization accounting on the vertical edges.  The elementary
factor `(s - 1)^2` does not increase the difference of logarithmic integrals;
its net right argument increment is at most `2 * pi`. -/

open Complex Filter MeasureTheory Set
open scoped Interval Topology

namespace PrimeNumberTheorem.CarlsonZeroDensity

theorem log_norm_regularizedTwoScale_eq {Y0 Y1 : ℕ} {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hne : twoScaleCarlsonZeroDetector Y0 Y1 s ≠ 0) :
    Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 s‖ =
      2 * Real.log ‖s - 1‖ + Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 s‖ := by
  rw [regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hs0 hs1,
    norm_mul, norm_pow,
    Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1)))
      (norm_ne_zero_iff.mpr hne), Real.log_pow]
  norm_num

theorem logDeriv_regularizedTwoScale_eq {Y0 Y1 : ℕ} {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hne : twoScaleCarlsonZeroDetector Y0 Y1 s ≠ 0) :
    logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) s =
      2 * (s - 1)⁻¹ + logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) s := by
  let p : ℂ → ℂ := fun z => (z - 1) ^ (2 : ℕ)
  have hfactor : regularizedTwoScaleCarlsonZeroDetector Y0 Y1 =ᶠ[𝓝 s]
      fun z => p z * twoScaleCarlsonZeroDetector Y0 Y1 z := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
    exact regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hz0 hz1
  have hlog : logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) s =
      logDeriv (fun z => p z * twoScaleCarlsonZeroDetector Y0 Y1 z) s := by
    simp only [logDeriv_apply]
    rw [hfactor.deriv_eq, hfactor.eq_of_nhds]
  have hpne : p s ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hs1)
  have hpdiff : DifferentiableAt ℂ p s := by dsimp [p]; fun_prop
  rw [hlog, logDeriv_mul s hpne hne hpdiff
    (analyticAt_twoScaleCarlsonZeroDetector_of_ne_one Y0 Y1 hs1).differentiableAt]
  have hpLog : logDeriv p s = 2 * (s - 1)⁻¹ := by
    dsimp [p]
    rw [logDeriv_fun_pow (n := 2) (by fun_prop)]
    simp [logDeriv_apply]
  rw [hpLog]

private theorem vertical_ne_real {x c : ℝ} (hxc : x ≠ c) (t : ℝ) :
    (x : ℂ) + I * (t : ℂ) ≠ (c : ℂ) := by
  intro h
  apply hxc
  simpa using congrArg Complex.re h

private theorem right_detector_ne {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (t : ℝ) :
    twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (t : ℂ)) ≠ 0 := by
  intro hzero
  have hre := eight_ninths_le_re_twoScaleCarlsonZeroDetector hY0 hY01
    (s := (4 : ℂ) + I * (t : ℂ)) (by simp)
  rw [hzero, Complex.zero_re] at hre
  norm_num at hre

private theorem continuous_vertical_log_subOne {x : ℝ} (hx1 : x ≠ 1) :
    Continuous (fun t : ℝ => Real.log ‖(x : ℂ) + I * (t : ℂ) - 1‖) := by
  apply Continuous.log (by fun_prop)
  intro t
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by
    simpa using vertical_ne_real hx1 t))

/-- Both summands and the regularized logarithm are integrable.  Only
nonvanishing on the actual vertical segment is required. -/
theorem integral_log_norm_regularizedTwoScale_eq {Y0 Y1 : ℕ} {x u v : ℝ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hne : ∀ t ∈ uIcc u v, twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + I * (t : ℂ))‖) volume u v ∧
    (∫ t in u..v, Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖) =
      2 * (∫ t in u..v, Real.log ‖(x : ℂ) + I * (t : ℂ) - 1‖) +
        ∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ := by
  have hrawCont : Continuous (fun t : ℝ =>
      twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hs1 : (x : ℂ) + I * (t : ℂ) ≠ 1 := by simpa using vertical_ne_real hx1 t
    have hmap : ContinuousAt (fun w : ℝ => (x : ℂ) + I * (w : ℂ)) t := by fun_prop
    simpa only [Function.comp_def] using
      (analyticAt_twoScaleCarlsonZeroDetector_of_ne_one Y0 Y1 hs1).continuousAt.comp
        (f := fun w : ℝ => (x : ℂ) + I * (w : ℂ)) hmap
  have hrawInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖) volume u v :=
    (hrawCont.norm.continuousOn.log (fun t ht => norm_ne_zero_iff.mpr (hne t ht))).intervalIntegrable
  have hlinInt : IntervalIntegrable (fun t : ℝ => Real.log ‖(x : ℂ) + I * (t : ℂ) - 1‖)
      volume u v := (continuous_vertical_log_subOne hx1).intervalIntegrable u v
  have heq : EqOn
      (fun t : ℝ => Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖)
      (fun t : ℝ => 2 * Real.log ‖(x : ℂ) + I * (t : ℂ) - 1‖ +
        Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖) (uIcc u v) := by
    intro t ht
    exact log_norm_regularizedTwoScale_eq (by simpa using vertical_ne_real hx0 t)
      (by simpa using vertical_ne_real hx1 t) (hne t ht)
  refine ⟨((hlinInt.const_mul 2).add hrawInt).congr (heq.symm.mono uIoc_subset_uIcc), ?_⟩
  rw [intervalIntegral.integral_congr heq,
    intervalIntegral.integral_add (hlinInt.const_mul 2) hrawInt,
    intervalIntegral.integral_const_mul]

/-- Cancellation is applied before estimating the two vertical edges.
This prevents the elementary regularizer from creating a spurious
height-times-log-height contribution. -/
theorem integral_regularizedTwoScale_verticalLogDifference_le
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {x u v : ℝ} (hxHalf : 1 / 2 < x) (hxOne : x < 1) (huv : u ≤ v)
    (hne : ∀ t ∈ Icc u v, twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) ≠ 0) :
    (∫ t in u..v, Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖) -
      (∫ t in u..v, Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (t : ℂ))‖) ≤
      (∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖) -
        (∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (t : ℂ))‖) := by
  have hl := integral_log_norm_regularizedTwoScale_eq (Y0 := Y0) (Y1 := Y1)
    (u := u) (v := v) (by linarith : x ≠ 0)
    (ne_of_lt hxOne) (by simpa only [uIcc_of_le huv] using hne)
  have hr := integral_log_norm_regularizedTwoScale_eq (Y0 := Y0) (Y1 := Y1)
    (u := u) (v := v) (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 1)
    (fun t _ => right_detector_ne hY0 hY01 t)
  simp only [Complex.ofReal_ofNat] at hr
  rw [hl.2, hr.2]
  linarith [integral_log_norm_subOne_left_le_fixedRight hxHalf hxOne huv]

/-- The bound is on the absolute value of the net integral, not on the
integral of the absolute logarithmic derivative. -/
theorem integral_regularizedTwoScale_rightArgument_bound
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (u v : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re)
      volume u v ∧
    |∫ t in u..v,
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re| ≤
      3 * Real.pi := by
  have hlinCont : Continuous (fun t : ℝ => (((4 : ℂ) + I * (t : ℂ) - 1)⁻¹).re) := by
    apply Complex.continuous_re.comp
    apply Continuous.inv₀ (by fun_prop)
    intro t hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
  have hlinInt : IntervalIntegrable (fun t : ℝ => (((4 : ℂ) + I * (t : ℂ) - 1)⁻¹).re)
      volume u v := hlinCont.intervalIntegrable u v
  have hrawInt := (integral_twoScaleCarlson_rightArgument_eq hY0 hY01 u v).1
  have heq : (fun t : ℝ =>
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re) =
      (fun t : ℝ => 2 * (((4 : ℂ) + I * (t : ℂ) - 1)⁻¹).re +
        (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re) := by
    funext t
    have hs0 : (4 : ℂ) + I * (t : ℂ) ≠ 0 := by
      simpa using vertical_ne_real (by norm_num : (4 : ℝ) ≠ 0) t
    have hs1 : (4 : ℂ) + I * (t : ℂ) ≠ 1 := by
      simpa using vertical_ne_real (by norm_num : (4 : ℝ) ≠ 1) t
    simpa using congrArg Complex.re (logDeriv_regularizedTwoScale_eq hs0 hs1
      (right_detector_ne hY0 hY01 t))
  rw [heq]
  refine ⟨(hlinInt.const_mul 2).add hrawInt, ?_⟩
  rw [intervalIntegral.integral_add (hlinInt.const_mul 2) hrawInt,
    intervalIntegral.integral_const_mul]
  have hlinear : |∫ t in u..v, (((4 : ℂ) + I * (t : ℂ) - 1)⁻¹).re| ≤ Real.pi := by
    simpa only [subOneFixedRightArgumentVariation, mul_comm I] using
      abs_subOneFixedRightArgumentVariation_le_pi u v
  have hraw := abs_integral_twoScaleCarlson_rightArgument_le_pi hY0 hY01 u v
  have htriangle := abs_add_le
    (2 * ∫ t in u..v, (((4 : ℂ) + I * (t : ℂ) - 1)⁻¹).re)
    (∫ t in u..v, (logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re)
  rw [abs_mul] at htriangle
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htriangle
  linarith

end PrimeNumberTheorem.CarlsonZeroDensity
