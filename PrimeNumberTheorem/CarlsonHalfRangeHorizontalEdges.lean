import PrimeNumberTheorem.CarlsonTwoScaleHorizontalBudget
import PrimeNumberTheorem.CarlsonHalfRangeAuxiliaryWindow

/-! Actual horizontal edges for the half-range shell.  Both good heights
are chosen before the auxiliary left line and include all needed
integrability and nonvanishing assertions. -/

open Complex Filter MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

theorem integral_twoScale_horizontal_weighted_bound
    {Y0 Y1 : ℕ} {x t M : ℝ} (hx0 : 0 < x) (hx4 : x ≤ 4) (hM : 0 ≤ M)
    (hne : ∀ w ∈ Icc x 4,
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((w : ℂ) + (t : ℂ) * I) ≠ 0)
    (hbound : ∀ w ∈ Icc x 4,
      ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((w : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    IntervalIntegrable (fun w : ℝ => (w - x) *
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((w : ℂ) + (t : ℂ) * I)).im)
      volume x 4 ∧
    |∫ w in x..4, (w - x) *
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((w : ℂ) + (t : ℂ) * I)).im| ≤
      (4 - x) ^ 2 * M := by
  let H := regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  have hInt : IntervalIntegrable (fun w : ℝ =>
      (w - x) * (logDeriv H ((w : ℂ) + (t : ℂ) * I)).im) volume x 4 := by
    apply ContinuousOn.intervalIntegrable
    intro w hw
    have hw' : w ∈ Icc x 4 := by simpa only [uIcc_of_le hx4] using hw
    have hA : AnalyticAt ℂ H ((w : ℂ) + (t : ℂ) * I) :=
      analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_re_gt
        (theta := (0 : ℝ)) le_rfl Y0 Y1 _ (by simpa using hx0.trans_le hw'.1)
    have hLog := ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero hA (hne w hw')
    have hmap : ContinuousAt (fun z : ℝ => (z : ℂ) + (t : ℂ) * I) w := by fun_prop
    have hcomp : ContinuousAt (fun z : ℝ => logDeriv H ((z : ℂ) + (t : ℂ) * I)) w := by
      simpa only [Function.comp_def] using hLog.continuousAt.comp
        (f := fun z : ℝ => (z : ℂ) + (t : ℂ) * I) hmap
    have hweight : ContinuousAt (fun z : ℝ => z - x) w := by fun_prop
    exact (hweight.mul (Complex.continuous_im.continuousAt.comp hcomp)).continuousWithinAt
  refine ⟨hInt, ?_⟩
  have hpoint (w : ℝ) (hw : w ∈ uIoc x 4) :
      ‖(w - x) * (logDeriv H ((w : ℂ) + (t : ℂ) * I)).im‖ ≤ (4 - x) * M := by
    rw [uIoc_of_le hx4] at hw
    have hnonneg : 0 ≤ w - x := by linarith [hw.1]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
    calc
      _ ≤ (w - x) * ‖logDeriv H ((w : ℂ) + (t : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) hnonneg
      _ ≤ (w - x) * M := mul_le_mul_of_nonneg_left (hbound w ⟨hw.1.le, hw.2⟩) hnonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [hw.2]) hM
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hi' : |∫ w in x..4, (w - x) * (logDeriv H ((w : ℂ) + (t : ℂ) * I)).im| ≤
      ((4 - x) * M) * (4 - x) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx4)] using hi
  calc
    _ ≤ ((4 - x) * M) * (4 - x) := hi'
    _ = _ := by ring

/-- Both chosen heights cover the closed target shell and lie inside the
Gaussian height interval.  They work simultaneously for every auxiliary
left line in the fixed window. -/
theorem exists_eventually_halfRange_horizontalEdges :
    ∃ K > (0 : ℝ), ∀ᶠ U : ℝ in atTop,
      let V := 10 * U / 21
      let H := regularizedTwoScaleCarlsonZeroDetector (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
      ∃ u ∈ Icc (U - 1) U, ∃ v ∈ Icc (9 * U / 8) (9 * U / 8 + 1),
        2 * V ≤ u ∧ v ≤ 5 * V / 2 ∧ u ≤ v ∧
        (∀ w ∈ Icc halfRangeAuxiliaryLeft 4, H ((w : ℂ) + (u : ℂ) * I) ≠ 0) ∧
        (∀ w ∈ Icc halfRangeAuxiliaryLeft 4, H ((w : ℂ) + (v : ℂ) * I) ≠ 0) ∧
        ∀ x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
          IntervalIntegrable (fun w : ℝ => (w - x) * (logDeriv H ((w : ℂ) + (u : ℂ) * I)).im)
            volume x 4 ∧
          IntervalIntegrable (fun w : ℝ => (w - x) * (logDeriv H ((w : ℂ) + (v : ℂ) * I)).im)
            volume x 4 ∧
          |∫ w in x..4, (w - x) * (logDeriv H ((w : ℂ) + (u : ℂ) * I)).im| +
            |∫ w in x..4, (w - x) * (logDeriv H ((w : ℂ) + (v : ℂ) * I)).im| ≤
            K * (1 + Real.log U) ^ 2 := by
  obtain ⟨K, hK, hhorizontal⟩ := exists_eventually_twoScale_horizontal_logDeriv_le_logSquare
  have hscale : Tendsto (fun U : ℝ => 10 * U / 21) atTop atTop := by
    have heq : (fun U : ℝ => 10 * U / 21) = (fun U : ℝ => (10 / 21 : ℝ) * U) := by
      funext U
      ring
    rw [heq]
    exact tendsto_id.const_mul_atTop (by norm_num)
  refine ⟨32 * K, by positivity, ?_⟩
  filter_upwards [hhorizontal, hscale.eventually eventually_halfRangeCutoff_conditions,
    eventually_ge_atTop (21 : ℝ)] with U hhorizontal hparams hU
  let V := 10 * U / 21
  let Y0 := halfRangeCoreCutoff V
  let Y1 := halfRangeOuterCutoff V
  let H := regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  obtain ⟨hV, hY0, hY01, _, hY1upper, _⟩ := hparams
  have hY1U : (Y1 : ℝ) ≤ U := by
    calc
      _ ≤ V ^ (9 / 20 : ℝ) := hY1upper
      _ ≤ V ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hV.le (by norm_num)
      _ = V := Real.rpow_one _
      _ ≤ U := by dsimp [V]; linarith
  obtain ⟨u, hu, hbottom, hbottomBound⟩ := hhorizontal hY0 hY01 hY1U
    (sigma := halfRangeAuxiliaryLeft) (S := U - 1)
    (by norm_num [halfRangeAuxiliaryLeft]) (by linarith) (by linarith)
  obtain ⟨v, hv, htop, htopBound⟩ := hhorizontal hY0 hY01 hY1U
    (sigma := halfRangeAuxiliaryLeft) (S := 9 * U / 8)
    (by norm_num [halfRangeAuxiliaryLeft]) (by linarith) (by linarith)
  have hu' : u ∈ Icc (U - 1) U := by simpa using hu
  refine ⟨u, hu', v, hv, ?_, ?_, ?_, hbottom, htop, ?_⟩
  · linarith [hu'.1]
  · linarith [hv.2]
  · linarith [hu'.2, hv.1]
  intro x hx
  obtain ⟨hxStrip, _, _⟩ := halfRangeAuxiliary_bounds hx
  have hx0 : 0 < x := by linarith [hxStrip.1]
  have hx4 : x ≤ 4 := by linarith [hxStrip.2]
  have hsub : Icc x 4 ⊆ Icc halfRangeAuxiliaryLeft 4 :=
    fun _ hw => ⟨hx.1.trans hw.1, hw.2⟩
  let M := K * (1 + Real.log U) ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb := integral_twoScale_horizontal_weighted_bound hx0 hx4 hM
    (fun w hw => hbottom w (hsub hw)) (fun w hw => hbottomBound w (hsub hw))
  have ht := integral_twoScale_horizontal_weighted_bound hx0 hx4 hM
    (fun w hw => htop w (hsub hw)) (fun w hw => htopBound w (hsub hw))
  refine ⟨hb.1, ht.1, ?_⟩
  have hw : (4 - x) ^ 2 ≤ 16 := by nlinarith
  have hwm := mul_le_mul_of_nonneg_right hw hM
  dsimp [M] at hwm hb ht
  nlinarith [hb.2, ht.2]

end PrimeNumberTheorem.CarlsonZeroDensity
