import MathlibAux.PaleyZygmund
import MathlibAux.SlidingIntegralFourierCompatibility

open Complex Convolution MeasureTheory Set
open scoped Convolution Interval

namespace MathlibAux

/-! # Absolute sliding-window L2 bound -/

private theorem integral_backwardRectangularKernel_eq
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ x : ℝ, backwardRectangularKernel H x) = (H : ℂ) := by
  change (∫ x : ℝ, (Ico (-H) 0).indicator (fun _ => (1 : ℂ)) x) = _
  rw [integral_indicator measurableSet_Ico]
  simp [MeasureTheory.integral_const, hH]

private theorem integrable_real_slidingIntegral
    {q : ℝ → ℝ} (hq : Integrable q) {H : ℝ} (hH : 0 ≤ H) :
    Integrable (fun t => ∫ u in t..t + H, q u) := by
  have hc : Integrable (fun t => ∫ u in t..t + H, (q u : ℂ)) :=
    integrable_slidingIntegral hq.ofReal hH
  refine hc.re.congr (Filter.Eventually.of_forall fun t => ?_)
  have ht := intervalIntegral.integral_ofReal
    (a := t) (b := t + H) (f := q) (μ := volume)
  simpa using congrArg Complex.re ht

private theorem integral_real_slidingIntegral_eq
    {q : ℝ → ℝ} (hq : Integrable q) {H : ℝ} (hH : 0 ≤ H) :
    (∫ t : ℝ, ∫ u in t..t + H, q u) = H * ∫ u : ℝ, q u := by
  let qC : ℝ → ℂ := fun t => (q t : ℂ)
  have hqC : Integrable qC := hq.ofReal
  have hconv := integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    hqC (integrable_backwardRectangularKernel H)
  have hpoint : ∀ t : ℝ,
      (qC ⋆[ContinuousLinearMap.mul ℂ ℂ] backwardRectangularKernel H) t =
        ∫ u in t..t + H, (q u : ℂ) :=
    convolution_backwardRectangularKernel_eq_slidingIntegral hH
  have hcomplex :
      (∫ t : ℝ, ∫ u in t..t + H, (q u : ℂ)) =
        (H : ℂ) * ∫ u : ℝ, (q u : ℂ) := by
    calc
      (∫ t : ℝ, ∫ u in t..t + H, (q u : ℂ)) =
          ∫ t : ℝ,
            (qC ⋆[ContinuousLinearMap.mul ℂ ℂ]
              backwardRectangularKernel H) t := by
        apply integral_congr_ae
        filter_upwards with t
        exact (hpoint t).symm
      _ = (∫ u : ℝ, qC u) *
          ∫ x : ℝ, backwardRectangularKernel H x := by
        simpa only [ContinuousLinearMap.mul_apply'] using hconv
      _ = (H : ℂ) * ∫ u : ℝ, (q u : ℂ) := by
        rw [integral_backwardRectangularKernel_eq hH]
        dsimp only [qC]
        ring
  have hc : Integrable (fun t => ∫ u in t..t + H, (q u : ℂ)) :=
    integrable_slidingIntegral hq.ofReal hH
  calc
    (∫ t : ℝ, ∫ u in t..t + H, q u) =
        ∫ t : ℝ, Complex.re (∫ u in t..t + H, (q u : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with t
      have ht := intervalIntegral.integral_ofReal
        (a := t) (b := t + H) (f := q) (μ := volume)
      simpa using (congrArg Complex.re ht).symm
    _ = Complex.re (∫ t : ℝ, ∫ u in t..t + H, (q u : ℂ)) :=
      integral_re hc
    _ = Complex.re ((H : ℂ) * ∫ u : ℝ, (q u : ℂ)) := by
      rw [hcomplex]
    _ = H * ∫ u : ℝ, q u := by
      rw [integral_complex_ofReal]
      simp

/-- The square of the global absolute sliding-window mass is bounded by the
window length squared times the global `L²` mass. -/
theorem integral_sq_abs_slidingWindow_le
    {F : ℝ → ℂ} (hF : MemLp F 2) {H : ℝ} (hH : 0 ≤ H) :
    (∫ t : ℝ, (∫ u in t..t + H, ‖F u‖) ^ 2) ≤
      H ^ 2 * ∫ u : ℝ, ‖F u‖ ^ 2 := by
  let q : ℝ → ℝ := fun u => ‖F u‖ ^ 2
  let S : ℝ → ℝ := fun t => ∫ u in t..t + H, ‖F u‖
  let Q : ℝ → ℝ := fun t => ∫ u in t..t + H, q u
  have hq : Integrable q := by
    exact (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  have hQ : Integrable Q := integrable_real_slidingIntegral hq hH
  have hpoint : ∀ t : ℝ, S t ^ 2 ≤ H * Q t := by
    intro t
    have hcs :=
      sq_setIntegral_le_measureReal_mul_setIntegral_sq_of_aestronglyMeasurable
        (s := Ioc t (t + H)) (f := fun u => ‖F u‖)
        (measure_Ioc_lt_top.ne)
        (hF.1.norm.mono_measure Measure.restrict_le_self) hq.integrableOn
    simpa only [S, Q, q,
      intervalIntegral.integral_of_le (le_add_of_nonneg_right hH),
      Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hH,
      add_sub_cancel_left] using hcs
  calc
    (∫ t : ℝ, S t ^ 2) ≤ ∫ t : ℝ, H * Q t := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun t => sq_nonneg (S t)
      · exact hQ.const_mul H
      · exact Filter.Eventually.of_forall hpoint
    _ = H * ∫ t : ℝ, Q t := integral_const_mul H Q
    _ = H * (H * ∫ u : ℝ, q u) := by
      rw [integral_real_slidingIntegral_eq hq hH]
    _ = H ^ 2 * ∫ u : ℝ, ‖F u‖ ^ 2 := by
      dsimp only [q]
      ring

end MathlibAux
