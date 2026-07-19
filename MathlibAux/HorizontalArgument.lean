import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Complex MeasureTheory Set
open scoped Interval

namespace MathlibAux

/-- The imaginary integral of one horizontal logarithmic-derivative pole is
the difference of two arctangent values. -/
theorem intervalIntegral_im_inv_horizontal_sub_eq
    {a b t : ℝ} {u : ℂ} (ht : t ≠ u.im) :
    (∫ sigma in a..b,
      (((((sigma : ℂ) + I * t) - u)⁻¹).im)) =
      -Real.arctan ((b - u.re) / (t - u.im)) +
        Real.arctan ((a - u.re) / (t - u.im)) := by
  let d : ℝ := t - u.im
  have hd : d ≠ 0 := sub_ne_zero.mpr ht
  let F : ℝ → ℝ := fun sigma =>
    -Real.arctan ((sigma - u.re) / d)
  have hpoint : ∀ sigma : ℝ,
      (((((sigma : ℂ) + I * t) - u)⁻¹).im) =
        -d / ((sigma - u.re) ^ 2 + d ^ 2) := by
    intro sigma
    rw [Complex.inv_im]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, I_re, I_im, zero_mul, one_mul, zero_add,
      Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, mul_zero, zero_sub]
    dsimp [d]
    ring
  have hderiv : deriv F = fun sigma : ℝ =>
      -d / ((sigma - u.re) ^ 2 + d ^ 2) := by
    funext sigma
    have hinner : HasDerivAt
        (fun x : ℝ => (x - u.re) / d) (1 / d) sigma := by
      convert ((hasDerivAt_id sigma).sub_const u.re).div_const d using 1
    have hcomp := (Real.hasDerivAt_arctan ((sigma - u.re) / d)).comp sigma hinner
    change deriv F sigma = -d / ((sigma - u.re) ^ 2 + d ^ 2)
    rw [show deriv F sigma =
        -(1 / (1 + ((sigma - u.re) / d) ^ 2) * (1 / d)) by
      exact hcomp.neg.deriv]
    field_simp [hd]
    ring
  have hdiff : ∀ sigma ∈ Set.uIcc a b,
      DifferentiableAt ℝ F sigma := by
    intro sigma _hsigma
    exact ((Real.hasDerivAt_arctan ((sigma - u.re) / d)).comp sigma
      (((hasDerivAt_id sigma).sub_const u.re).div_const d)).neg.differentiableAt
  have hcont : ContinuousOn
      (fun sigma : ℝ => -d / ((sigma - u.re) ^ 2 + d ^ 2))
      (Set.uIcc a b) := by
    have hden : ∀ sigma : ℝ,
        (sigma - u.re) ^ 2 + d ^ 2 ≠ 0 := by
      intro sigma
      exact ne_of_gt (add_pos_of_nonneg_of_pos
        (sq_nonneg (sigma - u.re)) (sq_pos_of_ne_zero hd))
    exact (continuous_const.neg.div₀
      (((continuous_id.sub continuous_const).pow 2).add
        (continuous_const.pow 2)) hden).continuousOn
  rw [show (fun sigma : ℝ =>
      (((((sigma : ℂ) + I * t) - u)⁻¹).im)) =
        fun sigma => -d / ((sigma - u.re) ^ 2 + d ^ 2) by
      funext sigma
      exact hpoint sigma]
  simpa [F, d] using
    intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont

/-- A single zero or pole contributes at most `pi` to horizontal argument
variation, independently of its distance from the horizontal line. -/
theorem abs_intervalIntegral_im_inv_horizontal_sub_le_pi
    {a b t : ℝ} {u : ℂ} (ht : t ≠ u.im) :
    |∫ sigma in a..b,
      (((((sigma : ℂ) + I * t) - u)⁻¹).im)| ≤ Real.pi := by
  rw [intervalIntegral_im_inv_horizontal_sub_eq ht]
  have ha_lo := Real.neg_pi_div_two_lt_arctan
    ((a - u.re) / (t - u.im))
  have ha_hi := Real.arctan_lt_pi_div_two
    ((a - u.re) / (t - u.im))
  have hb_lo := Real.neg_pi_div_two_lt_arctan
    ((b - u.re) / (t - u.im))
  have hb_hi := Real.arctan_lt_pi_div_two
    ((b - u.re) / (t - u.im))
  rw [abs_le]
  constructor <;> linarith

end MathlibAux
