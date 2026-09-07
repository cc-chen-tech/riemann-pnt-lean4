import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Data.Complex.BigOperators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Complex MeasureTheory Set
open scoped BigOperators Interval

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
      simpa using ((hasDerivAt_id sigma).sub_const u.re).div_const d
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

/-- The real integral of a pole on a vertical line is an arctangent difference.
The vertical line does not contain the pole; the endpoints can have either order. -/
theorem intervalIntegral_re_inv_vertical_sub_eq
    {a b x : ℝ} {u : ℂ} (hx : x ≠ u.re) :
    (∫ t in a..b, ((((x : ℂ) + I * t) - u)⁻¹).re) =
      Real.arctan ((b - u.im) / (x - u.re)) -
        Real.arctan ((a - u.im) / (x - u.re)) := by
  let d : ℝ := x - u.re
  have hd : d ≠ 0 := sub_ne_zero.mpr hx
  let F : ℝ → ℝ := fun t => Real.arctan ((t - u.im) / d)
  have hpoint : ∀ t : ℝ,
      ((((x : ℂ) + I * t) - u)⁻¹).re =
        d / (d ^ 2 + (t - u.im) ^ 2) := by
    intro t
    rw [Complex.inv_re]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, I_re, I_im, zero_mul, mul_zero,
      one_mul, zero_add, add_zero, sub_zero]
    simp only [d, pow_two]
  have hderiv : deriv F = fun t : ℝ => d / (d ^ 2 + (t - u.im) ^ 2) := by
    funext t
    have hinner : HasDerivAt (fun y : ℝ => (y - u.im) / d) (1 / d) t := by
      simpa using ((hasDerivAt_id t).sub_const u.im).div_const d
    have hcomp := (Real.hasDerivAt_arctan ((t - u.im) / d)).comp t hinner
    change deriv F t = d / (d ^ 2 + (t - u.im) ^ 2)
    rw [show deriv F t = 1 / (1 + ((t - u.im) / d) ^ 2) * (1 / d) by
      exact hcomp.deriv]
    field_simp [hd]
  have hdiff : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ F t := by
    intro t _ht
    exact ((Real.hasDerivAt_arctan ((t - u.im) / d)).comp t
      (((hasDerivAt_id t).sub_const u.im).div_const d)).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => d / (d ^ 2 + (t - u.im) ^ 2))
      (Set.uIcc a b) := by
    have hden : ∀ t : ℝ, d ^ 2 + (t - u.im) ^ 2 ≠ 0 := by
      intro t
      exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd)
        (sq_nonneg (t - u.im)))
    exact (continuous_const.div₀
      ((continuous_const.pow 2).add ((continuous_id.sub continuous_const).pow 2))
      hden).continuousOn
  rw [show (fun t : ℝ => ((((x : ℂ) + I * t) - u)⁻¹).re) =
      fun t => d / (d ^ 2 + (t - u.im) ^ 2) by funext t; exact hpoint t]
  simpa [F, d] using intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont

/-- A strictly interior left-boundary pole contributes exactly `pi` on the
positively oriented bottom, right and top edges. There is no left-edge integral
in this identity: its complex pole kernel would not be integrable there. -/
theorem threeEdgeArgument_left_boundary_root_eq_pi
    {x0 x1 U T tau : ℝ} (hx : x0 < x1) (hU : U < tau) (hT : tau < T) :
    (∫ x in x0..x1,
      ((((x : ℂ) + I * U) - ((x0 : ℂ) + I * tau))⁻¹).im) +
    (∫ t in U..T,
      ((((x1 : ℂ) + I * t) - ((x0 : ℂ) + I * tau))⁻¹).re) -
    (∫ x in x0..x1,
      ((((x : ℂ) + I * T) - ((x0 : ℂ) + I * tau))⁻¹).im) = Real.pi := by
  rw [intervalIntegral_im_inv_horizontal_sub_eq (by simpa using ne_of_lt hU),
    intervalIntegral_re_inv_vertical_sub_eq (by simpa using ne_of_gt hx),
    intervalIntegral_im_inv_horizontal_sub_eq (by simpa using ne_of_gt hT)]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, I_re, I_im, zero_mul, mul_zero, one_mul,
    zero_add, add_zero, sub_self, zero_div, Real.arctan_zero]
  have hneg : U - tau = -(tau - U) := by ring
  simp only [hneg, div_neg, neg_div, Real.arctan_neg, neg_neg]
  have hbottom := Real.arctan_inv_of_pos
    (div_pos (sub_pos.mpr hx) (sub_pos.mpr hU))
  have htop := Real.arctan_inv_of_pos
    (div_pos (sub_pos.mpr hx) (sub_pos.mpr hT))
  simp only [inv_div] at hbottom htop
  linarith

/-- The complete finite left-boundary principal part contributes `pi` times its
multiplicity mass on the three nonsingular edges. Integrability and interchange
of the finite sum with each real integral are proved, not supplied as inputs. -/
theorem threeEdgeArgument_left_principalParts_eq_pi_mul_sum
    {x0 x1 U T : ℝ} (left : Finset ℂ) (m : ℂ → ℕ)
    (hx : x0 < x1)
    (hleft : ∀ p ∈ left, p.re = x0 ∧ U < p.im ∧ p.im < T) :
    (∫ x in x0..x1,
      (∑ p ∈ left, (((x : ℂ) + I * U) - p)⁻¹ * (m p : ℂ)).im) +
    (∫ t in U..T,
      (∑ p ∈ left, (((x1 : ℂ) + I * t) - p)⁻¹ * (m p : ℂ)).re) -
    (∫ x in x0..x1,
      (∑ p ∈ left, (((x : ℂ) + I * T) - p)⁻¹ * (m p : ℂ)).im) =
      Real.pi * ∑ p ∈ left, (m p : ℝ) := by
  have hhor : ∀ p ∈ left, ∀ y : ℝ, y ≠ p.im →
      Continuous (fun x : ℝ => (((x : ℂ) + I * y) - p)⁻¹ * (m p : ℂ)) := by
    intro p _hp y hy
    apply (((Complex.continuous_ofReal.add continuous_const).sub
      continuous_const).inv₀ ?_).mul continuous_const
    intro x hz
    apply hy
    have him := congrArg Complex.im hz
    exact sub_eq_zero.mp (by simpa using him)
  have hver : ∀ p ∈ left,
      Continuous (fun t : ℝ => (((x1 : ℂ) + I * t) - p)⁻¹ * (m p : ℂ)) := by
    intro p hp
    apply (((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).sub
      continuous_const).inv₀ ?_).mul continuous_const
    intro t hz
    have hre := congrArg Complex.re hz
    simp [(hleft p hp).1] at hre
    linarith
  have hb : ∀ p ∈ left, IntervalIntegrable
      (fun x : ℝ => ((((x : ℂ) + I * U) - p)⁻¹ * (m p : ℂ)).im)
      volume x0 x1 := by
    intro p hp
    exact (Complex.continuous_im.comp
      (hhor p hp U (ne_of_lt (hleft p hp).2.1))).intervalIntegrable _ _
  have ht : ∀ p ∈ left, IntervalIntegrable
      (fun x : ℝ => ((((x : ℂ) + I * T) - p)⁻¹ * (m p : ℂ)).im)
      volume x0 x1 := by
    intro p hp
    exact (Complex.continuous_im.comp
      (hhor p hp T (ne_of_gt (hleft p hp).2.2))).intervalIntegrable _ _
  have hr : ∀ p ∈ left, IntervalIntegrable
      (fun t : ℝ => ((((x1 : ℂ) + I * t) - p)⁻¹ * (m p : ℂ)).re)
      volume U T := by
    intro p hp
    exact (Complex.continuous_re.comp (hver p hp)).intervalIntegrable _ _
  simp only [Complex.im_sum, Complex.re_sum]
  rw [intervalIntegral.integral_finsetSum hb,
    intervalIntegral.integral_finsetSum hr,
    intervalIntegral.integral_finsetSum ht,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpeq : (x0 : ℂ) + I * p.im = p := by
    apply Complex.ext <;> simp [(hleft p hp).1]
  have hsingle := threeEdgeArgument_left_boundary_root_eq_pi
    hx (hleft p hp).2.1 (hleft p hp).2.2
  rw [hpeq] at hsingle
  simp only [Complex.mul_im, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_add, sub_zero]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const]
  calc
    _ = ((∫ x in x0..x1, ((((x : ℂ) + I * U) - p)⁻¹).im) +
        (∫ t in U..T, ((((x1 : ℂ) + I * t) - p)⁻¹).re) -
        (∫ x in x0..x1, ((((x : ℂ) + I * T) - p)⁻¹).im)) * (m p : ℝ) := by ring
    _ = Real.pi * (m p : ℝ) := congrArg (fun r : ℝ => r * (m p : ℝ)) hsingle

end MathlibAux
