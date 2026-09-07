import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The quadratic cancellation in Conrey's arithmetic Euler factor

The literal two-shift Euler factor has deviation bounded by
`16 * ‖a‖ * ‖b‖ * log(p)^2 * exp (-(7/4) * log p)` for `p ≥ 2`
and shifts of norm at most `1/8`. In particular either zero shift
annihilates the deviation. All denominators are bounded away from zero.

This is a local arithmetic estimate, not the long mollified mean-value
theorem or the full arithmetic sum asymptotic. See the paper-first audit
`docs/research/2026-08-30-conrey-arithmetic-main-term-proof.md`.
-/

namespace HardyTheorem

noncomputable def conreyArithmeticPrimeWeight (p : ℝ) (a b : ℂ) : ℂ :=
  (1 - (p : ℂ)⁻¹ * Complex.exp (-(a + b) * (Real.log p : ℂ))) /
    ((1 - (p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))) *
     (1 - (p : ℂ)⁻¹ * Complex.exp (-b * (Real.log p : ℂ))))

noncomputable def conreyArithmeticEulerFactor (p : ℝ) (a b : ℂ) : ℂ :=
  (1 - (p : ℂ)⁻¹) * (1 + (p : ℂ)⁻¹ * conreyArithmeticPrimeWeight p a b)

private theorem norm_conreyPrimePower_le {p : ℝ} {a : ℂ}
    (hp : 2 ≤ p) (ha : ‖a‖ ≤ 1 / 8) :
    ‖(p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))‖ ≤ 3 / 4 := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hre : -(1 / 8 : ℝ) ≤ a.re := by
    have := (abs_le.mp (Complex.abs_re_le_norm a)).1
    linarith
  have hn : ‖(p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))‖ =
      Real.exp (-(1 + a.re) * Real.log p) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0,
      Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
    have hei : p⁻¹ = Real.exp (-Real.log p) := by
      rw [Real.exp_neg, Real.exp_log hp0]
    rw [hei, ← Real.exp_add]
    congr 1
    ring
  rw [hn]
  have hs : Real.exp (-(1 + a.re) * Real.log p) ^ 2 ≤ (1 / 2 : ℝ) := by
    calc
      _ = Real.exp (2 * (-(1 + a.re) * Real.log p)) := by
        simpa only [Nat.cast_ofNat] using
          (Real.exp_nat_mul (-(1 + a.re) * Real.log p) 2).symm
      _ ≤ Real.exp (-Real.log p) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + 2 * a.re) hl]
      _ = p⁻¹ := by rw [Real.exp_neg, Real.exp_log hp0]
      _ ≤ 1 / 2 := by
        simpa using (inv_le_inv₀ hp0 (by norm_num : (0 : ℝ) < 2)).mpr hp
  nlinarith [Real.exp_pos (-(1 + a.re) * Real.log p)]

/-- The shifted Euler denominator never vanishes on the closed shift ball. -/
theorem conreyArithmeticDenominator_norm_ge {p : ℝ} {a : ℂ}
    (hp : 2 ≤ p) (ha : ‖a‖ ≤ 1 / 8) :
    (1 / 4 : ℝ) ≤ ‖1 - (p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))‖ := by
  have h := norm_sub_norm_le (1 : ℂ)
    ((p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ)))
  have := norm_conreyPrimePower_le hp ha
  simp only [norm_one] at h
  linarith

/-- Exact two-shift cancellation, with nonzero denominators proved from
the numerical hypotheses, not assumed as an extra analytic input. -/
theorem conreyArithmeticEulerFactor_sub_one {p : ℝ} {a b : ℂ}
    (hp : 2 ≤ p) (ha : ‖a‖ ≤ 1 / 8) (hb : ‖b‖ ≤ 1 / 8) :
    conreyArithmeticEulerFactor p a b - 1 =
      -((p : ℂ)⁻¹ ^ 2) * (1 - Complex.exp (-a * (Real.log p : ℂ))) *
        (1 - Complex.exp (-b * (Real.log p : ℂ))) /
        ((1 - (p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))) *
         (1 - (p : ℂ)⁻¹ * Complex.exp (-b * (Real.log p : ℂ)))) := by
  have hda : 1 - (p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ)) ≠ 0 := by
    apply norm_pos_iff.mp
    have := conreyArithmeticDenominator_norm_ge hp ha
    linarith
  have hdb : 1 - (p : ℂ)⁻¹ * Complex.exp (-b * (Real.log p : ℂ)) ≠ 0 := by
    apply norm_pos_iff.mp
    have := conreyArithmeticDenominator_norm_ge hp hb
    linarith
  have he : Complex.exp (-(a + b) * (Real.log p : ℂ)) =
      Complex.exp (-a * (Real.log p : ℂ)) *
        Complex.exp (-b * (Real.log p : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold conreyArithmeticEulerFactor conreyArithmeticPrimeWeight
  rw [he]
  have halg (q x y : ℂ) (hx : 1 - q * x ≠ 0) (hy : 1 - q * y ≠ 0) :
      (1 - q) * (1 + q * ((1 - q * (x * y)) / ((1 - q * x) * (1 - q * y)))) - 1 =
        -(q ^ 2) * (1 - x) * (1 - y) / ((1 - q * x) * (1 - q * y)) := by
    field_simp
    ring
  exact halg _ _ _ hda hdb

private theorem norm_one_sub_exp_shift_le {p : ℝ} (hp : 2 ≤ p) (a : ℂ) :
    ‖1 - Complex.exp (-a * (Real.log p : ℂ))‖ ≤
      ‖a‖ * Real.log p * Real.exp (‖a‖ * Real.log p) := by
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp
    (-a * (Real.log p : ℂ)) 1
  simpa [norm_sub_rev, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hl] using h

private theorem conreyPrimePower_scalar_le {p : ℝ} {a b : ℂ}
    (hp : 2 ≤ p) (ha : ‖a‖ ≤ 1 / 8) (hb : ‖b‖ ≤ 1 / 8) :
    (p⁻¹ : ℝ) ^ 2 * Real.exp (‖a‖ * Real.log p) *
      Real.exp (‖b‖ * Real.log p) ≤ Real.exp (-(7 / 4 : ℝ) * Real.log p) := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have he : p⁻¹ = Real.exp (-Real.log p) := by
    rw [Real.exp_neg, Real.exp_log hp0]
  rw [he, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := mul_nonneg (by linarith : 0 ≤ 1 / 4 - ‖a‖ - ‖b‖) hl
  norm_num at *
  nlinarith

/-- A uniform, summable-in-primes quadratic error for the actual Euler
factor. The result includes both zero-shift cases and uses no asymptotic
or mean-square hypothesis. -/
theorem norm_conreyArithmeticEulerFactor_sub_one_le {p : ℝ} {a b : ℂ}
    (hp : 2 ≤ p) (ha : ‖a‖ ≤ 1 / 8) (hb : ‖b‖ ≤ 1 / 8) :
    ‖conreyArithmeticEulerFactor p a b - 1‖ ≤
      16 * ‖a‖ * ‖b‖ * Real.log p ^ 2 * Real.exp (-(7 / 4 : ℝ) * Real.log p) := by
  have hp0 : 0 < p := by linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hd : (1 / 16 : ℝ) ≤
      ‖1 - (p : ℂ)⁻¹ * Complex.exp (-a * (Real.log p : ℂ))‖ *
        ‖1 - (p : ℂ)⁻¹ * Complex.exp (-b * (Real.log p : ℂ))‖ := by
    have h := mul_le_mul (conreyArithmeticDenominator_norm_ge hp ha)
      (conreyArithmeticDenominator_norm_ge hp hb) (by norm_num)
      (norm_nonneg _)
    norm_num at h
    simpa only [neg_mul] using h
  rw [conreyArithmeticEulerFactor_sub_one hp ha hb, norm_div, norm_mul,
    norm_mul, norm_neg, norm_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hp0, norm_mul]
  calc
    _ ≤ ((p⁻¹)^2 * (‖a‖ * Real.log p * Real.exp (‖a‖ * Real.log p)) *
      (‖b‖ * Real.log p * Real.exp (‖b‖ * Real.log p))) / (1 / 16 : ℝ) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) hd
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_one_sub_exp_shift_le hp a) (sq_nonneg p⁻¹))
        (norm_one_sub_exp_shift_le hp b) (norm_nonneg _) (by positivity)
    _ = (16 * ‖a‖ * ‖b‖ * Real.log p ^ 2) *
      ((p⁻¹)^2 * Real.exp (‖a‖ * Real.log p) * Real.exp (‖b‖ * Real.log p)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (conreyPrimePower_scalar_le hp ha hb)
      (by positivity)

end HardyTheorem
