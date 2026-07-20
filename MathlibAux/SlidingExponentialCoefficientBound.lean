import MathlibAux.SlidingExponentialPolynomialMeanSquare

/-!
# Bounds for sliding exponential coefficients

The Fourier transform of an interval has both a trivial length bound and an
oscillatory reciprocal-frequency bound.  This file records those estimates
for `slidingExponentialCoefficient`, including arbitrary signed interval
lengths.
-/

open Complex MeasureTheory Set

namespace MathlibAux

/-- Exact evaluation of a nonconstant exponential mode over a signed interval. -/
theorem intervalIntegral_cexp_linear_eq {H lambda : ℝ} (hlambda : lambda ≠ 0) :
    (∫ u in (0 : ℝ)..H, Complex.exp (I * (lambda * u))) =
      (Complex.exp (I * (lambda * H)) - 1) / (I * (lambda : ℂ)) := by
  have hc : I * (lambda : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hlambda)
  convert integral_exp_mul_complex (a := (0 : ℝ)) (b := H) hc using 1 <;>
    push_cast <;> ring_nf
  simp

/-- The norm of an interval exponential integral is at most the absolute
length of the interval, with no sign assumption on `H`. -/
theorem norm_intervalIntegral_cexp_linear_le_abs_length (H lambda : ℝ) :
    ‖∫ u in (0 : ℝ)..H, Complex.exp (I * (lambda * u))‖ ≤ |H| := by
  calc
    ‖∫ u in (0 : ℝ)..H, Complex.exp (I * (lambda * u))‖ ≤
        1 * |H - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u _hu
      rw [show I * (lambda * u) = I * ((lambda * u : ℝ) : ℂ) by norm_num]
      exact le_of_eq (Complex.norm_exp_I_mul_ofReal (lambda * u))
    _ = |H| := by simp

/-- A nonzero exponential mode has the reciprocal-frequency bound, for an
interval of arbitrary signed length. -/
theorem norm_intervalIntegral_cexp_linear_le_two_div_abs {H lambda : ℝ}
    (hlambda : lambda ≠ 0) :
    ‖∫ u in (0 : ℝ)..H, Complex.exp (I * (lambda * u))‖ ≤
      2 / |lambda| := by
  exact norm_integral_cexp_linear_le hlambda

/-- Combining the length and oscillatory estimates gives the sharp reusable
envelope needed for sliding exponential-polynomial coefficients. -/
theorem norm_intervalIntegral_cexp_linear_le_abs_length_min {H lambda : ℝ}
    (hlambda : lambda ≠ 0) :
    ‖∫ u in (0 : ℝ)..H, Complex.exp (I * (lambda * u))‖ ≤
      min |H| (2 / |lambda|) := by
  exact le_min (norm_intervalIntegral_cexp_linear_le_abs_length H lambda)
    (norm_intervalIntegral_cexp_linear_le_two_div_abs hlambda)

/-- The sliding coefficient is bounded by the original coefficient times the
absolute interval length. -/
theorem norm_slidingExponentialCoefficient_le_abs_length
    {iota : Type*} (H : ℝ) (coeff : iota → ℂ) (freq : iota → ℝ) (j : iota) :
    ‖slidingExponentialCoefficient H coeff freq j‖ ≤
      ‖coeff j‖ * |H| := by
  rw [slidingExponentialCoefficient, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_intervalIntegral_cexp_linear_le_abs_length H (freq j)) (norm_nonneg _)

/-- At nonzero frequency, the sliding coefficient is bounded by the original
coefficient times the reciprocal-frequency envelope. -/
theorem norm_slidingExponentialCoefficient_le_two_div_abs
    {iota : Type*} {H : ℝ} (coeff : iota → ℂ) (freq : iota → ℝ) (j : iota)
    (hfreq : freq j ≠ 0) :
    ‖slidingExponentialCoefficient H coeff freq j‖ ≤
      ‖coeff j‖ * (2 / |freq j|) := by
  rw [slidingExponentialCoefficient, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_intervalIntegral_cexp_linear_le_two_div_abs hfreq) (norm_nonneg _)

/-- The combined minimum envelope for a sliding exponential coefficient. -/
theorem norm_slidingExponentialCoefficient_le_min
    {iota : Type*} {H : ℝ} (coeff : iota → ℂ) (freq : iota → ℝ) (j : iota)
    (hfreq : freq j ≠ 0) :
    ‖slidingExponentialCoefficient H coeff freq j‖ ≤
      ‖coeff j‖ * min |H| (2 / |freq j|) := by
  rw [slidingExponentialCoefficient, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_intervalIntegral_cexp_linear_le_abs_length_min hfreq) (norm_nonneg _)

end MathlibAux
