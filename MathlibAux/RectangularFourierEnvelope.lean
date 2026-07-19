import MathlibAux.DirichletPolynomialMeanSquare

open Complex MeasureTheory Set

namespace MathlibAux

/-- A rectangular linear exponential window is bounded by its length,
including at zero frequency. -/
theorem norm_integral_cexp_linear_le_length {delta omega : ℝ}
    (hdelta : 0 ≤ delta) :
    ‖∫ v in (0 : ℝ)..delta, Complex.exp (I * (omega * v))‖ ≤ delta := by
  calc
    ‖∫ v in (0 : ℝ)..delta, Complex.exp (I * (omega * v))‖ ≤
        1 * |delta - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v _hv
      rw [show I * (omega * v) = I * ((omega * v : ℝ) : ℂ) by norm_num]
      exact le_of_eq (Complex.norm_exp_I_mul_ofReal (omega * v))
    _ = delta := by
      simp only [sub_zero, abs_of_nonneg hdelta, one_mul]

/-- A rectangular linear exponential window is bounded both by its length
and by the reciprocal of its nonzero frequency. -/
theorem norm_integral_cexp_linear_le_min {delta omega : ℝ}
    (hdelta : 0 ≤ delta) (homega : omega ≠ 0) :
    ‖∫ v in (0 : ℝ)..delta, Complex.exp (I * (omega * v))‖ ≤
      min delta (2 / |omega|) := by
  exact le_min (norm_integral_cexp_linear_le_length hdelta)
    (norm_integral_cexp_linear_le homega)

/-- Squaring the short-window estimate gives a directly reusable Fourier
kernel energy bound. -/
theorem normSq_integral_cexp_linear_le_min {delta omega : ℝ}
    (hdelta : 0 ≤ delta) (homega : omega ≠ 0) :
    Complex.normSq (∫ v in (0 : ℝ)..delta, Complex.exp (I * (omega * v))) ≤
      (min delta (2 / |omega|)) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  apply (sq_le_sq₀ (norm_nonneg _) (le_min hdelta (by positivity))).mpr
  exact norm_integral_cexp_linear_le_min hdelta homega

end MathlibAux
