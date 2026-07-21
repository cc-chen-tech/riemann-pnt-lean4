import MathlibAux.DirichletPolynomialMeanSquare

open Complex MeasureTheory Set

namespace MathlibAux

/-- Exact integration by parts for the first moment of a rectangular Fourier
window at nonzero frequency. -/
theorem intervalIntegral_mul_cexp_linear_eq_integration_by_parts
    {delta omega : ℝ} (homega : omega ≠ 0) :
    (∫ v in (0 : ℝ)..delta,
      (v : ℂ) * Complex.exp (I * (omega * v))) =
      (delta : ℂ) * Complex.exp (I * (omega * delta)) / (I * (omega : ℂ)) -
        (∫ v in (0 : ℝ)..delta,
          Complex.exp (I * (omega * v))) / (I * (omega : ℂ)) := by
  let c : ℂ := I * (omega : ℂ)
  have hc : c ≠ 0 := by
    exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr homega)
  have h_exp :
      (∫ v in (0 : ℝ)..delta, Complex.exp (c * v)) =
        (Complex.exp (c * delta) - 1) / c := by
    simpa using
      (integral_exp_mul_complex (a := (0 : ℝ)) (b := delta) hc)
  have h_deriv (x : ℝ) :
      HasDerivAt
        (fun y : ℝ => Complex.exp (c * y) * ((y : ℂ) / c - 1 / c ^ 2))
        ((x : ℂ) * Complex.exp (c * x)) x := by
    have h_exp_deriv : HasDerivAt (fun y : ℝ => Complex.exp (c * y))
        (Complex.exp (c * x) * c) x := by
      apply (Complex.hasDerivAt_exp (c * x)).comp x
      simpa only [mul_one] using
        ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
    have h_linear_deriv : HasDerivAt
        (fun y : ℝ => (y : ℂ) / c - 1 / c ^ 2) (1 / c) x := by
      simpa using
        (((hasDerivAt_id (x : ℂ)).comp_ofReal.div_const c).sub_const (1 / c ^ 2))
    convert h_exp_deriv.mul h_linear_deriv using 1
    field_simp
    ring
  have h_weighted :
      (∫ v in (0 : ℝ)..delta, (v : ℂ) * Complex.exp (c * v)) =
        Complex.exp (c * delta) * ((delta : ℂ) / c - 1 / c ^ 2) + 1 / c ^ 2 := by
    calc
      _ = ∫ v in (0 : ℝ)..delta,
          deriv (fun y : ℝ => Complex.exp (c * y) *
            ((y : ℂ) / c - 1 / c ^ 2)) v := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact (h_deriv x).deriv.symm
      _ = _ := by
          rw [intervalIntegral.integral_deriv_eq_sub]
          · simp
          · intro x hx
            exact (h_deriv x).differentiableAt
          · apply ((Complex.continuous_ofReal.mul
              (Complex.continuous_exp.comp
                (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable 0 delta).congr
            intro x hx
            exact (h_deriv x).deriv.symm
  have h_formula :
      (∫ v in (0 : ℝ)..delta, (v : ℂ) * Complex.exp (c * v)) =
        (delta : ℂ) * Complex.exp (c * delta) / c -
          (∫ v in (0 : ℝ)..delta, Complex.exp (c * v)) / c := by
    rw [h_weighted, h_exp]
    field_simp
    ring
  simpa [c, ofReal_mul, mul_assoc] using h_formula

/-- The first moment of a rectangular Fourier window has the standard
integration-by-parts oscillatory bound. -/
theorem norm_intervalIntegral_mul_cexp_linear_le_oscillatory
    {delta omega : ℝ} (hdelta : 0 ≤ delta) (homega : omega ≠ 0) :
    ‖∫ v in (0 : ℝ)..delta,
      (v : ℂ) * Complex.exp (I * (omega * v))‖ ≤
      delta / |omega| + 2 / omega ^ 2 := by
  rw [intervalIntegral_mul_cexp_linear_eq_integration_by_parts homega]
  calc
    ‖(delta : ℂ) * Complex.exp (I * (omega * delta)) / (I * (omega : ℂ)) -
        (∫ v in (0 : ℝ)..delta,
          Complex.exp (I * (omega * v))) / (I * (omega : ℂ))‖ ≤
        ‖(delta : ℂ) * Complex.exp (I * (omega * delta)) / (I * (omega : ℂ))‖ +
          ‖(∫ v in (0 : ℝ)..delta,
            Complex.exp (I * (omega * v))) / (I * (omega : ℂ))‖ :=
      norm_sub_le _ _
    _ = delta / |omega| +
          ‖∫ v in (0 : ℝ)..delta, Complex.exp (I * (omega * v))‖ / |omega| := by
      have hden : ‖I * (omega : ℂ)‖ = |omega| := by
        rw [norm_mul, norm_I, norm_real]
        norm_num
      have hexp : ‖Complex.exp (I * (omega * delta))‖ = 1 := by
        rw [Complex.norm_exp]
        norm_num
      rw [norm_div, norm_div, norm_mul, norm_real, hden, hexp,
        Real.norm_eq_abs, abs_of_nonneg hdelta, mul_one]
    _ ≤ delta / |omega| + (2 / |omega|) / |omega| := by
      gcongr
      exact norm_integral_cexp_linear_le homega
    _ = delta / |omega| + 2 / omega ^ 2 := by
      rw [div_div, ← sq_abs]
      congr 1
      ring

/-- The first moment of a rectangular Fourier window is bounded by the
integral of its pointwise norm. -/
theorem norm_intervalIntegral_mul_cexp_linear_le_trivial
    {delta omega : ℝ} (hdelta : 0 ≤ delta) :
    ‖∫ v in (0 : ℝ)..delta,
      (v : ℂ) * Complex.exp (I * (omega * v))‖ ≤ delta ^ 2 / 2 := by
  calc
    ‖∫ v in (0 : ℝ)..delta,
        (v : ℂ) * Complex.exp (I * (omega * v))‖ ≤
        ∫ v in (0 : ℝ)..delta,
          ‖(v : ℂ) * Complex.exp (I * (omega * v))‖ :=
      intervalIntegral.norm_integral_le_integral_norm hdelta
    _ = ∫ v in (0 : ℝ)..delta, v := by
      apply intervalIntegral.integral_congr
      intro v hv
      change ‖(v : ℂ) * Complex.exp (I * (omega * v))‖ = v
      rw [norm_mul, norm_real]
      have hv0 : 0 ≤ v := by
        rcases mem_uIcc.mp hv with hv | hv
        · exact hv.1
        · exact hdelta.trans hv.1
      have hexp : ‖Complex.exp (I * (omega * v))‖ = 1 := by
        rw [Complex.norm_exp]
        norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg hv0, hexp, mul_one]
    _ = delta ^ 2 / 2 := by
      rw [integral_id]
      ring

/-- Combining the trivial and integration-by-parts estimates gives a uniform
rectangular Fourier first-moment bound. -/
theorem norm_intervalIntegral_mul_cexp_linear_le_min
    {delta omega : ℝ} (hdelta : 0 ≤ delta) (homega : omega ≠ 0) :
    ‖∫ v in (0 : ℝ)..delta,
      (v : ℂ) * Complex.exp (I * (omega * v))‖ ≤
      min (delta ^ 2 / 2) (delta / |omega| + 2 / omega ^ 2) := by
  exact le_min
    (norm_intervalIntegral_mul_cexp_linear_le_trivial hdelta)
    (norm_intervalIntegral_mul_cexp_linear_le_oscillatory hdelta homega)

end MathlibAux
