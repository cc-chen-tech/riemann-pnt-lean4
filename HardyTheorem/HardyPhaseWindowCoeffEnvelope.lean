import HardyTheorem.HardyPhaseWindowCoeffDerivative
import MathlibAux.RectangularFourierFirstMoment

open Complex MeasureTheory Set

namespace HardyTheorem

private theorem norm_inv_nat_cpow_half_envelope {n : ℕ} (hn : 0 < n) :
    ‖((n : ℂ) ^ (1 / 2 : ℂ))⁻¹‖ = (Real.sqrt n)⁻¹ := by
  rw [norm_inv, Complex.norm_natCast_cpow_of_pos hn]
  norm_num [Real.sqrt_eq_rpow]

/-- Away from the stationary frequency, the derivative of the moving Hardy
window coefficient inherits the oscillatory first-moment envelope. -/
theorem norm_deriv_hardyPhaseWindowCoeff_le_min
    {n : ℕ} (hn : 0 < n) {delta t : ℝ}
    (hdelta : 0 ≤ delta) (ht : 0 < t)
    (hfreq : deriv thetaModel t - Real.log n ≠ 0) :
    ‖deriv (hardyPhaseWindowCoeff n delta) t‖ ≤
      (Real.sqrt n)⁻¹ * (1 / (2 * t)) *
        min (delta ^ 2 / 2)
          (delta / |deriv thetaModel t - Real.log n| +
            2 / (deriv thetaModel t - Real.log n) ^ 2) := by
  rw [(hasDerivAt_hardyPhaseWindowCoeff n ht).deriv,
    hardyPhaseWindowCoeffDerivValue, norm_mul,
    norm_inv_nat_cpow_half_envelope hn]
  let omega : ℝ := deriv thetaModel t - Real.log n
  have hrewrite :
      (∫ v in (0 : ℝ)..delta,
          (I * ((v / (2 * t) : ℝ) : ℂ)) *
            Complex.exp (I * (((omega * v : ℝ) : ℂ)))) =
        (I / (((2 * t : ℝ) : ℂ))) *
          ∫ v in (0 : ℝ)..delta,
            (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ))) := by
    calc
      (∫ v in (0 : ℝ)..delta,
          (I * ((v / (2 * t) : ℝ) : ℂ)) *
            Complex.exp (I * (((omega * v : ℝ) : ℂ)))) =
          ∫ v in (0 : ℝ)..delta,
            (I / (((2 * t : ℝ) : ℂ))) *
              ((v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ)))) := by
            apply intervalIntegral.integral_congr
            intro v hv
            push_cast
            ring
      _ = (I / (((2 * t : ℝ) : ℂ))) *
          ∫ v in (0 : ℝ)..delta,
            (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ))) :=
        intervalIntegral.integral_const_mul _ _
  change
    (Real.sqrt n)⁻¹ *
        ‖∫ v in (0 : ℝ)..delta,
          (I * ((v / (2 * t) : ℝ) : ℂ)) *
            Complex.exp (I * ((((omega : ℝ) * v : ℝ) : ℂ)))‖ ≤ _
  rw [hrewrite, norm_mul]
  have hfactor : ‖I / (((2 * t : ℝ) : ℂ))‖ = 1 / (2 * t) := by
    rw [norm_div, norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * t)]
  rw [hfactor]
  have hfreqOmega : omega ≠ 0 := by simpa only [omega] using hfreq
  have hmoment := MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_min
    hdelta hfreqOmega
  have hmoment' :
      ‖∫ v in (0 : ℝ)..delta,
        (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ)))‖ ≤
        min (delta ^ 2 / 2)
          (delta / |deriv thetaModel t - Real.log n| +
            2 / (deriv thetaModel t - Real.log n) ^ 2) := by
    simpa only [omega] using hmoment
  have hscale : 0 ≤ (Real.sqrt n)⁻¹ * (1 / (2 * t)) := by positivity
  calc
    (Real.sqrt n)⁻¹ *
        (1 / (2 * t) *
          ‖∫ v in (0 : ℝ)..delta,
            (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ)))‖) =
        ((Real.sqrt n)⁻¹ * (1 / (2 * t))) *
          ‖∫ v in (0 : ℝ)..delta,
            (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ)))‖ := by ring
    _ ≤ ((Real.sqrt n)⁻¹ * (1 / (2 * t))) *
        min (delta ^ 2 / 2)
          (delta / |deriv thetaModel t - Real.log n| +
            2 / (deriv thetaModel t - Real.log n) ^ 2) :=
      mul_le_mul_of_nonneg_left hmoment' hscale
    _ = (Real.sqrt n)⁻¹ * (1 / (2 * t)) *
        min (delta ^ 2 / 2)
          (delta / |deriv thetaModel t - Real.log n| +
            2 / (deriv thetaModel t - Real.log n) ^ 2) := by ring

/-- The same derivative always has the nonoscillatory first-moment bound. -/
theorem norm_deriv_hardyPhaseWindowCoeff_le_trivial
    {n : ℕ} (hn : 0 < n) {delta t : ℝ}
    (hdelta : 0 ≤ delta) (ht : 0 < t) :
    ‖deriv (hardyPhaseWindowCoeff n delta) t‖ ≤
      (Real.sqrt n)⁻¹ * (1 / (2 * t)) * (delta ^ 2 / 2) := by
  rw [(hasDerivAt_hardyPhaseWindowCoeff n ht).deriv,
    hardyPhaseWindowCoeffDerivValue, norm_mul,
    norm_inv_nat_cpow_half_envelope hn]
  let omega : ℝ := deriv thetaModel t - Real.log n
  have hrewrite :
      (∫ v in (0 : ℝ)..delta,
          (I * ((v / (2 * t) : ℝ) : ℂ)) *
            Complex.exp (I * (((omega * v : ℝ) : ℂ)))) =
        (I / (((2 * t : ℝ) : ℂ))) *
          ∫ v in (0 : ℝ)..delta,
            (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ))) := by
    calc
      (∫ v in (0 : ℝ)..delta,
          (I * ((v / (2 * t) : ℝ) : ℂ)) *
            Complex.exp (I * (((omega * v : ℝ) : ℂ)))) =
          ∫ v in (0 : ℝ)..delta,
            (I / (((2 * t : ℝ) : ℂ))) *
              ((v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ)))) := by
            apply intervalIntegral.integral_congr
            intro v hv
            push_cast
            ring
      _ = (I / (((2 * t : ℝ) : ℂ))) *
          ∫ v in (0 : ℝ)..delta,
            (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ))) :=
        intervalIntegral.integral_const_mul _ _
  change
    (Real.sqrt n)⁻¹ *
        ‖∫ v in (0 : ℝ)..delta,
          (I * ((v / (2 * t) : ℝ) : ℂ)) *
            Complex.exp (I * ((((omega : ℝ) * v : ℝ) : ℂ)))‖ ≤ _
  rw [hrewrite, norm_mul]
  have hfactor : ‖I / (((2 * t : ℝ) : ℂ))‖ = 1 / (2 * t) := by
    rw [norm_div, norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * t)]
  rw [hfactor]
  have hmoment := MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_trivial
    (omega := omega) hdelta
  have hmoment' :
      ‖∫ v in (0 : ℝ)..delta,
        (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ)))‖ ≤
        delta ^ 2 / 2 := by
    exact hmoment
  have hscale : 0 ≤ (Real.sqrt n)⁻¹ * (1 / (2 * t)) := by positivity
  calc
    (Real.sqrt n)⁻¹ *
        (1 / (2 * t) *
          ‖∫ v in (0 : ℝ)..delta,
            (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ)))‖) =
        ((Real.sqrt n)⁻¹ * (1 / (2 * t))) *
          ‖∫ v in (0 : ℝ)..delta,
            (v : ℂ) * Complex.exp (I * ((omega : ℂ) * (v : ℂ)))‖ := by ring
    _ ≤ ((Real.sqrt n)⁻¹ * (1 / (2 * t))) * (delta ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hmoment' hscale
    _ = (Real.sqrt n)⁻¹ * (1 / (2 * t)) * (delta ^ 2 / 2) := by ring

end HardyTheorem
