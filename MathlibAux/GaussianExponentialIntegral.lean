import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# A shifted Gaussian exponential integral

This is the exact Fourier kernel used when expanding a Gaussian-weighted
finite exponential-polynomial second moment.
-/

open Complex MeasureTheory

namespace MathlibAux

/-- The shifted Gaussian Fourier integrand is integrable. -/
theorem integrable_shiftedGaussian_mul_cexp
    {Delta : ℝ} (hDelta : 0 < Delta) (w xi : ℝ) :
    Integrable fun t : ℝ =>
      (Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
        Complex.exp (I * (xi : ℂ) * (t : ℂ)) := by
  have hb : 0 < (1 / Delta ^ 2 : ℝ) := by positivity
  have hweight : Integrable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) := by
    have hbase := (integrable_exp_neg_mul_sq hb).comp_sub_right w
    convert hbase using 1
    funext t
    congr 1
    field_simp [hDelta.ne']
  have hcont : Continuous fun t : ℝ =>
      (Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
        Complex.exp (I * (xi : ℂ) * (t : ℂ)) := by
    fun_prop
  apply Integrable.mono hweight hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    norm_num

/-- Exact Fourier transform of the unnormalized Gaussian centered at `w`. -/
theorem integral_shiftedGaussian_mul_cexp
    {Delta : ℝ} (hDelta : 0 < Delta) (w xi : ℝ) :
    (∫ t : ℝ,
        (Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
          Complex.exp (I * (xi : ℂ) * (t : ℂ))) =
      (Real.sqrt (Real.pi / (1 / Delta ^ 2)) : ℂ) *
        Complex.exp (-(Delta ^ 2 * xi ^ 2) / 4 : ℝ) *
          Complex.exp (I * (xi : ℂ) * (w : ℂ)) := by
  have hb : 0 < ((1 / Delta ^ 2 : ℝ) : ℂ).re := by
    simp only [ofReal_re]
    positivity
  have hfourier := fourierIntegral_gaussian
    (b := ((1 / Delta ^ 2 : ℝ) : ℂ)) hb (xi : ℂ)
  have hsqrt :
      ((Real.pi : ℂ) / ((1 / Delta ^ 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
        (Real.sqrt (Real.pi / (1 / Delta ^ 2)) : ℂ) := by
    symm
    rw [Real.sqrt_eq_rpow]
    simpa only [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow
        (show 0 ≤ Real.pi / (1 / Delta ^ 2) by positivity)
        (1 / 2 : ℝ))
  have hexponent :
      -((xi : ℂ) ^ 2) / (4 * ((1 / Delta ^ 2 : ℝ) : ℂ)) =
        ((-(Delta ^ 2 * xi ^ 2) / 4 : ℝ) : ℂ) := by
    push_cast
    field_simp [hDelta.ne']
  have hcentered :
      (∫ u : ℝ,
          (Real.exp (-(u ^ 2) / Delta ^ 2) : ℂ) *
            Complex.exp (I * (xi : ℂ) * (u : ℂ))) =
        (Real.sqrt (Real.pi / (1 / Delta ^ 2)) : ℂ) *
          Complex.exp (-(Delta ^ 2 * xi ^ 2) / 4 : ℝ) := by
    have hintegrand :
        (fun u : ℝ =>
          (Real.exp (-(u ^ 2) / Delta ^ 2) : ℂ) *
            Complex.exp (I * (xi : ℂ) * (u : ℂ))) =
        fun u : ℝ =>
          Complex.exp (I * (xi : ℂ) * (u : ℂ)) *
            Complex.exp (-((1 / Delta ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ 2) := by
      funext u
      rw [mul_comm]
      congr 1
      rw [ofReal_exp]
      congr 1
      push_cast
      field_simp [hDelta.ne']
    rw [hintegrand, hfourier, hsqrt, hexponent]
  let base : ℝ → ℂ := fun u =>
    (Real.exp (-(u ^ 2) / Delta ^ 2) : ℂ) *
      Complex.exp (I * (xi : ℂ) * (u : ℂ))
  have hshift :
      (∫ t : ℝ, base (t - w)) = ∫ u : ℝ, base u := by
    exact integral_sub_right_eq_self base w
  have hfactor (t : ℝ) :
      (Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
          Complex.exp (I * (xi : ℂ) * (t : ℂ)) =
        base (t - w) * Complex.exp (I * (xi : ℂ) * (w : ℂ)) := by
    dsimp [base]
    have hphase :
        Complex.exp (I * (xi : ℂ) * (t : ℂ)) =
          Complex.exp (I * (xi : ℂ) * ((t - w : ℝ) : ℂ)) *
            Complex.exp (I * (xi : ℂ) * (w : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hphase]
    exact (mul_assoc _ _ _).symm
  simp_rw [hfactor, integral_mul_const, hshift]
  rw [show (∫ u : ℝ, base u) =
      (Real.sqrt (Real.pi / (1 / Delta ^ 2)) : ℂ) *
        Complex.exp (-(Delta ^ 2 * xi ^ 2) / 4 : ℝ) by
    simpa [base] using hcentered]

end MathlibAux
