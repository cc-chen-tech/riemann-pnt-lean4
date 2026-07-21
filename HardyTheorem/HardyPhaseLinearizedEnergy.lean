import HardyTheorem.HardyPhaseLinearizedSum

open Complex MeasureTheory Set

namespace HardyTheorem

open OscillatoryIntegral

/-- The weighted tangent-line coefficient appearing in the linearized first
Hardy model. -/
noncomputable def hardyPhaseLinearizedCoeff
    (n : ℕ) (delta t : ℝ) : ℂ :=
  ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
    hardyPhaseLinearizedShortIntegral n delta t

/-- The correct rectangular-window envelope, with the zero-frequency value
defined separately because division by zero in Lean is zero. -/
noncomputable def hardyPhaseLinearizedEnvelope
    (n : ℕ) (delta t : ℝ) : ℝ :=
  if deriv (hardyPhase n) t = 0 then delta
  else min delta (2 / |deriv (hardyPhase n) t|)

private theorem norm_inv_nat_cpow_half {n : ℕ} (hn : 0 < n) :
    ‖((n : ℂ) ^ (1 / 2 : ℂ))⁻¹‖ = (Real.sqrt n)⁻¹ := by
  rw [norm_inv, Complex.norm_natCast_cpow_of_pos hn]
  norm_num [Real.sqrt_eq_rpow]

/-- A nonstationary weighted linearized coefficient has both the length and
reciprocal-frequency decay of its rectangular Fourier window. -/
theorem norm_hardyPhaseLinearizedCoeff_le_min
    {n : ℕ} (hn : 0 < n) {delta t : ℝ} (hdelta : 0 ≤ delta)
    (hfreq : deriv (hardyPhase n) t ≠ 0) :
    ‖hardyPhaseLinearizedCoeff n delta t‖ ≤
      (Real.sqrt n)⁻¹ *
        min delta (2 / |deriv (hardyPhase n) t|) := by
  rw [hardyPhaseLinearizedCoeff, norm_mul, norm_inv_nat_cpow_half hn]
  exact mul_le_mul_of_nonneg_left
    (norm_hardyPhaseLinearizedShortIntegral_le_min hdelta hfreq)
    (by positivity)

/-- The same weighted coefficient has an unconditional window-length bound,
covering the stationary frequency. -/
theorem norm_hardyPhaseLinearizedCoeff_le_length
    {n : ℕ} (hn : 0 < n) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    ‖hardyPhaseLinearizedCoeff n delta t‖ ≤
      (Real.sqrt n)⁻¹ * delta := by
  rw [hardyPhaseLinearizedCoeff, norm_mul, norm_inv_nat_cpow_half hn]
  exact mul_le_mul_of_nonneg_left
    (norm_hardyPhaseLinearizedShortIntegral_le_length hdelta)
    (by positivity)

/-- Squaring the nonstationary envelope yields the termwise energy weight
used in the stationary-annulus summation. -/
theorem normSq_hardyPhaseLinearizedCoeff_le
    {n : ℕ} (hn : 0 < n) {delta t : ℝ} (hdelta : 0 ≤ delta)
    (hfreq : deriv (hardyPhase n) t ≠ 0) :
    Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
      ((Real.sqrt n)⁻¹ *
        min delta (2 / |deriv (hardyPhase n) t|)) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  apply (sq_le_sq₀ (norm_nonneg _) ?_).2
  · exact norm_hardyPhaseLinearizedCoeff_le_min hn hdelta hfreq
  · exact mul_nonneg (by positivity)
      (le_min hdelta (by positivity))

theorem hardyPhaseLinearizedEnvelope_nonneg
    (n : ℕ) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ hardyPhaseLinearizedEnvelope n delta t := by
  unfold hardyPhaseLinearizedEnvelope
  split_ifs
  · exact hdelta
  · exact le_min hdelta (by positivity)

/-- The pointwise coefficient estimate with the stationary and
nonstationary cases combined into one total envelope. -/
theorem norm_hardyPhaseLinearizedCoeff_le_envelope
    {n : ℕ} (hn : 0 < n) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    ‖hardyPhaseLinearizedCoeff n delta t‖ ≤
      (Real.sqrt n)⁻¹ * hardyPhaseLinearizedEnvelope n delta t := by
  by_cases hfreq : deriv (hardyPhase n) t = 0
  · rw [hardyPhaseLinearizedEnvelope, if_pos hfreq]
    exact norm_hardyPhaseLinearizedCoeff_le_length hn hdelta
  · rw [hardyPhaseLinearizedEnvelope, if_neg hfreq]
    exact norm_hardyPhaseLinearizedCoeff_le_min hn hdelta hfreq

/-- The unconditional termwise energy bound used by the stationary-annulus
sum. -/
theorem normSq_hardyPhaseLinearizedCoeff_le_envelope
    {n : ℕ} (hn : 0 < n) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
      ((Real.sqrt n)⁻¹ *
        hardyPhaseLinearizedEnvelope n delta t) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  apply (sq_le_sq₀ (norm_nonneg _) ?_).2
  · exact norm_hardyPhaseLinearizedCoeff_le_envelope hn hdelta
  · exact mul_nonneg (by positivity)
      (hardyPhaseLinearizedEnvelope_nonneg n hdelta)

end HardyTheorem
