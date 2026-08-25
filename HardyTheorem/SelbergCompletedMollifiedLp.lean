import HardyTheorem.SelbergJHighMassFinal

open Complex Filter FourierTransform MeasureTheory Set Topology
open scoped FourierTransform

namespace HardyTheorem

set_option maxHeartbeats 800000

/-! # L1/L2 control and the Mathlib-normalized Fourier pair -/

noncomputable def selbergCompletedMollifiedFComplex
    (delta : ℝ) (X : ℕ) (t : ℝ) : ℂ :=
  (selbergCompletedMollifiedF delta X t : ℂ)

theorem selbergMellinRaw_criticalLine_zero_eq_const_mul_F
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (t : ℝ) :
    selbergMellinRawIntegrand (selbergFourierZ delta 0) X
        ((1 / 2 : ℂ) + I * t) =
      (-2 * Real.sqrt (2 * Real.pi) : ℂ) *
        selbergFourierZ delta 0 ^ (1 / 2 : ℂ) *
          selbergCompletedMollifiedFComplex delta X t := by
  simpa [selbergCompletedMollifiedFComplex] using
    selbergMellinRaw_criticalLine_eq_fourierIntegrand
      hdelta0 hdeltaPi 0 X t

theorem selbergMellinRaw_zero_scalar_ne
    (delta : ℝ) :
    (-2 * Real.sqrt (2 * Real.pi) : ℂ) *
        selbergFourierZ delta 0 ^ (1 / 2 : ℂ) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0)
      (Real.sqrt_ne_zero'.2 (mul_pos (by norm_num) Real.pi_pos)))
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (selbergFourierZ_ne_zero delta 0))

theorem integrable_selbergMellinRaw_criticalLine_zero
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    Integrable (fun t : ℝ =>
      selbergMellinRawIntegrand (selbergFourierZ delta 0) X
        ((1 / 2 : ℂ) + I * t)) := by
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) by norm_num]
  apply integrable_selbergMellinRaw_vertical
    (sigma := (1 / 2 : ℝ)) hdelta0 hdeltaPi 0 X
  · exact ⟨le_rfl, by norm_num⟩
  · norm_num

theorem integrable_selbergCompletedMollifiedF_complex
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) :
    Integrable (selbergCompletedMollifiedFComplex delta X) := by
  let D : ℂ := (-2 * Real.sqrt (2 * Real.pi) : ℂ) *
    selbergFourierZ delta 0 ^ (1 / 2 : ℂ)
  let raw : ℝ → ℂ := fun t =>
    selbergMellinRawIntegrand (selbergFourierZ delta 0) X
      ((1 / 2 : ℂ) + I * t)
  have hraw : Integrable raw :=
    integrable_selbergMellinRaw_criticalLine_zero hdelta0 hdeltaPi X
  have hD : D ≠ 0 := selbergMellinRaw_zero_scalar_ne delta
  have hscaled := hraw.const_mul D⁻¹
  apply hscaled.congr
  filter_upwards with t
  have hrel := selbergMellinRaw_criticalLine_zero_eq_const_mul_F
    hdelta0 hdeltaPi X t
  have hrelD : raw t = D * selbergCompletedMollifiedFComplex delta X t := by
    simpa only [raw, D] using hrel
  change D⁻¹ * raw t = selbergCompletedMollifiedFComplex delta X t
  rw [hrelD]
  exact inv_mul_cancel_left₀ hD _

theorem fourier_selbergCompletedMollifiedF_eq_explicitKernel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (w : ℝ) :
    𝓕 (selbergCompletedMollifiedFComplex delta X) w =
      (Real.sqrt (2 * Real.pi) : ℂ) *
        selbergExplicitInverseFourierKernel delta X (2 * Real.pi * w) := by
  have hS1 := selbergS1_inverseFourier_identity
    hdelta0 hdeltaPi (2 * Real.pi * w) X
  rw [← hS1]
  unfold selbergInverseFourierIntegral selbergCompletedMollifiedFComplex
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hintegrand :
      (fun t : ℝ => Complex.exp (↑(-2 * Real.pi * t * w) * I) •
          (selbergCompletedMollifiedF delta X t : ℂ)) =
        fun t : ℝ => (selbergCompletedMollifiedF delta X t : ℂ) *
          Complex.exp (-I * ((2 * Real.pi * w) * t : ℝ)) := by
    funext t
    rw [smul_eq_mul]
    rw [mul_comm]
    congr 1
    push_cast
    ring
  rw [hintegrand]
  have hq : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  field_simp [hq.ne']

end HardyTheorem
