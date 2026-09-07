import HardyTheorem.AFECriticalUnitPhaseLogProof
import PrimeNumberTheorem.CarlsonUnitPhaseLogProductIntegrable

/-! The actual unconditional half-range critical product moment, with all
constants and logarithms normalized uniformly for Carlson interpolation. -/

open Complex Filter MeasureTheory

namespace PrimeNumberTheorem.CarlsonZeroDensity

/-- The proved weak AFE discharges the last premise of the full-line
Gaussian product estimate.  The result is uniform in centre and length. -/
theorem exists_eventually_integral_gaussian_product_le_halfRange_powerLog :
    ∃ C > (0 : ℝ), ∀ᶠ V : ℝ in atTop, ∀ (w : ℝ) (X : ℕ),
      2 * V ≤ w → w ≤ 3 * V → 2 ≤ X → (X : ℝ) ≤ V ^ (9 / 20 : ℝ) →
      (∫ t : ℝ, carlsonGaussianWeight (16 * V ^ (19 / 20 : ℝ)) w t *
        ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
        C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6 := by
  obtain ⟨R, hR, hmoment⟩ :=
    integral_gaussian_product_le_halfRange_simpleScale_of_unitPhase_log_target
      HardyTheorem.AFE.zeta_critical_unitPhase_logAfe
  let A : ℝ := 1 + Real.log 4
  let G : ℝ := MathlibAux.gaussianBucketSchurConstant
  let C : ℝ := 48 * Real.sqrt Real.pi * (256 * G * A ^ 6 + 4 * R ^ 2) + 1
  have hG : 0 < G := MathlibAux.gaussianBucketSchurConstant_pos
  have hA1 : 1 ≤ A := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [A]
    linarith
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  filter_upwards [hmoment, eventually_ge_atTop (1 : ℝ)] with V hmoment hV
  intro w X hwL hwU hX hXV
  have hV0 : 0 < V := by linarith
  let P : ℝ := V ^ (19 / 20 : ℝ)
  let L : ℝ := 1 + Real.log V
  have hP1 : 1 ≤ P := Real.one_le_rpow hV (by norm_num)
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hV]
  have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ hL1
  have hlog : 1 + Real.log (4 * V) ≤ A * L := by
    rw [Real.log_mul (by norm_num) hV0.ne']
    have hprod := mul_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num))
      (Real.log_nonneg hV)
    dsimp only [A, L]
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log (4 * V) := by
    have hlog4 := Real.log_nonneg (show 1 ≤ 4 * V by linarith)
    linarith
  have hlogPow : (1 + Real.log (4 * V)) ^ 6 ≤ A ^ 6 * L ^ 6 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hlog0 hlog 6
  have hbracket : 256 * G * (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2 ≤
      (256 * G * A ^ 6 + 4 * R ^ 2) * L ^ 6 := by
    have hfirst := mul_le_mul_of_nonneg_left hlogPow (show 0 ≤ 256 * G by positivity)
    have hlast := le_mul_of_one_le_right (show 0 ≤ 4 * R ^ 2 by positivity) hL6
    nlinarith
  have hmass : Real.sqrt (Real.pi / (1 / (16 * P) ^ 2)) =
      16 * Real.sqrt Real.pi * P := by
    rw [div_div_eq_mul_div, div_one, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (show 0 ≤ 16 * P by positivity)]
    ring
  have hraw := hmoment w X hwL hwU hX hXV
  change (∫ t : ℝ, carlsonGaussianWeight (16 * P) w t *
    ‖linearLogSelbergMollifiedZetaProduct X ((1 / 2 : ℂ) + I * (t : ℂ))‖ ^ 2) ≤ _ at hraw
  rw [hmass] at hraw
  have hone : 1 ≤ P * L ^ 6 := one_le_mul_of_one_le_of_one_le hP1 hL6
  calc
    _ ≤ 3 * (16 * Real.sqrt Real.pi * P) *
        (256 * G * (1 + Real.log (4 * V)) ^ 6 + 4 * R ^ 2) + 1 := hraw
    _ ≤ 3 * (16 * Real.sqrt Real.pi * P) *
        ((256 * G * A ^ 6 + 4 * R ^ 2) * L ^ 6) + P * L ^ 6 :=
      add_le_add (mul_le_mul_of_nonneg_left hbracket (by positivity)) hone
    _ = _ := by dsimp only [C, P, L]; ring

end PrimeNumberTheorem.CarlsonZeroDensity
