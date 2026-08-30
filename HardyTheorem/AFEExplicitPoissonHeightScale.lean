import HardyTheorem.AFEExplicitPoissonFrequencyCutoff

/-! Elementary conversion of the square-root Poisson budget to the height
scale of the logarithmic unit-phase AFE. -/

namespace HardyTheorem.AFE

theorem sqrt_heightCell_logAfe_scales {t : ℝ} {K : ℕ} (hK : 6 ≤ K)
    (htL : 2 * Real.pi * (K : ℝ) ^ 2 ≤ t)
    (htU : t ≤ 2 * Real.pi * ((K : ℝ) + 1) ^ 2) :
    let M := Nat.ceil (t / (Real.pi * K))
    1 ≤ t ∧
      (K : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 * t ^ (-1 / 4 : ℝ) ∧
      1 + Real.log M ≤ 1 + Real.log t ∧
      2 * Real.sqrt K * Real.exp (-2 * Real.pi * t) ≤ t ^ (-1 / 4 : ℝ) := by
  let M := Nat.ceil (t / (Real.pi * K))
  have hK6 : 6 ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : 0 < (K : ℝ) := by linarith
  have htK : (K : ℝ) ^ 2 ≤ t := by
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg (K : ℝ))
    nlinarith
  have ht1 : 1 ≤ t := by nlinarith [htK]
  have ht0 : 0 < t := by linarith
  have hKt : (K : ℝ) ≤ t := by nlinarith [htK]
  have htupper : t ≤ 16 * (K : ℝ) ^ 2 := by
    have hsq : ((K : ℝ) + 1) ^ 2 ≤ 2 * (K : ℝ) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2 * Real.pi by positivity)
    have hpi := mul_le_mul_of_nonneg_right (show 2 * Real.pi ≤ 8 by linarith [Real.pi_lt_four])
      (show 0 ≤ 2 * (K : ℝ) ^ 2 by positivity)
    nlinarith
  have hscale : (K : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 * t ^ (-1 / 4 : ℝ) := by
    have h16 : (16 : ℝ) ^ (-1 / 4 : ℝ) = 1 / 2 := by
      calc
        _ = ((2 : ℝ) ^ 4) ^ (-1 / 4 : ℝ) := by norm_num
        _ = (2 : ℝ) ^ ((4 : ℝ) * (-1 / 4)) :=
          (Real.rpow_natCast_mul (by norm_num) 4 _).symm
        _ = _ := by norm_num
    have hpow := Real.rpow_le_rpow_of_nonpos ht0 htupper (by norm_num : (-1 / 4 : ℝ) ≤ 0)
    rw [Real.mul_rpow (by norm_num) (sq_nonneg (K : ℝ)), h16,
      ← Real.rpow_natCast_mul hK0.le 2] at hpow
    norm_num only at hpow
    linarith
  obtain ⟨hML, hMU, _, _⟩ := sqrt_heightCell_frequency_cutoff hK htL htU
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < M by change 2 * K ≤ M at hML; omega)
  have hMt : (M : ℝ) ≤ t := by
    have hM' : (M : ℝ) ≤ 2 * (K : ℝ) + 5 := by exact_mod_cast hMU
    nlinarith [htK]
  have hlog : 1 + Real.log M ≤ 1 + Real.log t :=
    add_le_add le_rfl (Real.log_le_log hMpos hMt)
  have hphase : 2 * Real.sqrt K * Real.exp (-2 * Real.pi * t) ≤ t ^ (-1 / 4 : ℝ) := by
    have hexp : 2 * t ≤ Real.exp (2 * Real.pi * t) := by
      have hpi : 2 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hmul := mul_le_mul_of_nonneg_right hpi ht0.le
      linarith [Real.add_one_le_exp (2 * Real.pi * t)]
    have hexpInv : Real.exp (-2 * Real.pi * t) ≤ (2 * t)⁻¹ := by
      rw [show -2 * Real.pi * t = -(2 * Real.pi * t) by ring, Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hexp
    calc
      _ ≤ 2 * Real.sqrt t * (2 * t)⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hKt) (by norm_num))
          hexpInv (Real.exp_pos _).le (by positivity)
      _ = (Real.sqrt t)⁻¹ := by
        have hs0 := Real.sqrt_pos.mpr ht0
        field_simp
        nlinarith [Real.sq_sqrt ht0.le]
      _ = t ^ (-(1 / 2) : ℝ) := by rw [Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  exact ⟨ht1, hscale, hlog, hphase⟩

end HardyTheorem.AFE
