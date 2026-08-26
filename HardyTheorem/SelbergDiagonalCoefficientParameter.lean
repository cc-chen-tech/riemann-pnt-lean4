import HardyTheorem.SelbergDiagonalRemainderSum

namespace Real

theorem rpow_le_rpow_of_le_of_nonpos
    {a b e : ℝ} (ha : 0 < a) (hab : a ≤ b) (he : e ≤ 0) :
    b ^ e ≤ a ^ e := by
  have hb : 0 < b := ha.trans_le hab
  rw [show e = -(-e) by ring, Real.rpow_neg hb.le, Real.rpow_neg ha.le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hb (-e))
    (Real.rpow_pos_of_pos ha (-e))).2
      (Real.rpow_le_rpow ha.le hab (neg_nonneg.mpr he))

end Real

namespace HardyTheorem

/-! # Uniform bounds for the two signed diagonal coefficients. -/

theorem abs_selbergDiagonalSZeroCoefficient_le
    {delta x theta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 0 < x) (htheta : 0 < theta) :
    |selbergDiagonalSZeroCoefficient delta x theta| ≤
      (Real.sqrt Real.pi / 2) * delta ^ (-(1 / 2 : ℝ)) *
        x ^ (-theta) / theta := by
  have hcLower := delta_le_two_pi_mul_sin hdelta0 hdelta1
  have hc : 0 < 2 * Real.pi * Real.sin delta := hdelta0.trans_le hcLower
  have hpow := Real.rpow_le_rpow_of_le_of_nonpos hdelta0 hcLower
    (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hsqrt0 : 0 ≤ Real.sqrt Real.pi / 2 := by positivity
  have hxpow0 : 0 ≤ x ^ (-theta) := Real.rpow_nonneg hx.le _
  unfold selbergDiagonalSZeroCoefficient
  rw [abs_mul, abs_mul, abs_div, abs_of_pos htheta,
    abs_of_nonneg hsqrt0, abs_of_nonneg hxpow0,
    abs_of_nonneg (Real.rpow_nonneg hc.le _)]
  calc
    (Real.sqrt Real.pi / 2 / theta * x ^ (-theta)) *
        (2 * Real.pi * Real.sin delta) ^ (-(1 / 2 : ℝ)) ≤
      (Real.sqrt Real.pi / 2 / theta * x ^ (-theta)) *
        delta ^ (-(1 / 2 : ℝ)) := by
      gcongr
    _ = (Real.sqrt Real.pi / 2) * delta ^ (-(1 / 2 : ℝ)) *
        x ^ (-theta) / theta := by ring

theorem abs_selbergDiagonalSThetaCoefficient_le
    {delta theta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    |selbergDiagonalSThetaCoefficient delta theta| ≤
      (1 / 2 * Real.Gamma (1 / 4)) / theta *
        delta ^ ((theta - 1) / 2) := by
  have hcLower := delta_le_two_pi_mul_sin hdelta0 hdelta1
  have hc : 0 < 2 * Real.pi * Real.sin delta := hdelta0.trans_le hcLower
  have hexp : (theta - 1) / 2 ≤ 0 := by linarith
  have hpow := Real.rpow_le_rpow_of_le_of_nonpos hdelta0 hcLower hexp
  have hK := abs_selbergDiagonalK1_le htheta0 hthetaHalf
  have hGamma0 : 0 ≤ (1 / 2 : ℝ) * Real.Gamma (1 / 4) := by
    positivity
  unfold selbergDiagonalSThetaCoefficient
  rw [abs_mul, abs_div, abs_of_pos htheta0,
    abs_of_nonneg (Real.rpow_nonneg hc.le _)]
  calc
    (|selbergDiagonalK1 theta| / theta) *
        (2 * Real.pi * Real.sin delta) ^ ((theta - 1) / 2) ≤
      ((1 / 2 * Real.Gamma (1 / 4)) / theta) *
        delta ^ ((theta - 1) / 2) := by
      gcongr

end HardyTheorem
