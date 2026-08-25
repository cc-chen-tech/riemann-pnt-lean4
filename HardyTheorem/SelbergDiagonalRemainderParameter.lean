import HardyTheorem.SelbergDiagonalArithmeticMain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace HardyTheorem

/-! # Uniform parameter bound for Selberg's diagonal kernel remainder. -/

theorem delta_le_two_pi_mul_sin
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    delta ≤ 2 * Real.pi * Real.sin delta := by
  have hdeltaPi : delta ≤ Real.pi / 2 := by
    nlinarith [Real.two_le_pi]
  have hsin := Real.mul_le_sin hdelta0.le hdeltaPi
  have hmul := mul_le_mul_of_nonneg_left hsin Real.pi_pos.le
  have hid : Real.pi * (2 / Real.pi * delta) = 2 * delta := by
    field_simp [Real.pi_ne_zero]
  rw [hid] at hmul
  linarith

theorem delta_div_fourth_le_selbergDiagonalGaussianParameter
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa mu q : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hmu : 1 ≤ mu) (hq : 1 ≤ q) (hqX : q ≤ X ^ 2) :
    delta / (X : ℝ) ^ 4 ≤
      selbergDiagonalGaussianParameter delta kappa mu q := by
  have hdeltaPi : delta ≤ Real.pi / 2 := by
    nlinarith [Real.two_le_pi]
  have hsin := Real.mul_le_sin hdelta0.le hdeltaPi
  have hsin0 : 0 ≤ Real.sin delta :=
    (Real.mul_le_sin hdelta0.le hdeltaPi).trans' (by positivity)
  have hc : delta ≤ 2 * Real.pi * Real.sin delta :=
    delta_le_two_pi_mul_sin hdelta0 hdelta1
  have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqXR : (q : ℝ) ≤ (X : ℝ) ^ 2 := by
    exact_mod_cast hqX
  have hnum : (1 : ℝ) ≤ ((kappa * mu : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hkappa hmu
  have hratio : (1 : ℝ) / (X : ℝ) ^ 2 ≤
      ((kappa * mu : ℕ) : ℝ) / (q : ℝ) := by
    calc
      (1 : ℝ) / (X : ℝ) ^ 2 ≤ 1 / (q : ℝ) :=
        one_div_le_one_div_of_le hq0 hqXR
      _ ≤ ((kappa * mu : ℕ) : ℝ) / (q : ℝ) := by
        exact (div_le_div_iff_of_pos_right hq0).2 hnum
  have hs0 : 0 ≤ (1 : ℝ) / (X : ℝ) ^ 2 := by positivity
  have hr0 : 0 ≤ ((kappa * mu : ℕ) : ℝ) / (q : ℝ) := by positivity
  have hsquare : ((1 : ℝ) / (X : ℝ) ^ 2) ^ 2 ≤
      (((kappa * mu : ℕ) : ℝ) / (q : ℝ)) ^ 2 := by
    nlinarith
  have hprod := mul_le_mul hc hsquare (sq_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hsin0)
  unfold selbergDiagonalGaussianParameter
  calc
    delta / (X : ℝ) ^ 4 =
        delta * ((1 : ℝ) / (X : ℝ) ^ 2) ^ 2 := by
      field_simp [hX0.ne']
    _ ≤ (2 * Real.pi * Real.sin delta) *
        ((((kappa * mu : ℕ) : ℝ) / (q : ℝ)) ^ 2) := hprod

theorem inv_selbergDiagonalGaussianParameter_le
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa mu q : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hmu : 1 ≤ mu) (hq : 1 ≤ q) (hqX : q ≤ X ^ 2) :
    (selbergDiagonalGaussianParameter delta kappa mu q)⁻¹ ≤
      (X : ℝ) ^ 4 / delta := by
  have hbase0 : 0 < delta / (X : ℝ) ^ 4 := by positivity
  have hbase := delta_div_fourth_le_selbergDiagonalGaussianParameter
    hdelta0 hdelta1 hX hkappa hmu hq hqX
  have heta0 : 0 < selbergDiagonalGaussianParameter delta kappa mu q :=
    hbase0.trans_le hbase
  calc
    (selbergDiagonalGaussianParameter delta kappa mu q)⁻¹ ≤
        (delta / (X : ℝ) ^ 4)⁻¹ :=
      (inv_le_inv₀ heta0 hbase0).2 hbase
    _ = (X : ℝ) ^ 4 / delta := by
      field_simp [hdelta0.ne']

theorem log_two_add_inv_selbergDiagonalGaussianParameter_le
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    {X kappa mu q : ℕ} (hX : 1 ≤ X) (hkappa : 1 ≤ kappa)
    (hmu : 1 ≤ mu) (hq : 1 ≤ q) (hqX : q ≤ X ^ 2) :
    Real.log (2 + (selbergDiagonalGaussianParameter delta kappa mu q)⁻¹) ≤
      Real.log (2 + (X : ℝ) ^ 4 / delta) := by
  have hbase0 : 0 < delta / (X : ℝ) ^ 4 := by positivity
  have hbase := delta_div_fourth_le_selbergDiagonalGaussianParameter
    hdelta0 hdelta1 hX hkappa hmu hq hqX
  have heta0 : 0 < selbergDiagonalGaussianParameter delta kappa mu q :=
    hbase0.trans_le hbase
  apply Real.log_le_log
  · exact add_pos_of_pos_of_nonneg (by norm_num) (inv_nonneg.mpr heta0.le)
  · simpa only [add_comm] using add_le_add_left
      (inv_selbergDiagonalGaussianParameter_le
        hdelta0 hdelta1 hX hkappa hmu hq hqX) 2

end HardyTheorem
