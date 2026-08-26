import HardyTheorem.SelbergDiagonalKernelIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Real Set

namespace HardyTheorem

/-! # The one-term change of variables in Selberg's diagonal series. -/

noncomputable def selbergDiagonalScale (eta : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt eta * ((n + 1 : ℕ) : ℝ)

noncomputable def selbergDiagonalOriginalIntegrand
    (eta theta : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u ^ (-theta) *
    Real.exp (-(eta * (((n + 1 : ℕ) : ℝ) ^ 2) * u ^ 2))

theorem selbergDiagonalOriginalIntegrand_eq_scaled
    {eta theta u : ℝ} {n : ℕ} (heta : 0 < eta) (hu : 0 < u) :
    selbergDiagonalOriginalIntegrand eta theta n u =
      (selbergDiagonalScale eta n) ^ theta *
        selbergWeightedGaussian theta
          (selbergDiagonalScale eta n * u) := by
  have hr : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  have hb : 0 < selbergDiagonalScale eta n := mul_pos hsqrt hr
  have hpowCancel :
      (selbergDiagonalScale eta n) ^ theta *
          (selbergDiagonalScale eta n * u) ^ (-theta) =
        u ^ (-theta) := by
    rw [Real.mul_rpow hb.le hu.le]
    calc
      (selbergDiagonalScale eta n) ^ theta *
          ((selbergDiagonalScale eta n) ^ (-theta) * u ^ (-theta)) =
        ((selbergDiagonalScale eta n) ^ theta *
          (selbergDiagonalScale eta n) ^ (-theta)) * u ^ (-theta) := by ring
      _ = u ^ (-theta) := by
        rw [← Real.rpow_add hb]
        norm_num
  have hsq :
      (selbergDiagonalScale eta n * u) ^ 2 =
        eta * (((n + 1 : ℕ) : ℝ) ^ 2) * u ^ 2 := by
    unfold selbergDiagonalScale
    rw [mul_pow, mul_pow, Real.sq_sqrt heta.le]
  unfold selbergDiagonalOriginalIntegrand selbergWeightedGaussian
  rw [hsq]
  calc
    u ^ (-theta) *
        Real.exp (-(eta * (((n + 1 : ℕ) : ℝ) ^ 2) * u ^ 2)) =
      ((selbergDiagonalScale eta n) ^ theta *
        (selbergDiagonalScale eta n * u) ^ (-theta)) *
          Real.exp (-(eta * (((n + 1 : ℕ) : ℝ) ^ 2) * u ^ 2)) := by
        rw [hpowCancel]
    _ = (selbergDiagonalScale eta n) ^ theta *
        ((selbergDiagonalScale eta n * u) ^ (-theta) *
          Real.exp (-(eta * (((n + 1 : ℕ) : ℝ) ^ 2) * u ^ 2))) := by ring

theorem selbergDiagonalScale_rpow_split
    {eta theta : ℝ} {n : ℕ} (heta : 0 < eta) :
    (selbergDiagonalScale eta n) ^ (theta - 1) =
      eta ^ ((theta - 1) / 2) *
        (((n + 1 : ℕ) : ℝ) ^ (theta - 1)) := by
  have hr : 0 ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt : 0 ≤ Real.sqrt eta := Real.sqrt_nonneg eta
  unfold selbergDiagonalScale
  rw [Real.mul_rpow hsqrt hr, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul heta.le]
  congr 2
  ring

theorem integral_selbergDiagonalOriginalIntegrand_Ioi
    {eta x theta : ℝ} {n : ℕ} (heta : 0 < eta) (hx : 0 < x) :
    (∫ u in Set.Ioi x, selbergDiagonalOriginalIntegrand eta theta n u) =
      eta ^ ((theta - 1) / 2) *
        (((n + 1 : ℕ) : ℝ) ^ (theta - 1)) *
          (∫ y in Set.Ioi (selbergDiagonalScale eta n * x),
            selbergWeightedGaussian theta y) := by
  have hb : 0 < selbergDiagonalScale eta n := by
    unfold selbergDiagonalScale
    exact mul_pos (Real.sqrt_pos.2 heta) (by positivity)
  have hchange := integral_comp_mul_left_Ioi
    (selbergWeightedGaussian theta) x hb
  calc
    (∫ u in Set.Ioi x, selbergDiagonalOriginalIntegrand eta theta n u) =
      ∫ u in Set.Ioi x,
        (selbergDiagonalScale eta n) ^ theta *
          selbergWeightedGaussian theta
            (selbergDiagonalScale eta n * u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact selbergDiagonalOriginalIntegrand_eq_scaled heta (hx.trans hu)
    _ = (selbergDiagonalScale eta n) ^ theta *
        (∫ u in Set.Ioi x,
          selbergWeightedGaussian theta
            (selbergDiagonalScale eta n * u)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (selbergDiagonalScale eta n) ^ theta *
        ((selbergDiagonalScale eta n)⁻¹ *
          (∫ y in Set.Ioi (selbergDiagonalScale eta n * x),
            selbergWeightedGaussian theta y)) := by
      rw [hchange]
      rfl
    _ = (selbergDiagonalScale eta n) ^ (theta - 1) *
        (∫ y in Set.Ioi (selbergDiagonalScale eta n * x),
          selbergWeightedGaussian theta y) := by
      have hcoef :
          (selbergDiagonalScale eta n) ^ theta *
              (selbergDiagonalScale eta n)⁻¹ =
            (selbergDiagonalScale eta n) ^ (theta - 1) := by
        rw [← Real.rpow_neg_one]
        rw [← Real.rpow_add hb]
        congr 1
      rw [← mul_assoc, hcoef]
    _ = eta ^ ((theta - 1) / 2) *
        (((n + 1 : ℕ) : ℝ) ^ (theta - 1)) *
          (∫ y in Set.Ioi (selbergDiagonalScale eta n * x),
            selbergWeightedGaussian theta y) := by
      rw [selbergDiagonalScale_rpow_split heta]

end HardyTheorem
