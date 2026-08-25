import HardyTheorem.SelbergEulerPowerFloor
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Gamma

open MeasureTheory Real Set

namespace HardyTheorem

/-! # Scalar Gaussian integrals in Selberg's diagonal kernel. -/

noncomputable def selbergWeightedGaussian (theta y : ℝ) : ℝ :=
  y ^ (-theta) * Real.exp (-y ^ 2)

theorem integral_selbergWeightedGaussian_Ioi
    {theta : ℝ} (htheta1 : theta < 1) :
    (∫ y in Set.Ioi (0 : ℝ), selbergWeightedGaussian theta y) =
      (1 / 2 : ℝ) * Real.Gamma ((1 - theta) / 2) := by
  unfold selbergWeightedGaussian
  calc
    (∫ y in Set.Ioi (0 : ℝ), y ^ (-theta) * Real.exp (-y ^ 2)) =
        ∫ y in Set.Ioi (0 : ℝ),
          y ^ (-theta) * Real.exp (-y ^ (2 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      exact congrArg (fun t : ℝ => y ^ (-theta) * Real.exp (-t))
        (Real.rpow_two y).symm
    _ = (1 / (2 : ℝ)) * Real.Gamma ((-theta + 1) / 2) :=
      integral_rpow_mul_exp_neg_rpow
        (p := (2 : ℝ)) (q := -theta) (by norm_num) (by linarith)
    _ = (1 / 2 : ℝ) * Real.Gamma ((1 - theta) / 2) := by
      congr 2
      ring

theorem intervalIntegral_selbergGaussian_zero_le
    {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ ∫ y in 0..a, Real.exp (-y ^ 2) := by
  exact intervalIntegral.integral_nonneg ha fun y _ => (Real.exp_pos _).le

theorem intervalIntegral_selbergGaussian_le_length
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ y in 0..a, Real.exp (-y ^ 2)) ≤ a := by
  have hgauss : IntervalIntegrable (fun y : ℝ => Real.exp (-y ^ 2))
      volume 0 a :=
    (by fun_prop : Continuous (fun y : ℝ => Real.exp (-y ^ 2)))
      |>.intervalIntegrable 0 a
  have hone : IntervalIntegrable (fun _y : ℝ => (1 : ℝ)) volume 0 a :=
    intervalIntegrable_const
  calc
    (∫ y in 0..a, Real.exp (-y ^ 2)) ≤ ∫ _y : ℝ in 0..a, 1 := by
      apply intervalIntegral.integral_mono_on ha hgauss hone
      intro y _hy
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))
    _ = a := by simp

theorem intervalIntegrable_selbergWeightedGaussian
    {theta a : ℝ} (htheta1 : theta < 1) :
    IntervalIntegrable (selbergWeightedGaussian theta) volume 0 a := by
  have hpow : IntervalIntegrable (fun y : ℝ => y ^ (-theta)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hexp : ContinuousOn (fun y : ℝ => Real.exp (-y ^ 2))
      (Set.uIcc 0 a) := by fun_prop
  exact (hpow.continuousOn_mul hexp).congr fun y _hy => by
    unfold selbergWeightedGaussian
    ring

theorem intervalIntegral_selbergWeightedGaussian_zero_le
    {theta a : ℝ} (ha : 0 ≤ a) :
    0 ≤ ∫ y in 0..a, selbergWeightedGaussian theta y := by
  apply intervalIntegral.integral_nonneg ha
  intro y hy
  unfold selbergWeightedGaussian
  exact mul_nonneg (Real.rpow_nonneg hy.1 _) (Real.exp_pos _).le

theorem intervalIntegral_selbergWeightedGaussian_le_rpow
    {theta a : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta < 1)
    (ha : 0 ≤ a) :
    (∫ y in 0..a, selbergWeightedGaussian theta y) ≤
      a ^ (1 - theta) / (1 - theta) := by
  have hweighted := intervalIntegrable_selbergWeightedGaussian
    (theta := theta) (a := a) htheta1
  have hpow : IntervalIntegrable (fun y : ℝ => y ^ (-theta)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  calc
    (∫ y in 0..a, selbergWeightedGaussian theta y) ≤
        ∫ y in 0..a, y ^ (-theta) := by
      apply intervalIntegral.integral_mono_on ha hweighted hpow
      intro y hy
      unfold selbergWeightedGaussian
      have hyrpow : 0 ≤ y ^ (-theta) := Real.rpow_nonneg hy.1 _
      exact (mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg y))) hyrpow)
        |>.trans_eq (mul_one _)
    _ = a ^ (1 - theta) / (1 - theta) := by
      rw [integral_rpow (Or.inl (by linarith : -1 < -theta))]
      have honeTheta : 0 < 1 - theta := by linarith
      have hexpEq : -theta + 1 = 1 - theta := by ring
      rw [hexpEq, Real.zero_rpow honeTheta.ne']
      ring

noncomputable def selbergDiagonalK1 (theta : ℝ) : ℝ :=
  selbergEulerPowerConstant theta *
    ((1 / 2 : ℝ) * Real.Gamma ((1 - theta) / 2))

theorem selbergDiagonalK1_signed_identity
    {theta eta : ℝ} (htheta1 : theta < 1) :
    (selbergEulerPowerConstant theta / theta) *
        eta ^ ((theta - 1) / 2) *
          (∫ y in Set.Ioi (0 : ℝ), selbergWeightedGaussian theta y) =
      (selbergDiagonalK1 theta / theta) *
        eta ^ ((theta - 1) / 2) := by
  rw [integral_selbergWeightedGaussian_Ioi htheta1]
  unfold selbergDiagonalK1
  ring

theorem abs_selbergDiagonalK1_le
    {theta : ℝ} (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2) :
    |selbergDiagonalK1 theta| ≤
      (1 / 2 : ℝ) * Real.Gamma (1 / 4) := by
  let s : ℝ := (1 - theta) / 2
  have hsMem : s ∈ Set.Ioc (0 : ℝ) 1 := by
    dsimp [s]
    constructor <;> linarith
  have hquarterMem : (1 / 4 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by norm_num
  have hquarterLe : (1 / 4 : ℝ) ≤ s := by
    dsimp [s]
    linarith
  have hGamma := Real.Gamma_strictAntiOn_Ioc.antitoneOn
    hquarterMem hsMem hquarterLe
  have hs0 : 0 < s := hsMem.1
  have hGamma0 : 0 ≤ Real.Gamma s := (Real.Gamma_pos_of_pos hs0).le
  have hquarterGamma0 : 0 ≤ Real.Gamma (1 / 4) :=
    (Real.Gamma_pos_of_pos (by norm_num)).le
  unfold selbergDiagonalK1
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    abs_of_nonneg hGamma0]
  calc
    |selbergEulerPowerConstant theta| *
        (1 / 2 * Real.Gamma s) ≤ 1 * (1 / 2 * Real.Gamma (1 / 4)) := by
      gcongr
      exact abs_selbergEulerPowerConstant_le_one htheta0 hthetaHalf
    _ = (1 / 2 : ℝ) * Real.Gamma (1 / 4) := one_mul _

end HardyTheorem
