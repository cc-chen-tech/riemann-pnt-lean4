import HardyTheorem.SelbergDiagonalLogTail

open Real

namespace HardyTheorem

/-! # Pointwise Euler decomposition of Selberg's diagonal kernel. -/

noncomputable def selbergDiagonalFloorKernelIntegrand
    (eta x theta y : ℝ) : ℝ :=
  eta ^ ((theta - 1) / 2) * selbergWeightedGaussian theta y *
    selbergEulerFloorPowerSum theta (y / (x * Real.sqrt eta))

noncomputable def selbergDiagonalEulerMainIntegrand
    (eta x theta y : ℝ) : ℝ :=
  eta ^ ((theta - 1) / 2) * selbergWeightedGaussian theta y *
    ((y / (x * Real.sqrt eta)) ^ theta / theta)

noncomputable def selbergDiagonalEulerConstantIntegrand
    (eta _x theta y : ℝ) : ℝ :=
  eta ^ ((theta - 1) / 2) * selbergWeightedGaussian theta y *
    (selbergEulerPowerConstant theta / theta)

noncomputable def selbergDiagonalEulerErrorIntegrand
    (eta x theta y : ℝ) : ℝ :=
  eta ^ ((theta - 1) / 2) * selbergWeightedGaussian theta y *
    selbergEulerFloorError theta (y / (x * Real.sqrt eta))

theorem selbergDiagonalFloorKernelIntegrand_decomposition
    {eta x theta y : ℝ} :
    selbergDiagonalFloorKernelIntegrand eta x theta y =
      selbergDiagonalEulerMainIntegrand eta x theta y +
        selbergDiagonalEulerConstantIntegrand eta x theta y +
          selbergDiagonalEulerErrorIntegrand eta x theta y := by
  unfold selbergDiagonalFloorKernelIntegrand
  unfold selbergDiagonalEulerMainIntegrand
  unfold selbergDiagonalEulerConstantIntegrand
  unfold selbergDiagonalEulerErrorIntegrand
  rw [selbergEulerFloorPowerSum_eq_main_add_error]
  ring

theorem selberg_rpow_floor_error_algebra
    {a y theta : ℝ} (ha : 0 < a) (hy : 0 < y) :
    y ^ (-theta) * (y / a) ^ (theta - 1) =
      a ^ (1 - theta) / y := by
  rw [Real.div_rpow hy.le ha.le]
  have hexpY : -theta + (theta - 1) = (-1 : ℝ) := by ring
  have hexpA : 1 - theta = -(theta - 1) := by ring
  calc
    y ^ (-theta) * (y ^ (theta - 1) / a ^ (theta - 1)) =
        (y ^ (-theta) * y ^ (theta - 1)) / a ^ (theta - 1) := by ring
    _ = y ^ (-1 : ℝ) / a ^ (theta - 1) := by
      rw [← Real.rpow_add hy, hexpY]
    _ = a ^ (1 - theta) / y := by
      rw [hexpA, Real.rpow_neg ha.le, Real.rpow_neg_one]
      field_simp [ha.ne', hy.ne', Real.rpow_ne_zero ha.le]

theorem selbergEtaSqrtCancellation
    {eta x theta : ℝ} (heta : 0 < eta) (hx : 0 < x) :
    eta ^ ((theta - 1) / 2) *
        (x * Real.sqrt eta) ^ (1 - theta) =
      x ^ (1 - theta) := by
  have hsqrt0 : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  rw [Real.mul_rpow hx.le hsqrt0.le]
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul heta.le]
  have hexp : (1 / 2 : ℝ) * (1 - theta) + (theta - 1) / 2 = 0 := by ring
  calc
    eta ^ ((theta - 1) / 2) *
        (x ^ (1 - theta) * eta ^ (1 / 2 * (1 - theta))) =
        x ^ (1 - theta) *
          (eta ^ (1 / 2 * (1 - theta)) * eta ^ ((theta - 1) / 2)) := by ring
    _ = x ^ (1 - theta) *
        eta ^ ((1 / 2 : ℝ) * (1 - theta) + (theta - 1) / 2) := by
      rw [Real.rpow_add heta]
    _ = x ^ (1 - theta) := by rw [hexp, Real.rpow_zero, mul_one]

theorem abs_selbergDiagonalEulerErrorIntegrand_le
    {eta x theta y : ℝ} (heta : 0 < eta) (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (hy : x * Real.sqrt eta ≤ y) :
    |selbergDiagonalEulerErrorIntegrand eta x theta y| ≤
      x ^ (1 - theta) * selbergDiagonalLogTail y := by
  have hsqrt0 : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  have ha : 0 < x * Real.sqrt eta := mul_pos hx hsqrt0
  have hy0 : 0 < y := ha.trans_le hy
  have hz : 1 ≤ y / (x * Real.sqrt eta) :=
    (le_div_iff₀ ha).2 (by simpa [one_mul] using hy)
  have herror := abs_selbergEulerFloorError_le htheta0 hthetaHalf hz
  have hscale0 : 0 ≤ eta ^ ((theta - 1) / 2) := Real.rpow_nonneg heta.le _
  have hweighted0 : 0 ≤ selbergWeightedGaussian theta y := by
    unfold selbergWeightedGaussian
    positivity
  calc
    |selbergDiagonalEulerErrorIntegrand eta x theta y| =
        (eta ^ ((theta - 1) / 2) * selbergWeightedGaussian theta y) *
          |selbergEulerFloorError theta (y / (x * Real.sqrt eta))| := by
      unfold selbergDiagonalEulerErrorIntegrand
      rw [abs_mul, abs_mul, abs_of_nonneg hscale0, abs_of_nonneg hweighted0]
    _ ≤ (eta ^ ((theta - 1) / 2) * selbergWeightedGaussian theta y) *
        (y / (x * Real.sqrt eta)) ^ (theta - 1) := by
      exact mul_le_mul_of_nonneg_left herror (mul_nonneg hscale0 hweighted0)
    _ = (eta ^ ((theta - 1) / 2) *
          (x * Real.sqrt eta) ^ (1 - theta)) *
        selbergDiagonalLogTail y := by
      unfold selbergWeightedGaussian selbergDiagonalLogTail
      have halgebra := selberg_rpow_floor_error_algebra
        (theta := theta) ha hy0
      calc
        eta ^ ((theta - 1) / 2) * (y ^ (-theta) * Real.exp (-y ^ 2)) *
            (y / (x * Real.sqrt eta)) ^ (theta - 1) =
            eta ^ ((theta - 1) / 2) *
              (y ^ (-theta) *
                (y / (x * Real.sqrt eta)) ^ (theta - 1)) *
                  Real.exp (-y ^ 2) := by ring
        _ = eta ^ ((theta - 1) / 2) *
            ((x * Real.sqrt eta) ^ (1 - theta) / y) *
              Real.exp (-y ^ 2) := by rw [halgebra]
        _ = (eta ^ ((theta - 1) / 2) *
              (x * Real.sqrt eta) ^ (1 - theta)) *
            (Real.exp (-y ^ 2) / y) := by ring
    _ = x ^ (1 - theta) * selbergDiagonalLogTail y := by
      rw [selbergEtaSqrtCancellation heta hx]

end HardyTheorem
