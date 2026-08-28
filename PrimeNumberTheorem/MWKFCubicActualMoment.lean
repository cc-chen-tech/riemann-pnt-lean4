import HardyTheorem.SelbergMollifier
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.ConstMulAction

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# The actual cubic mollified second moment

This module replaces the abstract function `I` in the reassembly layer by the
literal zeta/Mobius integral with `N = floor(T^3)`.  The test-weight structure
records smoothness and support in `[1,2]`.
-/

/-- A real smooth test weight supported in `[1,2]`. -/
structure CubicTestWeight where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ⊤ toFun
  support_subset : Function.support toFun ⊆ Icc (1 : ℝ) 2

instance : CoeFun CubicTestWeight (fun _ ↦ ℝ → ℝ) :=
  ⟨CubicTestWeight.toFun⟩

namespace CubicTestWeight

theorem continuous (W : CubicTestWeight) : Continuous W :=
  W.smooth.continuous

theorem hasCompactSupport (W : CubicTestWeight) : HasCompactSupport W := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    W.support_subset

end CubicTestWeight

/-- The exact integer cutoff `floor(T^3)`.  Natural floor is zero for negative
inputs; only the cofinal positive range is used in the asymptotic theorem. -/
noncomputable def cubicMollifierLength (T : ℝ) : ℕ :=
  ⌊T ^ 3⌋₊

theorem cubicMollifierLength_cast_le {T : ℝ} (hT : 0 ≤ T) :
    (cubicMollifierLength T : ℝ) ≤ T ^ 3 := by
  exact Nat.floor_le (pow_nonneg hT 3)

theorem cubicMollifierLength_pos {T : ℝ} (hT : 1 ≤ T) :
    0 < cubicMollifierLength T := by
  apply Nat.floor_pos.mpr
  simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hT 3)

/-- Literal integrand
`|zeta(1/2+it)|^2 |M_floor(T^3)(1/2+it)|^2 W(t/T)`. -/
noncomputable def cubicMomentIntegrand
    (W : CubicTestWeight) (T t : ℝ) : ℝ :=
  Complex.normSq (riemannZeta ((1 / 2 : ℂ) + I * t)) *
    Complex.normSq (HardyTheorem.selbergMoebiusMollifier
      (cubicMollifierLength T) ((1 / 2 : ℂ) + I * t)) *
    W (t / T)

/-- The actual full-real-axis cubic mollified second moment. -/
noncomputable def cubicMollifiedSecondMoment
    (W : CubicTestWeight) (T : ℝ) : ℝ :=
  ∫ t : ℝ, cubicMomentIntegrand W T t

/-- The zeta energy in the literal integrand is exactly `hardyZ(t)^2`. -/
theorem cubicMomentIntegrand_eq_hardy
    (W : CubicTestWeight) (T t : ℝ) :
    cubicMomentIntegrand W T t =
      HardyTheorem.hardyZ t ^ 2 *
        Complex.normSq (HardyTheorem.selbergMoebiusMollifier
          (cubicMollifierLength T) ((1 / 2 : ℂ) + I * t)) *
        W (t / T) := by
  unfold cubicMomentIntegrand
  have hzeta : HardyTheorem.hardyZ t ^ 2 =
      Complex.normSq (riemannZeta ((1 / 2 : ℂ) + I * t)) := by
    rw [← sq_abs, HardyTheorem.abs_hardyZ_eq_norm_riemannZeta,
      Complex.normSq_eq_norm_sq]
  rw [hzeta]

/-- For fixed nonzero scale, the literal integrand is continuous. -/
theorem continuous_cubicMomentIntegrand
    (W : CubicTestWeight) (T : ℝ) :
    Continuous (cubicMomentIntegrand W T) := by
  rw [show cubicMomentIntegrand W T = fun t ↦
      HardyTheorem.hardyZ t ^ 2 *
        Complex.normSq (HardyTheorem.selbergMoebiusMollifier
          (cubicMollifierLength T) ((1 / 2 : ℂ) + I * t)) *
        W (t / T) by
    funext t
    exact cubicMomentIntegrand_eq_hardy W T t]
  exact ((HardyTheorem.hardyZ_continuous.pow 2).mul
    (Complex.continuous_normSq.comp
      (HardyTheorem.continuous_selbergMollifier_criticalLine
        (cubicMollifierLength T)
        (fun n ↦ (HardyTheorem.selbergMoebiusCoeff
          (cubicMollifierLength T) n : ℂ))))).mul
    (W.continuous.comp (continuous_id.div_const T))

/-- The test weight supplies compact support after the nonzero dilation. -/
theorem hasCompactSupport_cubicMomentIntegrand
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) :
    HasCompactSupport (cubicMomentIntegrand W T) := by
  have hscaled : HasCompactSupport (fun t : ℝ ↦ W (t / T)) := by
    have h := W.hasCompactSupport.comp_smul (c := T⁻¹) (inv_ne_zero hT)
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using h
  unfold cubicMomentIntegrand
  exact hscaled.mul_left

/-- The full-real-axis integral defining the actual cubic moment is genuine
(not the default value of a nonintegrable Bochner integral). -/
theorem integrable_cubicMomentIntegrand
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) :
    Integrable (cubicMomentIntegrand W T) :=
  (continuous_cubicMomentIntegrand W T).integrable_of_hasCompactSupport
    (hasCompactSupport_cubicMomentIntegrand W hT)

end MWKFCubic
end PrimeNumberTheorem
