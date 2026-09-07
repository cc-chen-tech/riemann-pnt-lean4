import PrimeNumberTheorem.MWKFCubicAFEDyadicBoundary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex MeasureTheory Set

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Actual finite-height physical decay

The envelope is obtained from the literal finite vertical integral, not an
assumed majorant. Constants depend on the fixed physical parameters; this
module does not assert an asymptotic estimate uniform in T or V.
-/

theorem cubicAFEWeightEnvelope_nonneg (X V t : ℝ) :
    0 ≤ cubicAFEWeightEnvelope X V t := by
  unfold cubicAFEWeightEnvelope
  positivity

theorem norm_cubicAFERealProductWeightFinite_le_envelope
    (t X V : ℝ) {P : ℝ} (hP : 0 < P) :
    ‖cubicAFERealProductWeightFinite t X V P‖ ≤
      cubicAFEWeightEnvelope X V t * P ^ (-X) := by
  have hnorm (y : ℝ) :
      ‖Complex.exp (-cubicAFEVerticalPoint X y * (Real.log P : ℂ))‖ = P ^ (-X) := by
    rw [Complex.norm_exp, Real.rpow_def_of_pos hP]
    congr 1
    simp [cubicAFEVerticalPoint, Complex.mul_re, mul_comm]
  have hi := intervalIntegral.norm_integral_le_abs_integral_norm
    (f := fun y : ℝ ↦ cubicAFEScalar t (cubicAFEVerticalPoint X y) *
      Complex.exp (-cubicAFEVerticalPoint X y * (Real.log P : ℂ)))
    (a := -V) (b := V) (μ := volume)
  simp_rw [norm_mul, hnorm] at hi
  rw [intervalIntegral.integral_mul_const, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hP.le _)] at hi
  calc
    _ = ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖∫ y : ℝ in -V..V,
        cubicAFEScalar t (cubicAFEVerticalPoint X y) *
          Complex.exp (-cubicAFEVerticalPoint X y * (Real.log P : ℂ))‖ := norm_mul _ _
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
        (|∫ y : ℝ in -V..V, ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖| *
          P ^ (-X)) := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = _ := by unfold cubicAFEWeightEnvelope; ring

noncomputable def cubicAFEPhysicalTimeEnvelope
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (t : ℝ) : ℝ :=
  ‖(cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2‖ *
    (Real.sqrt (d * e))⁻¹ * cubicAFEWeightEnvelope X V t * ‖W (t / T)‖

theorem cubicAFEPhysicalTimeEnvelope_nonneg
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (t : ℝ) :
    0 ≤ cubicAFEPhysicalTimeEnvelope W T X V d e t := by
  unfold cubicAFEPhysicalTimeEnvelope
  exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))) (cubicAFEWeightEnvelope_nonneg X V t))
      (norm_nonneg _)

theorem integrable_cubicAFEPhysicalTimeEnvelope
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) : Integrable (cubicAFEPhysicalTimeEnvelope W T X V d e) := by
  have hc : Continuous (cubicAFEPhysicalTimeEnvelope W T X V d e) :=
    (continuous_const.mul (continuous_cubicAFEWeightEnvelope hX V)).mul
      (W.continuous.comp (continuous_id.div_const T)).norm
  exact hc.integrable_of_hasCompactSupport (W.hasCompactSupport_dilate hT).norm.mul_left

theorem norm_cubicAFEProgressionPhysicalSummand_le_envelope
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (δ : ℤ) (t : ℝ) {x : ℝ}
    (hP : 0 < cubicAFEProgressionRealProduct d e δ x) :
    ‖cubicAFEProgressionPhysicalSummand W T X V d e δ t x‖ ≤
      cubicAFEPhysicalTimeEnvelope W T X V d e t *
        (cubicAFEProgressionRealProduct d e δ x) ^ (-X - 1 / 2) := by
  let P := cubicAFEProgressionRealProduct d e δ x
  have hpw := norm_cubicAFERealProductWeightFinite_le_envelope t X V hP
  have hphase (u : ℝ) : ‖Complex.exp ((I * (u : ℂ)) * t)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hpow : (Real.sqrt P)⁻¹ * P ^ (-X) = P ^ (-X - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hP.le, ← Real.rpow_add hP]
    congr 1
    ring
  have hnorm : ‖cubicAFEProgressionPhysicalSummand W T X V d e δ t x‖ =
      ‖(cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2‖ *
        (((Real.sqrt P)⁻¹ * (Real.sqrt (d * e))⁻¹) *
          ‖cubicAFERealProductWeightFinite t X V P‖) * ‖W (t / T)‖ := by
    simp only [cubicAFEProgressionPhysicalSummand, norm_mul, norm_inv,
      hphase, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), P]
  rw [hnorm]
  calc
    _ ≤ ‖(cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2‖ *
        (((Real.sqrt P)⁻¹ * (Real.sqrt (d * e))⁻¹) *
          (cubicAFEWeightEnvelope X V t * P ^ (-X))) * ‖W (t / T)‖ := by
      gcongr
    _ = cubicAFEPhysicalTimeEnvelope W T X V d e t *
        ((Real.sqrt P)⁻¹ * P ^ (-X)) := by
      unfold cubicAFEPhysicalTimeEnvelope
      ring
    _ = _ := by rw [hpow]

/-- Integrable half-line majorant. The lower endpoint is strictly positive. -/
noncomputable def cubicAFEHalfLinePower (X x : ℝ) : ℝ :=
  (Ioi (1 / 2 : ℝ)).indicator (fun x : ℝ ↦ x ^ (-X - 1 / 2)) x

theorem cubicAFEHalfLinePower_nonneg (X x : ℝ) : 0 ≤ cubicAFEHalfLinePower X x := by
  unfold cubicAFEHalfLinePower
  by_cases hx : x ∈ Ioi (1 / 2 : ℝ)
  · rw [indicator_of_mem hx]
    exact Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _
  · rw [indicator_of_notMem hx]

theorem integrable_cubicAFEHalfLinePower {X : ℝ} (hX : 1 / 2 < X) :
    Integrable (cubicAFEHalfLinePower X) :=
  (integrableOn_Ioi_rpow_of_lt (by linarith : -X - 1 / 2 < -1)
    (by norm_num : (0 : ℝ) < 1 / 2)).integrable_indicator measurableSet_Ioi

theorem cubicAFEDyadicLowerWeight_mul_rpow_le (X x : ℝ) :
    cubicAFEDyadicLowerWeight x * x ^ (-X - 1 / 2) ≤ cubicAFEHalfLinePower X x := by
  by_cases hx : x ≤ 1 / 2
  · rw [cubicAFEDyadicLowerWeight_zero hx, zero_mul]
    exact cubicAFEHalfLinePower_nonneg X x
  · have hx' : (1 / 2 : ℝ) < x := lt_of_not_ge hx
    rw [cubicAFEHalfLinePower, indicator_of_mem (show x ∈ Ioi (1 / 2 : ℝ) from hx')]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _)
      (cubicAFEDyadicLowerWeight_le_one x)

end PrimeNumberTheorem.MWKFCubic
