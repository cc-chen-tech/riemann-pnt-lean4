import PrimeNumberTheorem.CarneiroLittmannNormalization
import Mathlib.Analysis.Fourier.Inversion

open Complex MeasureTheory Set
open FourierTransform

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- The compactly supported triangle kernel whose Fourier transform is the
square of the normalized sinc function. -/
noncomputable def triangleFourierKernel (x : ℝ) : ℝ :=
  max (1 - |x|) 0

theorem continuous_triangleFourierKernel :
    Continuous triangleFourierKernel := by
  exact (continuous_const.sub continuous_abs).max continuous_const

theorem triangleFourierKernel_nonneg (x : ℝ) :
    0 ≤ triangleFourierKernel x := by
  exact le_max_right _ _

theorem triangleFourierKernel_eq_zero_of_not_mem_Icc {x : ℝ}
    (hx : x ∉ Set.Icc (-1 : ℝ) 1) :
    triangleFourierKernel x = 0 := by
  have hAbs : 1 ≤ |x| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  rw [triangleFourierKernel, max_eq_right]
  linarith

theorem hasCompactSupport_triangleFourierKernel :
    HasCompactSupport triangleFourierKernel := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  exact triangleFourierKernel_eq_zero_of_not_mem_Icc hx

theorem integrable_triangleFourierKernel :
    Integrable triangleFourierKernel :=
  continuous_triangleFourierKernel.integrable_of_hasCompactSupport
    hasCompactSupport_triangleFourierKernel

@[simp] theorem triangleFourierKernel_zero :
    triangleFourierKernel 0 = 1 := by
  simp [triangleFourierKernel]

theorem integral_triangleFourierKernel :
    (∫ x : ℝ, triangleFourierKernel x) = 1 := by
  have hWhole :
      (∫ x : ℝ, triangleFourierKernel x) =
        ∫ x : ℝ in Set.Icc (-1 : ℝ) 1, triangleFourierKernel x := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · simp [hx]
    · simp [hx, triangleFourierKernel_eq_zero_of_not_mem_Icc hx]
  rw [hWhole, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_triangleFourierKernel.intervalIntegrable (-1) 0)
    (continuous_triangleFourierKernel.intervalIntegrable 0 1)]
  have hNeg :
      (∫ x : ℝ in (-1)..0, triangleFourierKernel x) =
        ∫ x : ℝ in (-1)..0, 1 + x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    rw [triangleFourierKernel, abs_of_nonpos hx.2, max_eq_left]
    · ring
    · linarith [hx.1]
  have hPos :
      (∫ x : ℝ in 0..1, triangleFourierKernel x) =
        ∫ x : ℝ in 0..1, 1 - x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [triangleFourierKernel, abs_of_nonneg hx.1,
      max_eq_left (sub_nonneg.mpr hx.2)]
  rw [hNeg, hPos]
  change (∫ x : ℝ in (-1)..0, (fun _ : ℝ => 1) x + id x) +
      (∫ x : ℝ in 0..1, (fun _ : ℝ => 1) x - id x) = 1
  rw [intervalIntegral.integral_add
      (continuous_const.intervalIntegrable (-1) 0)
      (continuous_id.intervalIntegrable (-1) 0),
    intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable 0 1)
      (continuous_id.intervalIntegrable 0 1)]
  simp only [id_eq, integral_one, integral_id]
  norm_num

private theorem intervalIntegral_affine_mul_cexp {a b c : ℂ}
    (hc : c ≠ 0) (u v : ℝ) :
    (∫ x in u..v, (a + b * x) * Complex.exp (c * x)) =
      Complex.exp (c * v) * ((a + b * v) / c - b / c ^ 2) -
        Complex.exp (c * u) * ((a + b * u) / c - b / c ^ 2) := by
  let P : ℝ → ℂ := fun x =>
    Complex.exp (c * x) * ((a + b * x) / c - b / c ^ 2)
  have hP : ∀ x : ℝ, HasDerivAt P
      ((a + b * x) * Complex.exp (c * x)) x := by
    intro x
    have hExp : HasDerivAt (fun y : ℝ => Complex.exp (c * y))
        (c * Complex.exp (c * x)) x := by
      convert ((Complex.hasDerivAt_exp (c * x)).comp x
        (((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal)) using 1
      all_goals ring
    have hAffine : HasDerivAt (fun y : ℝ => a + b * y) b x := by
      convert (((hasDerivAt_id (x : ℂ)).const_mul b).comp_ofReal.const_add a) using 1
      all_goals ring
    have hBracket : HasDerivAt
        (fun y : ℝ => (a + b * y) / c - b / c ^ 2) (b / c) x := by
      convert (hAffine.div_const c).sub_const (b / c ^ 2) using 1
    convert hExp.mul hBracket using 1
    all_goals
      dsimp [P]
      field_simp [hc]
      ring
  rw [intervalIntegral.integral_deriv_eq_sub' P (funext fun x => (hP x).deriv)
    (fun x _ => (hP x).differentiableAt)]
  fun_prop

/-- The Fourier transform of the compact triangle kernel is the square of
the normalized sinc function. -/
theorem fourier_triangleFourierKernel (xi : ℝ) :
    𝓕 (fun x : ℝ => (triangleFourierKernel x : ℂ)) xi =
      ((Real.sinc (Real.pi * xi) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  by_cases hxi : xi = 0
  · subst xi
    simp only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero,
      one_smul, Real.sinc_zero, one_pow, ofReal_one]
    norm_cast
    exact integral_triangleFourierKernel
  let c : ℂ := ((-2 * Real.pi * xi : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hxi)) Complex.I_ne_zero
  have hPhase (v : ℝ) :
      ((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I = c * v := by
    dsimp [c]
    push_cast
    ring
  have hWhole :
      (∫ v : ℝ, Complex.exp (((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I) •
          (triangleFourierKernel v : ℂ)) =
        ∫ v : ℝ in Set.Icc (-1 : ℝ) 1,
          Complex.exp (((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I) •
            (triangleFourierKernel v : ℂ) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v ∈ Set.Icc (-1 : ℝ) 1
    · simp [hv]
    · simp [hv, triangleFourierKernel_eq_zero_of_not_mem_Icc hv]
  rw [hWhole, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hCont : Continuous (fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I) •
        (triangleFourierKernel v : ℂ)) := by
    rw [show (fun v : ℝ =>
        Complex.exp (((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I) •
          (triangleFourierKernel v : ℂ)) =
        fun v : ℝ => Complex.exp (c * v) * (triangleFourierKernel v : ℂ) by
      funext v
      rw [hPhase]
      simp only [smul_eq_mul]]
    exact ((continuous_const.mul continuous_ofReal).cexp).mul
      (continuous_ofReal.comp continuous_triangleFourierKernel)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hCont.intervalIntegrable (-1) 0) (hCont.intervalIntegrable 0 1)]
  have hNeg :
      (∫ v : ℝ in (-1)..0,
          Complex.exp (((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I) •
            (triangleFourierKernel v : ℂ)) =
        ∫ v : ℝ in (-1)..0,
          ((1 : ℂ) + (1 : ℂ) * v) * Complex.exp (c * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
    change Complex.exp (((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I) •
        (triangleFourierKernel v : ℂ) =
      ((1 : ℂ) + (1 : ℂ) * v) * Complex.exp (c * v)
    rw [hPhase, triangleFourierKernel, abs_of_nonpos hv.2, max_eq_left]
    · simp only [smul_eq_mul]
      push_cast
      ring
    · linarith [hv.1]
  have hPos :
      (∫ v : ℝ in 0..1,
          Complex.exp (((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I) •
            (triangleFourierKernel v : ℂ)) =
        ∫ v : ℝ in 0..1,
          ((1 : ℂ) + (-1 : ℂ) * v) * Complex.exp (c * v) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    change Complex.exp (((-2 * Real.pi * v * xi : ℝ) : ℂ) * Complex.I) •
        (triangleFourierKernel v : ℂ) =
      ((1 : ℂ) + (-1 : ℂ) * v) * Complex.exp (c * v)
    rw [hPhase, triangleFourierKernel, abs_of_nonneg hv.1,
      max_eq_left (sub_nonneg.mpr hv.2)]
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [hNeg, hPos]
  rw [intervalIntegral_affine_mul_cexp (a := 1) (b := 1) hc (-1) 0,
    intervalIntegral_affine_mul_cexp (a := 1) (b := -1) hc 0 1]
  simp only [ofReal_zero, ofReal_one, ofReal_neg, mul_zero, mul_one,
    Complex.exp_zero, one_mul, add_zero]
  norm_num
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxi)]
  have hAlgebra :
      c⁻¹ - (c ^ 2)⁻¹ + Complex.exp (-c) * (c ^ 2)⁻¹ +
          (-(Complex.exp c * (-1 / c ^ 2)) - (c⁻¹ - -1 / c ^ 2)) =
        (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
    field_simp [hc]
    ring
  rw [hAlgebra]
  have hExpSum :
      Complex.exp c + Complex.exp (-c) =
        ((2 * Real.cos (2 * Real.pi * xi) : ℝ) : ℂ) := by
    dsimp [c]
    rw [show ((-2 * Real.pi * xi : ℝ) : ℂ) * Complex.I =
        (((-2 * Real.pi * xi : ℝ) : ℂ) * Complex.I) by rfl,
      Complex.exp_mul_I]
    rw [show -(((-2 * Real.pi * xi : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring,
      Complex.exp_mul_I]
    push_cast
    rw [show (-2 : ℂ) * Real.pi * xi = -(2 * Real.pi * xi) by ring]
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  have hcSq :
      c ^ 2 = ((-4 * (Real.pi * xi) ^ 2 : ℝ) : ℂ) := by
    dsimp [c]
    push_cast
    calc
      (-2 * (Real.pi : ℂ) * xi * Complex.I) ^ 2 =
          (-2 * (Real.pi : ℂ) * xi) ^ 2 * Complex.I ^ 2 := by ring
      _ = -4 * ((Real.pi : ℂ) * xi) ^ 2 := by
        rw [Complex.I_sq]
        ring
  rw [hExpSum, hcSq]
  norm_cast
  rw [show 2 * Real.pi * xi = 2 * (Real.pi * xi) by ring,
    Real.cos_two_mul_eq_one_sub]
  field_simp [Real.pi_ne_zero, hxi]
  norm_num
  ring

/-- Fourier inversion at zero gives the exact mass of the normalized
sinc-square kernel. -/
theorem integral_carneiroLittmannSincSquareBase_eq_one :
    (∫ x : ℝ, carneiroLittmannSincSquareBase x) = 1 := by
  let f : ℝ → ℂ := fun x => (triangleFourierKernel x : ℂ)
  have hf : MeasureTheory.Integrable f := by
    exact integrable_triangleFourierKernel.ofReal
  have hF : MeasureTheory.Integrable (𝓕 f) := by
    have hBase : MeasureTheory.Integrable
        (fun x : ℝ => (carneiroLittmannSincSquareBase x : ℂ)) :=
      integrable_carneiroLittmannSincSquareBase.ofReal
    have hFourierEq : 𝓕 f =
        fun x : ℝ => (carneiroLittmannSincSquareBase x : ℂ) := by
      funext x
      simpa only [f, carneiroLittmannSincSquareBase] using
        fourier_triangleFourierKernel x
    rw [hFourierEq]
    exact hBase
  have hInv := hf.fourierInv_fourier_eq hF
    ((continuous_ofReal.comp continuous_triangleFourierKernel).continuousAt :
      ContinuousAt f 0)
  rw [Real.fourierInv_eq'] at hInv
  simp only [inner_zero_right, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, f, triangleFourierKernel_zero, ofReal_one] at hInv
  simp_rw [fourier_triangleFourierKernel] at hInv
  change (∫ v : ℝ, (carneiroLittmannSincSquareBase v : ℂ)) = 1 at hInv
  norm_cast at hInv

/-- The Carneiro--Littmann derivative has the unit mass required by the
extremal majorant normalization. -/
theorem integral_carneiroLittmannDerivative_eq_one :
    (∫ x : ℝ, carneiroLittmannDerivative x) = 1 := by
  rw [integral_carneiroLittmannDerivative_eq_sincSquareBase,
    integral_carneiroLittmannSincSquareBase_eq_one]

end DirichletPolynomial
end PrimeNumberTheorem
