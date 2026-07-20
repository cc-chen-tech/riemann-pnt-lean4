import PrimeNumberTheorem.SincSquareIntegral
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion

open Convolution ContinuousLinearMap FourierTransform MeasureTheory Set

namespace PrimeNumberTheorem
namespace SincSquareFourier

/-- The convolution theorem for complex-valued integrable functions on the
real line.  Mathlib's current pointwise theorem assumes continuity of both
factors; for Fourier integrals, absolute integrability is enough. -/
theorem fourier_mul_convolution_eq_of_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (xi : ℝ) :
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) xi =
      𝓕 f xi * 𝓕 g xi := by
  have hkernel : Integrable (fun p : ℝ × ℝ =>
      𝐞 (-(p.1 * xi)) •
        (ContinuousLinearMap.mul ℂ ℂ) (f (p.1 - p.2)) (g p.2))
      (volume.prod volume) := by
    have hbase := hg.convolution_integrand
      (ContinuousLinearMap.mul ℂ ℂ).flip hf
    apply hbase.bdd_mul (by fun_prop) (c := 1)
    filter_upwards with p
    simp
  calc
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) xi =
        𝓕 (g ⋆[(ContinuousLinearMap.mul ℂ ℂ).flip] f) xi := by
      rw [convolution_flip]
    _ =
        ∫ x, 𝐞 (-(x * xi)) • ∫ y,
          (ContinuousLinearMap.mul ℂ ℂ) (f (x - y)) (g y) := by
      rw [Real.fourier_real_eq]
      rfl
    _ = ∫ x, ∫ y, 𝐞 (-(x * xi)) •
          (ContinuousLinearMap.mul ℂ ℂ) (f (x - y)) (g y) := by
      simp_rw [Circle.smul_def, MeasureTheory.integral_smul]
    _ = ∫ y, ∫ x, 𝐞 (-(x * xi)) •
          (ContinuousLinearMap.mul ℂ ℂ) (f (x - y)) (g y) := by
      exact integral_integral_swap hkernel
    _ = ∫ y, ∫ x, 𝐞 (-((y + x) * xi)) •
          (ContinuousLinearMap.mul ℂ ℂ) (f x) (g y) := by
      congr with y
      convert integral_sub_right_eq_self _ y (μ := volume)
      congr
      simp
    _ = ∫ y, ∫ x, 𝐞 (-(y * xi)) • 𝐞 (-(x * xi)) •
          (ContinuousLinearMap.mul ℂ ℂ) (f x) (g y) := by
      congr
      ext y
      congr
      ext x
      rw [smul_smul, ← AddChar.map_add_eq_mul]
      congr
      ring
    _ = ∫ y,
        (ContinuousLinearMap.mul ℂ ℂ)
          (∫ x, 𝐞 (-(x * xi)) • f x)
          (𝐞 (-(y * xi)) • g y) := by
      congr with y
      have heq : (fun x => 𝐞 (-(y * xi)) • 𝐞 (-(x * xi)) •
          (ContinuousLinearMap.mul ℂ ℂ) (f x) (g y)) =
          fun x => (𝐞 (-(x * xi)) • f x) *
            (𝐞 (-(y * xi)) • g y) := by
        funext x
        simp only [ContinuousLinearMap.mul_apply', Circle.smul_def, smul_eq_mul]
        ring
      rw [heq]
      simpa only [ContinuousLinearMap.mul_apply] using
        (MeasureTheory.integral_mul_const (μ := volume)
          (𝐞 (-(y * xi)) • g y)
          (fun x => 𝐞 (-(x * xi)) • f x))
    _ = (ContinuousLinearMap.mul ℂ ℂ)
        (∫ x, 𝐞 (-(x * xi)) • f x)
        (∫ y, 𝐞 (-(y * xi)) • g y) := by
      change (∫ y, (∫ x, 𝐞 (-(x * xi)) • f x) *
        (𝐞 (-(y * xi)) • g y)) = _
      simpa only [ContinuousLinearMap.mul_apply] using
        (MeasureTheory.integral_const_mul
          (∫ x, 𝐞 (-(x * xi)) • f x)
          (fun y => 𝐞 (-(y * xi)) • g y))
    _ = 𝓕 f xi * 𝓕 g xi := by
      rw [Real.fourier_real_eq, Real.fourier_real_eq]
      rfl

/-- The triangular pulse supported on `[-1, 1]`. -/
noncomputable def triangularPulse (x : ℝ) : ℂ :=
  (max (1 - |x|) 0 : ℝ)

theorem continuous_triangularPulse : Continuous triangularPulse := by
  unfold triangularPulse
  fun_prop

private theorem centeredIndicator_convolution_integrand (x : ℝ) :
    (fun t => (ContinuousLinearMap.mul ℂ ℂ)
      (SincSquareIntegral.centeredUnitIntervalIndicator t)
      (SincSquareIntegral.centeredUnitIntervalIndicator (x - t))) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2) ∩
        Icc (x - 1 / 2) (x + 1 / 2)).indicator (fun _ => (1 : ℂ)) := by
  funext t
  have hshift : x - t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ↔
      t ∈ Icc (x - 1 / 2) (x + 1 / 2) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hboth : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧
      x - t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · have hrhs : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∩
        Icc (x - 1 / 2) (x + 1 / 2) :=
      ⟨hboth.1, hshift.mp hboth.2⟩
    rw [SincSquareIntegral.centeredUnitIntervalIndicator,
      indicator_of_mem hboth.1,
      SincSquareIntegral.centeredUnitIntervalIndicator,
      indicator_of_mem hboth.2,
      ContinuousLinearMap.mul_apply', one_mul,
      indicator_of_mem hrhs]
  · have hrhs : t ∉ Icc (-(1 / 2 : ℝ)) (1 / 2) ∩
        Icc (x - 1 / 2) (x + 1 / 2) := by
      intro h
      exact hboth ⟨h.1, hshift.mpr h.2⟩
    rcases not_and_or.mp hboth with ht | hs
    · rw [SincSquareIntegral.centeredUnitIntervalIndicator,
        Set.indicator_of_notMem ht, ContinuousLinearMap.mul_apply',
        zero_mul, Set.indicator_of_notMem hrhs]
    · rw [SincSquareIntegral.centeredUnitIntervalIndicator,
        SincSquareIntegral.centeredUnitIntervalIndicator,
        Set.indicator_of_notMem hs, ContinuousLinearMap.mul_apply',
        mul_zero, Set.indicator_of_notMem hrhs]

private theorem overlapVolume_eq_triangularPulse (x : ℝ) :
    (volume (Icc (-(1 / 2 : ℝ)) (1 / 2) ∩
      Icc (x - 1 / 2) (x + 1 / 2))).toReal =
      max (1 - |x|) 0 := by
  rw [Icc_inter_Icc, Real.volume_Icc]
  change (ENNReal.ofReal
      (min (1 / 2 : ℝ) (x + 1 / 2) -
        max (-(1 / 2 : ℝ)) (x - 1 / 2))).toReal =
    max (1 - |x|) 0
  by_cases hxneg : x ≤ -1
  · have hx0 : x ≤ 0 := by linarith
    rw [max_eq_left (by linarith), min_eq_right (by linarith),
      abs_of_nonpos hx0, max_eq_right (by linarith)]
    rw [ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero]
  · have hxm1 : -1 < x := lt_of_not_ge hxneg
    by_cases hx0 : x ≤ 0
    · rw [max_eq_left (by linarith), min_eq_right (by linarith),
        abs_of_nonpos hx0, max_eq_left (by linarith)]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring
    · have hx0' : 0 < x := lt_of_not_ge hx0
      by_cases hx1 : x ≤ 1
      · rw [max_eq_right (by linarith), min_eq_left (by linarith),
          abs_of_pos hx0', max_eq_left (by linarith)]
        rw [ENNReal.toReal_ofReal (by linarith)]
        ring
      · have hx1' : 1 < x := lt_of_not_ge hx1
        rw [max_eq_right (by linarith), min_eq_left (by linarith),
          abs_of_pos hx0', max_eq_right (by linarith)]
        rw [ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero]

/-- The self-convolution of the centered unit interval is the triangular
pulse. -/
theorem centeredUnitIntervalIndicator_convolution_self (x : ℝ) :
    (SincSquareIntegral.centeredUnitIntervalIndicator ⋆[
      ContinuousLinearMap.mul ℂ ℂ]
      SincSquareIntegral.centeredUnitIntervalIndicator) x =
      triangularPulse x := by
  rw [convolution_def, centeredIndicator_convolution_integrand]
  rw [integral_indicator
    (measurableSet_Icc.inter measurableSet_Icc)]
  rw [integral_const]
  rw [measureReal_restrict_apply_univ]
  simp only [Measure.real]
  rw [overlapVolume_eq_triangularPulse]
  change ((max (1 - |x|) 0 : ℝ) : ℂ) * 1 = _
  simp [triangularPulse]

theorem integrable_complex_sinc_pi_sq :
    Integrable (fun x : ℝ => (Real.sinc (Real.pi * x) ^ 2 : ℂ)) := by
  have hreal : Integrable (fun x : ℝ =>
      Real.sinc (Real.pi * x) ^ 2) :=
    (integrable_comp_mul_left_iff
      (fun x : ℝ => Real.sinc x ^ 2) Real.pi_ne_zero).2
      SincSquareIntegral.integrable_sinc_sq
  have hc : Integrable (fun x : ℝ =>
      Complex.ofReal (Real.sinc (Real.pi * x) ^ 2)) volume :=
    hreal.ofReal
  simpa using hc

/-- The Fourier transform of normalized sinc square is the triangular pulse.
In particular, it vanishes outside `[-1, 1]`. -/
theorem fourier_sinc_pi_mul_sq (xi : ℝ) :
    𝓕 (fun x : ℝ => (Real.sinc (Real.pi * x) ^ 2 : ℂ)) xi =
      (max (1 - |xi|) 0 : ℝ) := by
  let g := SincSquareIntegral.centeredUnitIntervalIndicator
  let h := g ⋆[ContinuousLinearMap.mul ℂ ℂ] g
  have hg : Integrable g :=
    memLp_one_iff_integrable.mp
      SincSquareIntegral.centeredUnitIntervalIndicator_memLp_one
  have hh : Integrable h :=
    hg.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  have hhEq : h = triangularPulse := by
    funext x
    exact centeredUnitIntervalIndicator_convolution_self x
  have hfourierEq : 𝓕 h =
      fun x : ℝ => (Real.sinc (Real.pi * x) ^ 2 : ℂ) := by
    funext x
    rw [fourier_mul_convolution_eq_of_integrable hg hg,
      SincSquareIntegral.fourier_centeredUnitIntervalIndicator]
    ring
  have hfourierInt : Integrable (𝓕 h) := by
    rw [hfourierEq]
    exact integrable_complex_sinc_pi_sq
  have hinv := hh.fourierInv_fourier_eq hfourierInt
    ((continuous_triangularPulse.congr (congrFun hhEq.symm)).continuousAt :
      ContinuousAt h (-xi))
  rw [hfourierEq, Real.fourierInv_eq_fourier_neg, hhEq] at hinv
  simpa [triangularPulse] using hinv

theorem fourier_sinc_pi_add_one_sq (xi : ℝ) :
    𝓕 (fun x : ℝ =>
      (Real.sinc (Real.pi * (x + 1)) ^ 2 : ℂ)) xi =
      Complex.exp ((2 * Real.pi * xi : ℝ) * Complex.I) *
        (max (1 - |xi|) 0 : ℝ) := by
  let f : ℝ → ℂ := fun x => Real.sinc (Real.pi * x) ^ 2
  have htranslate := congrFun
    (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume f 1) xi
  have hscalar (u : ℝ → ℂ) (w : ℝ) :
      Fourier.fourierIntegral Real.fourierChar volume u w = 𝓕 u w := by
    rw [Fourier.fourierIntegral_def, Real.fourier_real_eq]
  rw [hscalar, hscalar] at htranslate
  rw [fourier_sinc_pi_mul_sq] at htranslate
  simpa only [f, Function.comp_apply, one_mul, Real.fourierChar_apply,
    Circle.smul_def, smul_eq_mul] using htranslate

theorem fourier_sinc_pi_add_one_sq_eq_zero
    {xi : ℝ} (hxi : 1 ≤ |xi|) :
    𝓕 (fun x : ℝ =>
      (Real.sinc (Real.pi * (x + 1)) ^ 2 : ℂ)) xi = 0 := by
  rw [fourier_sinc_pi_add_one_sq]
  have hmax : max (1 - |xi|) 0 = 0 := max_eq_right (by linarith)
  rw [hmax]
  simp

end SincSquareFourier
end PrimeNumberTheorem
