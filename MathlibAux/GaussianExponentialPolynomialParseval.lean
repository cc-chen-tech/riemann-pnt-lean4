import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import MathlibAux.DirichletPolynomialMeanSquare
import MathlibAux.DyadicDriftingGaussianSchur

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace MathlibAux

noncomputable def gaussianFourierDensity (m y : ℝ) : ℝ :=
  Real.exp (-y ^ 2 / (4 * m)) / (2 * Real.sqrt (Real.pi * m))

noncomputable def frozenDriftingExponentialPolynomial {ι : Type*}
    (S : Finset ι) (coeff : ι → ℂ) (drift freq : ι → ℝ) (t y : ℝ) : ℂ :=
  ∑ i ∈ S, coeff i * Real.exp (drift i * t) *
    Complex.exp (Complex.I * ((freq i : ℂ) * (y : ℂ)))

noncomputable def gaussianWeightedSecondMoment {ι : Type*}
    (S : Finset ι) (coeff : ι → ℂ) (drift freq : ι → ℝ) (t m : ℝ) : ℝ :=
  ∫ y : ℝ, gaussianFourierDensity m y *
    Complex.normSq (frozenDriftingExponentialPolynomial S coeff drift freq t y)

private theorem integral_gaussianFourierDensity_mul_cexp
    {m : ℝ} (hm : 0 < m) (omega : ℝ) :
    (∫ y : ℝ, (gaussianFourierDensity m y : ℂ) *
      Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))) =
      Complex.exp (-(m : ℂ) * (omega : ℂ) ^ 2) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  let b : ℝ := 1 / (4 * m)
  let D : ℝ := 2 * Real.sqrt (Real.pi * m)
  have hbReal : 0 < b := by dsimp [b]; positivity
  have hb : 0 < (b : ℂ).re := by simpa using hbReal
  have hfourier := fourierIntegral_gaussian hb (omega : ℂ)
  have hsqrt : ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) = (D : ℂ) := by
    calc
      ((Real.pi : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) =
          (((Real.pi / b) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
            rw [← Complex.ofReal_div]
            exact (by convert (Complex.ofReal_cpow (x := Real.pi / b) (by positivity)
              (1 / 2 : ℝ)).symm using 1 <;> norm_num)
      _ = (Real.sqrt (Real.pi / b) : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ = (D : ℂ) := by
        norm_cast
        dsimp [b, D]
        rw [show Real.pi / (1 / (4 * m)) = 4 * (Real.pi * m) by field_simp]
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
        have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
          norm_num
        rw [hsqrt4]
  have hexponent : -((omega : ℂ) ^ 2) / (4 * (b : ℂ)) =
      -(m : ℂ) * (omega : ℂ) ^ 2 := by
    dsimp [b]
    push_cast
    field_simp
  rw [hsqrt, hexponent] at hfourier
  have hD : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr <|
    mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr (mul_pos Real.pi_pos hm))
  have hpoint :
      (fun y : ℝ => (gaussianFourierDensity m y : ℂ) *
        Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))) =
      (fun y : ℝ => (D : ℂ)⁻¹ *
        (Complex.exp (Complex.I * (omega : ℂ) * (y : ℂ)) *
          Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2))) := by
    funext y
    have hgauss : (Real.exp (-y ^ 2 / (4 * m)) : ℂ) =
        Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2) := by
      rw [Complex.ofReal_exp]
      congr 1
      dsimp [b]
      push_cast
      field_simp
    rw [gaussianFourierDensity, Complex.ofReal_div, hgauss]
    dsimp [D]
    ring
  rw [hpoint]
  calc
    (∫ y : ℝ, (D : ℂ)⁻¹ *
        (Complex.exp (Complex.I * (omega : ℂ) * (y : ℂ)) *
          Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2))) =
      (D : ℂ)⁻¹ * (∫ y : ℝ,
        Complex.exp (Complex.I * (omega : ℂ) * (y : ℂ)) *
          Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2)) := by
        exact integral_const_mul _ _
    _ = (D : ℂ)⁻¹ * ((D : ℂ) *
        Complex.exp (-(m : ℂ) * (omega : ℂ) ^ 2)) := by rw [hfourier]
    _ = Complex.exp (-(m : ℂ) * (omega : ℂ) ^ 2) := by field_simp

private theorem integrable_gaussianFourierDensity
    {m : ℝ} (hm : 0 < m) : Integrable (gaussianFourierDensity m) := by
  have hb : 0 < 1 / (4 * m) := by positivity
  have h := (integrable_exp_neg_mul_sq hb).div_const
    (2 * Real.sqrt (Real.pi * m))
  convert h using 1
  funext y
  rw [gaussianFourierDensity]
  congr 2
  field_simp

private theorem integrable_gaussianFourierDensity_mul_cexp
    {m : ℝ} (hm : 0 < m) (omega : ℝ) :
    Integrable (fun y : ℝ => (gaussianFourierDensity m y : ℂ) *
      Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))) := by
  have hgReal := integrable_gaussianFourierDensity hm
  have hg : Integrable (fun y : ℝ => (gaussianFourierDensity m y : ℂ)) :=
    hgReal.ofReal
  apply hg.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards [] with y
    rw [Complex.norm_exp, Complex.I_mul_re]
    simp

private theorem integral_gaussianFourierDensity_mul_re_cexp
    {m : ℝ} (hm : 0 < m) (z : ℂ) (omega : ℝ) :
    (∫ y : ℝ, gaussianFourierDensity m y *
      (z * Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))).re) =
      z.re * Real.exp (-m * omega ^ 2) := by
  let g := fun y : ℝ => (gaussianFourierDensity m y : ℂ) *
    Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))
  have hg : Integrable g := integrable_gaussianFourierDensity_mul_cexp hm omega
  have hzg : Integrable (fun y => z * g y) := hg.const_mul z
  calc
    (∫ y : ℝ, gaussianFourierDensity m y *
        (z * Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))).re) =
      ∫ y : ℝ, (z * g y).re := by
        congr 1
        funext y
        dsimp [g]
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
        ring
    _ = (∫ y : ℝ, z * g y).re := integral_re hzg
    _ = (z * (∫ y : ℝ, g y)).re := by
      congr 1
      exact integral_const_mul z g
    _ = (z * Complex.exp (-(m : ℂ) * (omega : ℂ) ^ 2)).re := by
      rw [integral_gaussianFourierDensity_mul_cexp hm omega]
    _ = z.re * Real.exp (-m * omega ^ 2) := by
      have he : -(m : ℂ) * (omega : ℂ) ^ 2 = ((-m * omega ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      have hexp : Complex.exp (((-m * omega ^ 2 : ℝ) : ℂ)) =
          (Real.exp (-m * omega ^ 2) : ℂ) :=
        (Complex.ofReal_exp (-m * omega ^ 2)).symm
      have hexp' : Complex.exp (-(m : ℂ) * (omega : ℂ) ^ 2) =
          (Real.exp (-m * omega ^ 2) : ℂ) := by rw [he, hexp]
      have hz := congrArg (fun w : ℂ => (z * w).re) hexp'
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] using hz


private theorem integrable_gaussianFourierDensity_mul_re_cexp
    {m : ℝ} (hm : 0 < m) (z : ℂ) (omega : ℝ) :
    Integrable (fun y : ℝ => gaussianFourierDensity m y *
      (z * Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))).re) := by
  have h := ((integrable_gaussianFourierDensity_mul_cexp hm omega).const_mul z).re
  apply h.congr
  filter_upwards [] with y
  change (z * ((gaussianFourierDensity m y : ℂ) *
      Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ))))).re = _
  rw [show z * ((gaussianFourierDensity m y : ℂ) *
      Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))) =
    (gaussianFourierDensity m y : ℂ) *
      (z * Complex.exp (Complex.I * ((omega : ℂ) * (y : ℂ)))) by ring]
  simp

private theorem conj_exponential_cross_term
    (ai aj : ℂ) (di dj fi fj t y : ℝ) :
    starRingEnd ℂ
        (aj * (Real.exp (dj * t) : ℂ) *
          Complex.exp (Complex.I * ((fj : ℂ) * (y : ℂ)))) *
      (ai * (Real.exp (di * t) : ℂ) *
        Complex.exp (Complex.I * ((fi : ℂ) * (y : ℂ)))) =
    (starRingEnd ℂ (aj * Real.exp (dj * t)) *
      (ai * Real.exp (di * t))) *
        Complex.exp (Complex.I * (((fi - fj) : ℂ) * (y : ℂ))) := by
  rw [map_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  calc
    _ = (starRingEnd ℂ aj * Real.exp (dj * t) *
          (ai * Real.exp (di * t))) *
        (Complex.exp (-Complex.I * ((fj : ℂ) * (y : ℂ))) *
          Complex.exp (Complex.I * ((fi : ℂ) * (y : ℂ)))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

variable {ι : Type*} [DecidableEq ι]

private noncomputable def gaussianCrossIntegrand
    (coeff : ι → ℂ) (drift freq : ι → ℝ) (i j : ι) (t m y : ℝ) : ℝ :=
  gaussianFourierDensity m y *
    (starRingEnd ℂ
        (coeff j * (Real.exp (drift j * t) : ℂ) *
          Complex.exp (Complex.I * ((freq j : ℂ) * (y : ℂ)))) *
      (coeff i * (Real.exp (drift i * t) : ℂ) *
        Complex.exp (Complex.I * ((freq i : ℂ) * (y : ℂ))))).re

private theorem gaussianCrossIntegrand_eq
    (coeff : ι → ℂ) (drift freq : ι → ℝ) (i j : ι) (t m y : ℝ) :
    gaussianCrossIntegrand coeff drift freq i j t m y =
      gaussianFourierDensity m y *
        ((starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
            (coeff i * Real.exp (drift i * t))) *
          Complex.exp (Complex.I * (((freq i - freq j) : ℂ) * (y : ℂ)))).re := by
  rw [gaussianCrossIntegrand]
  congr 1
  exact congrArg Complex.re
    (conj_exponential_cross_term (coeff i) (coeff j)
      (drift i) (drift j) (freq i) (freq j) t y)

private theorem integrable_gaussianCrossIntegrand
    (coeff : ι → ℂ) (drift freq : ι → ℝ) (i j : ι) (t : ℝ)
    {m : ℝ} (hm : 0 < m) :
    Integrable (gaussianCrossIntegrand coeff drift freq i j t m) := by
  apply (integrable_gaussianFourierDensity_mul_re_cexp hm
    (starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
      (coeff i * Real.exp (drift i * t))) (freq i - freq j)).congr
  filter_upwards [] with y
  rw [gaussianCrossIntegrand_eq]
  congr 2
  push_cast
  ring

private theorem integral_gaussianCrossIntegrand
    (coeff : ι → ℂ) (drift freq : ι → ℝ) (i j : ι) (t : ℝ)
    {m : ℝ} (hm : 0 < m) :
    (∫ y : ℝ, gaussianCrossIntegrand coeff drift freq i j t m y) =
      (starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
        (coeff i * Real.exp (drift i * t))).re *
          Real.exp (-m * (freq i - freq j) ^ 2) := by
  rw [show (fun y => gaussianCrossIntegrand coeff drift freq i j t m y) =
      (fun y => gaussianFourierDensity m y *
        ((starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
            (coeff i * Real.exp (drift i * t))) *
          Complex.exp (Complex.I * (((freq i - freq j) : ℂ) * (y : ℂ)))).re) by
    funext y
    exact gaussianCrossIntegrand_eq coeff drift freq i j t m y]
  simpa only [Complex.ofReal_sub] using
    integral_gaussianFourierDensity_mul_re_cexp hm
      (starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
        (coeff i * Real.exp (drift i * t))) (freq i - freq j)

theorem gaussianWeightedSecondMoment_eq_hermitian_sum
    (S : Finset ι) (coeff : ι → ℂ) (drift freq : ι → ℝ)
    (t : ℝ) {m : ℝ} (hm : 0 < m) :
    gaussianWeightedSecondMoment S coeff drift freq t m =
      ∑ i ∈ S, ∑ j ∈ S,
        (starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
          (coeff i * Real.exp (drift i * t))).re *
            Real.exp (-m * (freq i - freq j) ^ 2) := by
  rw [gaussianWeightedSecondMoment]
  simp_rw [frozenDriftingExponentialPolynomial,
    MathlibAux.normSq_finset_sum_eq_sum_re_conj_mul]
  have hpoint : (fun y : ℝ => gaussianFourierDensity m y *
      ∑ i ∈ S, ∑ j ∈ S,
        (starRingEnd ℂ
            (coeff j * (Real.exp (drift j * t) : ℂ) *
              Complex.exp (Complex.I * ((freq j : ℂ) * (y : ℂ)))) *
          (coeff i * (Real.exp (drift i * t) : ℂ) *
            Complex.exp (Complex.I * ((freq i : ℂ) * (y : ℂ))))).re) =
      (fun y : ℝ => ∑ i ∈ S, ∑ j ∈ S,
        gaussianCrossIntegrand coeff drift freq i j t m y) := by
    funext y
    simp_rw [gaussianCrossIntegrand, Finset.mul_sum]
  rw [hpoint, integral_finset_sum S]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finset_sum S]
    · apply Finset.sum_congr rfl
      intro j hj
      exact integral_gaussianCrossIntegrand coeff drift freq i j t hm
    · intro j hj
      exact integrable_gaussianCrossIntegrand coeff drift freq i j t hm
  · intro i hi
    exact integrable_finset_sum S fun j hj =>
      integrable_gaussianCrossIntegrand coeff drift freq i j t hm


theorem gaussianWeightedSecondMoment_le_driftingGram
    (S : Finset ι) (coeff : ι → ℂ) (mass drift freq : ι → ℝ)
    (t : ℝ) {m : ℝ} (hm : 0 < m)
    (hmass : ∀ i ∈ S, ‖coeff i‖ = mass i) :
    gaussianWeightedSecondMoment S coeff drift freq t m ≤
      dyadicDriftingGaussianGram S mass drift freq t m := by
  rw [gaussianWeightedSecondMoment_eq_hermitian_sum S coeff drift freq t hm]
  rw [dyadicDriftingGaussianGram]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hk : 0 ≤ Real.exp (-m * (freq i - freq j) ^ 2) := Real.exp_nonneg _
  gcongr
  calc
    (starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
        (coeff i * Real.exp (drift i * t))).re ≤
      ‖starRingEnd ℂ (coeff j * Real.exp (drift j * t)) *
        (coeff i * Real.exp (drift i * t))‖ := Complex.re_le_norm _
    _ = driftingMass mass drift t i * driftingMass mass drift t j := by
      rw [norm_mul, Complex.norm_conj, norm_mul, norm_mul, hmass i hi, hmass j hj]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [driftingMass, driftingMass]
      ring

end MathlibAux
