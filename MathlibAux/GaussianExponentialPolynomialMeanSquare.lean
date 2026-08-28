import MathlibAux.DirichletPolynomialMeanSquare
import MathlibAux.GaussianExponentialIntegral

/-!
# Gaussian mean square of a finite exponential polynomial

The full-line Gaussian second moment is bounded by its exact positive
frequency kernel.  This is the finite analytic layer needed after an
approximate functional equation.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace MathlibAux

private theorem normSq_exponentialPolynomial_eq_gaussian_double_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    Complex.normSq (exponentialPolynomial s coeff freq t) =
      ∑ m ∈ s, ∑ n ∈ s,
        ((starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((freq m - freq n) * t))).re := by
  have hnorm :
      Complex.normSq (exponentialPolynomial s coeff freq t) =
        ((starRingEnd ℂ) (exponentialPolynomial s coeff freq t) *
          exponentialPolynomial s coeff freq t).re := by
    have h := congrArg Complex.re
      (Complex.normSq_eq_conj_mul_self
        (z := exponentialPolynomial s coeff freq t))
    simpa using h
  rw [hnorm]
  simp only [exponentialPolynomial, map_sum, Finset.sum_mul, Finset.mul_sum,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, conj_I, conj_ofReal]
  rw [show
    (starRingEnd ℂ) (coeff n) *
        Complex.exp (-I * ((freq n : ℂ) * (t : ℂ))) *
        (coeff m * Complex.exp (I * ((freq m : ℂ) * (t : ℂ)))) =
      ((starRingEnd ℂ) (coeff n) * coeff m) *
        (Complex.exp (-I * ((freq n : ℂ) * (t : ℂ))) *
          Complex.exp (I * ((freq m : ℂ) * (t : ℂ)))) by ring]
  rw [← Complex.exp_add]
  congr 2
  ring

/-- Gaussian second moment bounded by the exact positive frequency kernel.
No frequency separation is assumed. -/
theorem integral_gaussian_mul_normSq_exponentialPolynomial_le
    {ι : Type*} [DecidableEq ι]
    {Delta : ℝ} (hDelta : 0 < Delta) (w : ℝ)
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq (exponentialPolynomial s coeff freq t)) ≤
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        ∑ m ∈ s, ∑ n ∈ s,
          ‖coeff m‖ * ‖coeff n‖ *
            Real.exp (-(Delta ^ 2 * (freq m - freq n) ^ 2) / 4) := by
  have htermInt (m n : ι) : Integrable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        ((starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((freq m - freq n) * t))).re := by
    have hcomplex :=
      (integrable_shiftedGaussian_mul_cexp hDelta w (freq m - freq n)).const_mul
        ((starRingEnd ℂ) (coeff n) * coeff m)
    have hre : Integrable fun t : ℝ =>
        (((starRingEnd ℂ) (coeff n) * coeff m) *
          ((Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
            Complex.exp (I * ((freq m - freq n : ℝ) : ℂ) * (t : ℂ)))).re :=
      hcomplex.re
    refine hre.congr (Filter.Eventually.of_forall fun t => ?_)
    change
      (((starRingEnd ℂ) (coeff n) * coeff m) *
          ((Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
            Complex.exp
              (I * ((freq m - freq n : ℝ) : ℂ) * (t : ℂ)))).re =
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          (((starRingEnd ℂ) (coeff n) * coeff m) *
            Complex.exp
              (I * (((freq m : ℂ) - (freq n : ℂ)) * (t : ℂ)))).re
    rw [show ((freq m - freq n : ℝ) : ℂ) =
      (freq m : ℂ) - (freq n : ℂ) by push_cast; rfl]
    calc
      _ = (((Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
              ((starRingEnd ℂ) (coeff n) * coeff m *
                Complex.exp
                  (I * (((freq m : ℂ) - (freq n : ℂ)) * (t : ℂ)))))).re := by
            congr 1
            ring
      _ = _ := by
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsumInt : Integrable fun t : ℝ =>
      ∑ m ∈ s, ∑ n ∈ s,
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          ((starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((freq m - freq n) * t))).re := by
    exact integrable_finsetSum s fun m _hm =>
      integrable_finsetSum s fun n _hn => htermInt m n
  rw [show (fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq (exponentialPolynomial s coeff freq t)) =
      fun t : ℝ => ∑ m ∈ s, ∑ n ∈ s,
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          ((starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((freq m - freq n) * t))).re by
    funext t
    rw [normSq_exponentialPolynomial_eq_gaussian_double_sum]
    simp only [Finset.mul_sum]]
  rw [integral_finsetSum s (fun m _hm =>
    integrable_finsetSum s fun n _hn => htermInt m n)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [integral_finsetSum s (fun n _hn => htermInt m n)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hcomplex :=
    (integrable_shiftedGaussian_mul_cexp hDelta w (freq m - freq n)).const_mul
      ((starRingEnd ℂ) (coeff n) * coeff m)
  have hre :
      (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        ((starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((freq m - freq n) * t))).re) =
      (∫ t : ℝ,
        ((starRingEnd ℂ) (coeff n) * coeff m) *
          ((Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
            Complex.exp (I * ((freq m - freq n : ℝ) : ℂ) * (t : ℂ)))).re := by
    calc
      _ = ∫ t : ℝ,
          (((starRingEnd ℂ) (coeff n) * coeff m) *
            ((Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
              Complex.exp
                (I * ((freq m - freq n : ℝ) : ℂ) * (t : ℂ)))).re := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => by
          change
            Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
                (((starRingEnd ℂ) (coeff n) * coeff m) *
                  Complex.exp
                    (I * (((freq m : ℂ) - (freq n : ℂ)) * (t : ℂ)))).re =
              (((starRingEnd ℂ) (coeff n) * coeff m) *
                ((Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
                  Complex.exp
                    (I * ((freq m - freq n : ℝ) : ℂ) * (t : ℂ)))).re
          rw [show ((freq m - freq n : ℝ) : ℂ) =
            (freq m : ℂ) - (freq n : ℂ) by push_cast; rfl]
          calc
            _ = (((Real.exp (-((t - w) ^ 2) / Delta ^ 2) : ℂ) *
                  (((starRingEnd ℂ) (coeff n) * coeff m) *
                    Complex.exp
                      (I * (((freq m : ℂ) - (freq n : ℂ)) *
                        (t : ℂ)))))).re := by
              simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                zero_mul, sub_zero]
            _ = _ := by
              congr 1
              ring
      _ = _ := Complex.reCLM.integral_comp_comm hcomplex
  rw [hre]
  have hkernel := integral_shiftedGaussian_mul_cexp
    hDelta w (freq m - freq n)
  rw [integral_const_mul, hkernel]
  calc
    (((starRingEnd ℂ) (coeff n) * coeff m) *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) : ℂ) *
          Complex.exp
            (-(Delta ^ 2 * (freq m - freq n) ^ 2) / 4 : ℝ) *
          Complex.exp
            (I * ((freq m - freq n : ℝ) : ℂ) * (w : ℂ)))).re ≤
      ‖((starRingEnd ℂ) (coeff n) * coeff m) *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) : ℂ) *
          Complex.exp
            (-(Delta ^ 2 * (freq m - freq n) ^ 2) / 4 : ℝ) *
          Complex.exp
            (I * ((freq m - freq n : ℝ) : ℂ) * (w : ℂ)))‖ :=
      Complex.re_le_norm _
    _ = Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        (‖coeff m‖ * ‖coeff n‖ *
          Real.exp (-(Delta ^ 2 * (freq m - freq n) ^ 2) / 4)) := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj]
      have hsqrt :
          ‖(Real.sqrt (Real.pi / (1 / Delta ^ 2)) : ℂ)‖ =
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      have hrealexp :
          ‖Complex.exp
              (-(Delta ^ 2 * (freq m - freq n) ^ 2) / 4 : ℝ)‖ =
            Real.exp (-(Delta ^ 2 * (freq m - freq n) ^ 2) / 4) := by
        rw [Complex.norm_exp]
        simp only [Complex.ofReal_re]
      have himagexp :
          ‖Complex.exp
              (I * ((freq m - freq n : ℝ) : ℂ) * (w : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        norm_num
      rw [hsqrt, hrealexp, himagexp]
      ring

end MathlibAux
