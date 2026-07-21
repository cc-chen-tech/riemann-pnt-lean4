import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Data.Complex.BigOperators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Complex MeasureTheory Set

namespace MathlibAux

/-- A finite exponential polynomial with complex coefficients and real frequencies. -/
noncomputable def exponentialPolynomial {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, coeff n * Complex.exp (I * (freq n * t))

/-- A nonzero linear frequency has an interval integral bounded only by the
reciprocal frequency gap. -/
theorem norm_integral_cexp_linear_le {a b omega : ℝ} (homega : omega ≠ 0) :
    ‖∫ t in a..b, Complex.exp (I * (omega * t))‖ ≤ 2 / |omega| := by
  have hIomega : I * (omega : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr homega)
  have hform :
      (∫ t in a..b, Complex.exp (I * (omega * t))) =
        (Complex.exp ((I * (omega : ℂ)) * b) -
          Complex.exp ((I * (omega : ℂ)) * a)) /
            (I * (omega : ℂ)) := by
    convert integral_exp_mul_complex (a := a) (b := b) hIomega using 1
    ring
  rw [hform, norm_div, norm_mul, norm_I, one_mul, norm_real]
  have hnum :
      ‖Complex.exp ((I * (omega : ℂ)) * b) -
        Complex.exp ((I * (omega : ℂ)) * a)‖ ≤ 2 := by
    calc
      ‖Complex.exp ((I * (omega : ℂ)) * b) -
          Complex.exp ((I * (omega : ℂ)) * a)‖ ≤
          ‖Complex.exp ((I * (omega : ℂ)) * b)‖ +
            ‖Complex.exp ((I * (omega : ℂ)) * a)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp, Complex.norm_exp]
        norm_num
  exact div_le_div_of_nonneg_right hnum (abs_nonneg omega)

/-- The norm-square of a finite complex sum is the real part of its complete
Hermitian double sum. -/
theorem normSq_finset_sum_eq_sum_re_conj_mul
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ n ∈ s, f n) =
      ∑ m ∈ s, ∑ n ∈ s,
        ((starRingEnd ℂ) (f n) * f m).re := by
  have hnorm :
      Complex.normSq (∑ n ∈ s, f n) =
        ((starRingEnd ℂ) (∑ n ∈ s, f n) *
          (∑ n ∈ s, f n)).re := by
    have h := congrArg Complex.re
      (Complex.normSq_eq_conj_mul_self (z := ∑ n ∈ s, f n))
    simpa using h
  rw [hnorm]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]

private theorem normSq_exponentialPolynomial_eq_sum {ι : Type*} [DecidableEq ι]
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

/-- A finite exponential polynomial has the standard diagonal plus
frequency-gap upper bound for its interval second moment. -/
theorem integral_normSq_exponentialPolynomial_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {a b : ℝ}
    (hfreq : ∀ m ∈ s, ∀ n ∈ s, m ≠ n → freq m ≠ freq n) :
    (∫ t in a..b, Complex.normSq (exponentialPolynomial s coeff freq t)) ≤
      ∑ m ∈ s, ∑ n ∈ s,
        if m = n then (b - a) * Complex.normSq (coeff n)
        else 2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n| := by
  have htermInt (m : ι) (hm : m ∈ s) (n : ι) (hn : n ∈ s) :
      IntervalIntegrable
        (fun t : ℝ => ((starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((freq m - freq n) * t))).re)
        volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [show (fun t : ℝ => Complex.normSq (exponentialPolynomial s coeff freq t)) =
      fun (t : ℝ) => ∑ m ∈ s, ∑ n ∈ s,
        ((starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((freq m - freq n) * t))).re by
      funext t
      exact normSq_exponentialPolynomial_eq_sum s coeff freq t]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_le_sum
    intro m hm
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_le_sum
      intro n hn
      by_cases hmn : m = n
      · subst n
        rw [if_pos rfl]
        simp only [sub_self, zero_mul, mul_zero,
          Complex.exp_zero, mul_one]
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        rw [show ((starRingEnd ℂ) (coeff m) * coeff m).re =
            Complex.normSq (coeff m) by
          have h := Complex.normSq_eq_conj_mul_self (z := coeff m)
          exact (congrArg Complex.re h).symm]
      · simp only [if_neg hmn]
        have homega : freq m - freq n ≠ 0 :=
          sub_ne_zero.mpr (hfreq m hm n hn hmn)
        have hcomplexInt : IntervalIntegrable
            (fun t : ℝ => ((starRingEnd ℂ) (coeff n) * coeff m) *
              Complex.exp (I * ((freq m - freq n) * t))) volume a b := by
          apply Continuous.intervalIntegrable
          fun_prop
        have hre :
            (∫ t in a..b, (((starRingEnd ℂ) (coeff n) * coeff m) *
              Complex.exp (I * ((freq m - freq n) * t))).re) =
              (∫ t in a..b, ((starRingEnd ℂ) (coeff n) * coeff m) *
                Complex.exp (I * ((freq m - freq n) * t))).re := by
          exact Complex.reCLM.intervalIntegral_comp_comm hcomplexInt
        rw [hre]
        have hfactor :
            (∫ t in a..b, ((starRingEnd ℂ) (coeff n) * coeff m) *
              Complex.exp (I * ((freq m - freq n) * t))) =
              ((starRingEnd ℂ) (coeff n) * coeff m) *
                ∫ t in a..b, Complex.exp (I * ((freq m - freq n) * t)) :=
          intervalIntegral.integral_const_mul _ _
        rw [hfactor]
        calc
          (((starRingEnd ℂ) (coeff n) * coeff m) *
              (∫ t in a..b, Complex.exp (I * ((freq m - freq n) * t)))).re ≤
              ‖((starRingEnd ℂ) (coeff n) * coeff m) *
                (∫ t in a..b, Complex.exp (I * ((freq m - freq n) * t)))‖ :=
            Complex.re_le_norm _
          _ = ‖coeff m‖ * ‖coeff n‖ *
              ‖∫ t in a..b, Complex.exp (I * ((freq m - freq n) * t))‖ := by
            simp only [norm_mul, Complex.norm_conj]
            ac_rfl
          _ ≤ ‖coeff m‖ * ‖coeff n‖ * (2 / |freq m - freq n|) := by
            gcongr
            simpa only [ofReal_sub] using
              (norm_integral_cexp_linear_le (a := a) (b := b) homega)
          _ = 2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n| := by
            ring
    · intro n hn
      exact htermInt m hm n hn
  · intro m hm
    apply Continuous.intervalIntegrable
    fun_prop

end MathlibAux
