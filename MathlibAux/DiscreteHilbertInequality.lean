import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import MathlibAux.DirichletPolynomialMeanSquare

open Complex MeasureTheory Set
open scoped Interval

namespace MathlibAux

/-- The finite discrete Hilbert bilinear form.  The diagonal is removed before
division, so the definition is total for arbitrary finite index sets. -/
noncomputable def discreteHilbertForm
    (s : Finset ℕ) (coeff : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (coeff n) * coeff m / ((m : ℂ) - (n : ℂ))

/-- The two-sequence version of the finite discrete Hilbert form. -/
noncomputable def discreteHilbertBilinearForm
    (s : Finset ℕ) (left right : ℕ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if m = n then 0
    else (starRingEnd ℂ) (left n) * right m / ((m : ℂ) - (n : ℂ))

private theorem integral_cexp_int_frequency_eq_zero
    (k : ℤ) (hk : k ≠ 0) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      Complex.exp (I * ((k : ℝ) * t))) = 0 := by
  let c : ℂ := I * (k : ℂ)
  have hc : c ≠ 0 := by
    exact mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr hk)
  have hfun : (fun t : ℝ => Complex.exp (I * ((k : ℝ) * t))) =
      fun t : ℝ => Complex.exp (c * t) := by
    funext t
    dsimp only [c]
    push_cast
    ring
  rw [hfun, integral_exp_mul_complex hc]
  have hupper : Complex.exp (c * (2 * Real.pi : ℝ)) = 1 := by
    rw [show c * (2 * Real.pi : ℝ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * I) by
      dsimp only [c]
      push_cast
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [hupper]
  simp

private theorem integral_sawtooth_mul_cexp_int_frequency
    (k : ℤ) (hk : k ≠ 0) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      ((Real.pi - t : ℝ) : ℂ) *
        Complex.exp (I * ((k : ℝ) * t))) =
      2 * Real.pi * I / (k : ℂ) := by
  let c : ℂ := I * (k : ℂ)
  have hc : c ≠ 0 := by
    exact mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr hk)
  have hphasefun :
      (fun t : ℝ => Complex.exp (I * ((k : ℝ) * t))) =
        fun t : ℝ => Complex.exp (c * t) := by
    funext t
    dsimp only [c]
    push_cast
    ring
  let u : ℝ → ℂ := fun t => (Real.pi - t : ℝ)
  let v : ℝ → ℂ := fun t => Complex.exp (c * t) / c
  let u' : ℝ → ℂ := fun _ => -1
  let v' : ℝ → ℂ := fun t => Complex.exp (c * t)
  have hu : ∀ x ∈ [[(0 : ℝ), 2 * Real.pi]], HasDerivAt u (u' x) x := by
    intro x hx
    dsimp only [u, u']
    simpa using
      ((hasDerivAt_const x (Real.pi : ℂ)).sub
        Complex.ofRealCLM.hasDerivAt)
  have hv : ∀ x ∈ [[(0 : ℝ), 2 * Real.pi]], HasDerivAt v (v' x) x := by
    intro x hx
    dsimp only [v, v']
    have harg : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
      simpa using Complex.ofRealCLM.hasDerivAt.const_mul c
    simpa [hc] using harg.cexp.div_const c
  have huInt : IntervalIntegrable u' volume (0 : ℝ) (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hvInt : IntervalIntegrable v' volume (0 : ℝ) (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv huInt hvInt
  have hzero := integral_cexp_int_frequency_eq_zero k hk
  have hupper : Complex.exp (c * (2 * Real.pi : ℝ)) = 1 := by
    rw [show c * (2 * Real.pi : ℝ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * I) by
      dsimp only [c]
      push_cast
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
        ((Real.pi - t : ℝ) : ℂ) *
          Complex.exp (I * ((k : ℝ) * t))) =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          ((Real.pi - t : ℝ) : ℂ) * Complex.exp (c * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [c]
      push_cast
      ring
    _ = u (2 * Real.pi) * v (2 * Real.pi) - u 0 * v 0 -
          ∫ t in (0 : ℝ)..2 * Real.pi, u' t * v t := by
      simpa only [u, v, u', v'] using hibp
    _ = 2 * Real.pi * I / (k : ℂ) := by
      dsimp only [u, v, u']
      rw [hupper]
      simp only [ofReal_zero, mul_zero, Complex.exp_zero]
      have hvzero : (∫ t in (0 : ℝ)..2 * Real.pi,
          (-1 : ℂ) * (Complex.exp (c * t) / c)) = 0 := by
        have hfun : (fun t : ℝ => Complex.exp (c * t)) =
            fun t : ℝ => Complex.exp (I * ((k : ℝ) * t)) := by
          funext t
          dsimp only [c]
          push_cast
          ring
        calc
          (∫ t in (0 : ℝ)..2 * Real.pi,
              (-1 : ℂ) * (Complex.exp (c * t) / c)) =
              ∫ t in (0 : ℝ)..2 * Real.pi,
                ((-1 : ℂ) / c) * Complex.exp (c * t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
          _ =
              ((-1 : ℂ) / c) *
                ∫ t in (0 : ℝ)..2 * Real.pi, Complex.exp (c * t) :=
            intervalIntegral.integral_const_mul _ _
          _ = 0 := by rw [hfun, hzero, mul_zero]
      rw [hvzero]
      field_simp [hc, Int.cast_ne_zero.mpr hk]
      dsimp only [c]
      push_cast
      rw [show I * (k : ℂ) * 2 * (Real.pi : ℂ) * I =
          ((k : ℂ) * 2 * (Real.pi : ℂ)) * (I * I) by ring,
        Complex.I_mul_I]
      ring

private theorem integral_sawtooth_eq_zero :
    (∫ t in (0 : ℝ)..2 * Real.pi, ((Real.pi - t : ℝ) : ℂ)) = 0 := by
  have hrealInt : IntervalIntegrable (fun t : ℝ => Real.pi - t)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi, ((Real.pi - t : ℝ) : ℂ)) =
        Complex.ofRealCLM
          (∫ t in (0 : ℝ)..2 * Real.pi, Real.pi - t) :=
      Complex.ofRealCLM.intervalIntegral_comp_comm hrealInt
    _ = 0 := by
      have hzero : (∫ t in (0 : ℝ)..2 * Real.pi, Real.pi - t) = 0 := by
        rw [intervalIntegral.integral_sub]
        · rw [intervalIntegral.integral_const, integral_id]
          simp only [smul_eq_mul]
          ring
        · exact continuous_const.intervalIntegrable _ _
        · exact continuous_id.intervalIntegrable _ _
      rw [hzero]
      exact map_zero Complex.ofRealCLM

private theorem integral_sawtooth_mul_pair
    (coeff : ℕ → ℂ) (m n : ℕ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      ((Real.pi - t : ℝ) : ℂ) *
        ((starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)))) =
      if m = n then 0
      else 2 * Real.pi * I *
        ((starRingEnd ℂ) (coeff n) * coeff m /
          ((m : ℂ) - (n : ℂ))) := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl]
    simp only [sub_self, Int.cast_zero, ofReal_zero, zero_mul, mul_zero,
      Complex.exp_zero, mul_one]
    rw [show (fun t : ℝ =>
        ((Real.pi - t : ℝ) : ℂ) *
          ((starRingEnd ℂ) (coeff m) * coeff m)) =
        fun t : ℝ => ((starRingEnd ℂ) (coeff m) * coeff m) *
          ((Real.pi - t : ℝ) : ℂ) by
      funext t
      ring]
    calc
      (∫ t in (0 : ℝ)..2 * Real.pi,
          ((starRingEnd ℂ) (coeff m) * coeff m) *
            ((Real.pi - t : ℝ) : ℂ)) =
          ((starRingEnd ℂ) (coeff m) * coeff m) *
            ∫ t in (0 : ℝ)..2 * Real.pi,
              ((Real.pi - t : ℝ) : ℂ) :=
        intervalIntegral.integral_const_mul _ _
      _ = 0 := by rw [integral_sawtooth_eq_zero, mul_zero]
  · rw [if_neg hmn]
    let k : ℤ := (m : ℤ) - (n : ℤ)
    have hk : k ≠ 0 := by
      exact sub_ne_zero.mpr (Int.ofNat_injective.ne hmn)
    have hsaw := integral_sawtooth_mul_cexp_int_frequency k hk
    rw [show (fun t : ℝ =>
        ((Real.pi - t : ℝ) : ℂ) *
          ((starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((k : ℝ) * t)))) =
        fun t : ℝ => ((starRingEnd ℂ) (coeff n) * coeff m) *
          (((Real.pi - t : ℝ) : ℂ) *
            Complex.exp (I * ((k : ℝ) * t))) by
      funext t
      ring]
    have hkcast : (k : ℂ) = (m : ℂ) - (n : ℂ) := by
      dsimp only [k]
      push_cast
      rfl
    calc
      (∫ t in (0 : ℝ)..2 * Real.pi,
          ((starRingEnd ℂ) (coeff n) * coeff m) *
            (((Real.pi - t : ℝ) : ℂ) *
              Complex.exp (I * ((k : ℝ) * t)))) =
          ((starRingEnd ℂ) (coeff n) * coeff m) *
            ∫ t in (0 : ℝ)..2 * Real.pi,
              (((Real.pi - t : ℝ) : ℂ) *
                Complex.exp (I * ((k : ℝ) * t))) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by rw [hsaw, hkcast]; ring

private theorem conj_mul_exponentialPolynomial_eq_double_sum
    (s : Finset ℕ) (coeff : ℕ → ℂ) (t : ℝ) :
    (starRingEnd ℂ)
          (exponentialPolynomial s coeff (fun n => (n : ℝ)) t) *
        exponentialPolynomial s coeff (fun n => (n : ℝ)) t =
      ∑ m ∈ s, ∑ n ∈ s,
        (starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)) := by
  simp only [exponentialPolynomial, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, conj_I, conj_ofReal]
  rw [show
      (starRingEnd ℂ) (coeff n) *
          Complex.exp (-I * ((n : ℝ) * t)) *
          (coeff m * Complex.exp (I * ((m : ℝ) * t))) =
        ((starRingEnd ℂ) (coeff n) * coeff m) *
          (Complex.exp (-I * ((n : ℝ) * t)) *
            Complex.exp (I * ((m : ℝ) * t))) by ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integral_sawtooth_mul_conj_mul_exponentialPolynomial_eq
    (s : Finset ℕ) (coeff : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      ((Real.pi - t : ℝ) : ℂ) *
        ((starRingEnd ℂ)
            (exponentialPolynomial s coeff (fun n => (n : ℝ)) t) *
          exponentialPolynomial s coeff (fun n => (n : ℝ)) t)) =
      2 * Real.pi * I * discreteHilbertForm s coeff := by
  have hpoint : (fun t : ℝ =>
      ((Real.pi - t : ℝ) : ℂ) *
        ((starRingEnd ℂ)
            (exponentialPolynomial s coeff (fun n => (n : ℝ)) t) *
          exponentialPolynomial s coeff (fun n => (n : ℝ)) t)) =
      fun t : ℝ => ∑ m ∈ s, ∑ n ∈ s,
        ((Real.pi - t : ℝ) : ℂ) *
          ((starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))) := by
    funext t
    rw [conj_mul_exponentialPolynomial_eq_double_sum]
    simp only [Finset.mul_sum]
  rw [hpoint]
  rw [intervalIntegral.integral_finset_sum]
  · have hinner (m : ℕ) :
        (∫ t in (0 : ℝ)..2 * Real.pi, ∑ n ∈ s,
          ((Real.pi - t : ℝ) : ℂ) *
            ((starRingEnd ℂ) (coeff n) * coeff m *
              Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)))) =
          ∑ n ∈ s, ∫ t in (0 : ℝ)..2 * Real.pi,
            ((Real.pi - t : ℝ) : ℂ) *
              ((starRingEnd ℂ) (coeff n) * coeff m *
                Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))) := by
      rw [intervalIntegral.integral_finset_sum]
      intro n hn
      apply Continuous.intervalIntegrable
      fun_prop
    rw [show (fun m : ℕ =>
        ∫ t in (0 : ℝ)..2 * Real.pi, ∑ n ∈ s,
          ((Real.pi - t : ℝ) : ℂ) *
            ((starRingEnd ℂ) (coeff n) * coeff m *
              Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)))) =
        fun m : ℕ => ∑ n ∈ s, ∫ t in (0 : ℝ)..2 * Real.pi,
          ((Real.pi - t : ℝ) : ℂ) *
            ((starRingEnd ℂ) (coeff n) * coeff m *
              Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))) by
      funext m
      exact hinner m]
    calc
      (∑ m ∈ s, ∑ n ∈ s, ∫ t in (0 : ℝ)..2 * Real.pi,
          ((Real.pi - t : ℝ) : ℂ) *
            ((starRingEnd ℂ) (coeff n) * coeff m *
              Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)))) =
          ∑ m ∈ s, ∑ n ∈ s,
            if m = n then 0 else 2 * Real.pi * I *
              ((starRingEnd ℂ) (coeff n) * coeff m /
                ((m : ℂ) - (n : ℂ))) := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        exact integral_sawtooth_mul_pair coeff m n
      _ = 2 * Real.pi * I * discreteHilbertForm s coeff := by
        unfold discreteHilbertForm
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hmn : m = n <;> simp [hmn]
  · intro m hm
    apply Continuous.intervalIntegrable
    fun_prop

private theorem integral_re_exponential_pair
    (coeff : ℕ → ℂ) (m n : ℕ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      ((starRingEnd ℂ) (coeff n) * coeff m *
        Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))).re) =
      if m = n then 2 * Real.pi * Complex.normSq (coeff n) else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl]
    simp only [sub_self, Int.cast_zero, ofReal_zero, zero_mul, mul_zero,
      Complex.exp_zero, mul_one]
    have hnorm :
        ((starRingEnd ℂ) (coeff m) * coeff m).re =
          Complex.normSq (coeff m) := by
      have h := Complex.normSq_eq_conj_mul_self (z := coeff m)
      exact (congrArg Complex.re h).symm
    rw [hnorm, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  · rw [if_neg hmn]
    let k : ℤ := (m : ℤ) - (n : ℤ)
    have hk : k ≠ 0 := sub_ne_zero.mpr (Int.ofNat_injective.ne hmn)
    have hcomplexInt : IntervalIntegrable
        (fun t : ℝ => ((starRingEnd ℂ) (coeff n) * coeff m) *
          Complex.exp (I * ((k : ℝ) * t))) volume 0 (2 * Real.pi) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hre :
        (∫ t in (0 : ℝ)..2 * Real.pi,
          (((starRingEnd ℂ) (coeff n) * coeff m) *
            Complex.exp (I * ((k : ℝ) * t))).re) =
          (∫ t in (0 : ℝ)..2 * Real.pi,
            ((starRingEnd ℂ) (coeff n) * coeff m) *
              Complex.exp (I * ((k : ℝ) * t))).re :=
      Complex.reCLM.intervalIntegral_comp_comm hcomplexInt
    change (∫ t in (0 : ℝ)..2 * Real.pi,
      (((starRingEnd ℂ) (coeff n) * coeff m) *
        Complex.exp (I * ((k : ℝ) * t))).re) = 0
    have hfactor :
        (∫ t in (0 : ℝ)..2 * Real.pi,
          ((starRingEnd ℂ) (coeff n) * coeff m) *
            Complex.exp (I * ((k : ℝ) * t))) =
          ((starRingEnd ℂ) (coeff n) * coeff m) *
            ∫ t in (0 : ℝ)..2 * Real.pi,
              Complex.exp (I * ((k : ℝ) * t)) :=
      intervalIntegral.integral_const_mul _ _
    rw [hre, hfactor, integral_cexp_int_frequency_eq_zero k hk, mul_zero]
    rfl

private theorem integral_normSq_exponentialPolynomial_nat_eq
    (s : Finset ℕ) (coeff : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      Complex.normSq
        (exponentialPolynomial s coeff (fun n => (n : ℝ)) t)) =
      2 * Real.pi * ∑ n ∈ s, Complex.normSq (coeff n) := by
  have hpoint : (fun t : ℝ => Complex.normSq
      (exponentialPolynomial s coeff (fun n => (n : ℝ)) t)) =
      fun t : ℝ => ∑ m ∈ s, ∑ n ∈ s,
        ((starRingEnd ℂ) (coeff n) * coeff m *
          Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))).re := by
    funext t
    have hnorm : Complex.normSq
          (exponentialPolynomial s coeff (fun n => (n : ℝ)) t) =
        ((starRingEnd ℂ)
            (exponentialPolynomial s coeff (fun n => (n : ℝ)) t) *
          exponentialPolynomial s coeff (fun n => (n : ℝ)) t).re := by
      have h := Complex.normSq_eq_conj_mul_self
        (z := exponentialPolynomial s coeff (fun n => (n : ℝ)) t)
      calc
        Complex.normSq
            (exponentialPolynomial s coeff (fun n => (n : ℝ)) t) =
            ((Complex.normSq
              (exponentialPolynomial s coeff (fun n => (n : ℝ)) t) : ℂ)).re := by
          simp
        _ = _ := congrArg Complex.re h
    rw [hnorm, conj_mul_exponentialPolynomial_eq_double_sum]
    simp only [Complex.re_sum]
  rw [hpoint, intervalIntegral.integral_finset_sum]
  · have hinner (m : ℕ) :
        (∫ t in (0 : ℝ)..2 * Real.pi, ∑ n ∈ s,
          ((starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))).re) =
          ∑ n ∈ s, ∫ t in (0 : ℝ)..2 * Real.pi,
            ((starRingEnd ℂ) (coeff n) * coeff m *
              Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))).re := by
      rw [intervalIntegral.integral_finset_sum]
      intro n hn
      apply Continuous.intervalIntegrable
      fun_prop
    rw [show (fun m : ℕ =>
        ∫ t in (0 : ℝ)..2 * Real.pi, ∑ n ∈ s,
          ((starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))).re) =
        fun m : ℕ => ∑ n ∈ s, ∫ t in (0 : ℝ)..2 * Real.pi,
          ((starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))).re by
      funext m
      exact hinner m]
    calc
      (∑ m ∈ s, ∑ n ∈ s, ∫ t in (0 : ℝ)..2 * Real.pi,
          ((starRingEnd ℂ) (coeff n) * coeff m *
            Complex.exp (I * ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))).re) =
          ∑ m ∈ s, ∑ n ∈ s,
            if m = n then 2 * Real.pi * Complex.normSq (coeff n) else 0 := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        exact integral_re_exponential_pair coeff m n
      _ = 2 * Real.pi * ∑ n ∈ s, Complex.normSq (coeff n) := by
        simp [Finset.mul_sum]
  · intro m hm
    apply Continuous.intervalIntegrable
    fun_prop

private theorem four_mul_discreteHilbertBilinearForm_eq_polarization
    (s : Finset ℕ) (left right : ℕ → ℂ) :
    4 * discreteHilbertBilinearForm s left right =
      discreteHilbertForm s (fun n => left n + right n) -
        discreteHilbertForm s (fun n => left n - right n) -
        I * discreteHilbertForm s (fun n => left n + I * right n) +
        I * discreteHilbertForm s (fun n => left n - I * right n) := by
  unfold discreteHilbertBilinearForm discreteHilbertForm
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, ↓reduceIte, map_add, map_sub, map_mul, conj_I]
    have hden : (m : ℂ) - (n : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (Nat.cast_injective.ne hmn)
    field_simp [hden]
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem normSq_four_polarization_sum (x y : ℂ) :
    Complex.normSq (x + y) + Complex.normSq (x - y) +
        Complex.normSq (x + I * y) + Complex.normSq (x - I * y) =
      4 * (Complex.normSq x + Complex.normSq y) := by
  simp only [Complex.normSq_apply, add_re, add_im, sub_re, sub_im,
    mul_re, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub]
  ring

/-- Hilbert's finite discrete inequality with its classical constant `π`.
The proof realizes the kernel `1 / (m - n)` as a Fourier coefficient of the
bounded sawtooth `π - t` and uses exact orthogonality of integer frequencies. -/
theorem norm_discreteHilbertForm_le_pi_mul_sum_normSq
    (s : Finset ℕ) (coeff : ℕ → ℂ) :
    ‖discreteHilbertForm s coeff‖ ≤
      Real.pi * ∑ n ∈ s, Complex.normSq (coeff n) := by
  let P : ℝ → ℂ := fun t =>
    exponentialPolynomial s coeff (fun n => (n : ℝ)) t
  have hPcont : Continuous P := by
    dsimp only [P, exponentialPolynomial]
    fun_prop
  have hrep :
      (∫ t in (0 : ℝ)..2 * Real.pi,
        ((Real.pi - t : ℝ) : ℂ) *
          ((starRingEnd ℂ) (P t) * P t)) =
        2 * Real.pi * I * discreteHilbertForm s coeff := by
    simpa only [P] using
      integral_sawtooth_mul_conj_mul_exponentialPolynomial_eq s coeff
  have hmajor : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ‖((Real.pi - t : ℝ) : ℂ) *
          ((starRingEnd ℂ) (P t) * P t)‖ ≤
        Real.pi * Complex.normSq (P t) := by
    intro t ht
    have habs : |Real.pi - t| ≤ Real.pi := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_real,
      Real.norm_eq_abs, Complex.norm_mul_self_eq_normSq]
    exact mul_le_mul_of_nonneg_right habs (Complex.normSq_nonneg (P t))
  have hgInt : IntervalIntegrable
      (fun t : ℝ => Real.pi * Complex.normSq (P t))
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (Complex.continuous_normSq.comp hPcont)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
    (by filter_upwards with t; intro ht; exact hmajor t ht) hgInt
  have hmajorInt :
      (∫ t in (0 : ℝ)..2 * Real.pi,
        Real.pi * Complex.normSq (P t)) =
        Real.pi * (2 * Real.pi *
          ∑ n ∈ s, Complex.normSq (coeff n)) := by
    rw [intervalIntegral.integral_const_mul]
    rw [show (∫ t in (0 : ℝ)..2 * Real.pi, Complex.normSq (P t)) =
        2 * Real.pi * ∑ n ∈ s, Complex.normSq (coeff n) by
      simpa only [P] using
        integral_normSq_exponentialPolynomial_nat_eq s coeff]
  have htotal :
      ‖2 * Real.pi * I * discreteHilbertForm s coeff‖ ≤
        Real.pi * (2 * Real.pi *
          ∑ n ∈ s, Complex.normSq (coeff n)) := by
    rw [← hrep, ← hmajorInt]
    exact hnorm
  have hscale :
      ‖2 * Real.pi * I * discreteHilbertForm s coeff‖ =
        2 * Real.pi * ‖discreteHilbertForm s coeff‖ := by
    simp only [norm_mul, norm_I, norm_ofNat, norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    ring
  rw [hscale] at htotal
  have hsum : 0 ≤ ∑ n ∈ s, Complex.normSq (coeff n) := by
    apply Finset.sum_nonneg
    intro n hn
    exact Complex.normSq_nonneg (coeff n)
  nlinarith [Real.pi_pos]

/-- Bilinear Hilbert inequality in a polarization-friendly form.  The right
side is homogeneous after reciprocal rescaling of the two input sequences,
which is the form needed on dyadic logarithmic-frequency blocks. -/
theorem norm_discreteHilbertBilinearForm_le_pi_mul_add_sum_normSq
    (s : Finset ℕ) (left right : ℕ → ℂ) :
    ‖discreteHilbertBilinearForm s left right‖ ≤
      Real.pi * ((∑ n ∈ s, Complex.normSq (left n)) +
        ∑ n ∈ s, Complex.normSq (right n)) := by
  let qpp := discreteHilbertForm s (fun n => left n + right n)
  let qpm := discreteHilbertForm s (fun n => left n - right n)
  let qip := discreteHilbertForm s (fun n => left n + I * right n)
  let qim := discreteHilbertForm s (fun n => left n - I * right n)
  have hqpp : ‖qpp‖ ≤ Real.pi *
      ∑ n ∈ s, Complex.normSq (left n + right n) := by
    exact norm_discreteHilbertForm_le_pi_mul_sum_normSq _ _
  have hqpm : ‖qpm‖ ≤ Real.pi *
      ∑ n ∈ s, Complex.normSq (left n - right n) := by
    exact norm_discreteHilbertForm_le_pi_mul_sum_normSq _ _
  have hqip : ‖qip‖ ≤ Real.pi *
      ∑ n ∈ s, Complex.normSq (left n + I * right n) := by
    exact norm_discreteHilbertForm_le_pi_mul_sum_normSq _ _
  have hqim : ‖qim‖ ≤ Real.pi *
      ∑ n ∈ s, Complex.normSq (left n - I * right n) := by
    exact norm_discreteHilbertForm_le_pi_mul_sum_normSq _ _
  have hpolar :
      4 * discreteHilbertBilinearForm s left right =
        qpp - qpm - I * qip + I * qim := by
    simpa only [qpp, qpm, qip, qim] using
      four_mul_discreteHilbertBilinearForm_eq_polarization s left right
  have htriangle : ‖qpp - qpm - I * qip + I * qim‖ ≤
      ‖qpp‖ + ‖qpm‖ + ‖qip‖ + ‖qim‖ := by
    calc
      ‖qpp - qpm - I * qip + I * qim‖ ≤
          ‖qpp - qpm - I * qip‖ + ‖I * qim‖ := norm_add_le _ _
      _ ≤ (‖qpp - qpm‖ + ‖I * qip‖) + ‖I * qim‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖qpp‖ + ‖qpm‖) + ‖qip‖) + ‖qim‖ := by
        rw [norm_mul, norm_mul, norm_I, one_mul, one_mul]
        gcongr
        exact norm_sub_le _ _
      _ = ‖qpp‖ + ‖qpm‖ + ‖qip‖ + ‖qim‖ := by ring
  have hsumPolar :
      (∑ n ∈ s, Complex.normSq (left n + right n)) +
          (∑ n ∈ s, Complex.normSq (left n - right n)) +
          (∑ n ∈ s, Complex.normSq (left n + I * right n)) +
          (∑ n ∈ s, Complex.normSq (left n - I * right n)) =
        4 * ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    calc
      (∑ n ∈ s,
          (Complex.normSq (left n + right n) +
            Complex.normSq (left n - right n) +
            Complex.normSq (left n + I * right n) +
            Complex.normSq (left n - I * right n))) =
          ∑ n ∈ s, 4 *
            (Complex.normSq (left n) + Complex.normSq (right n)) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact normSq_four_polarization_sum (left n) (right n)
      _ = 4 * ((∑ n ∈ s, Complex.normSq (left n)) +
          ∑ n ∈ s, Complex.normSq (right n)) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  have hscale :
      ‖4 * discreteHilbertBilinearForm s left right‖ =
        4 * ‖discreteHilbertBilinearForm s left right‖ := by
    simp
  have htotal :
      4 * ‖discreteHilbertBilinearForm s left right‖ ≤
        Real.pi *
          ((∑ n ∈ s, Complex.normSq (left n + right n)) +
            (∑ n ∈ s, Complex.normSq (left n - right n)) +
            (∑ n ∈ s, Complex.normSq (left n + I * right n)) +
            (∑ n ∈ s, Complex.normSq (left n - I * right n))) := by
    rw [← hscale, hpolar]
    calc
      ‖qpp - qpm - I * qip + I * qim‖ ≤
          ‖qpp‖ + ‖qpm‖ + ‖qip‖ + ‖qim‖ := htriangle
      _ ≤ _ := by nlinarith [Real.pi_pos]
  rw [hsumPolar] at htotal
  nlinarith [Real.pi_pos]

end MathlibAux
