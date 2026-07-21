import HardyTheorem.FirstZetaApproximation
import MathlibAux.DirichletPolynomialMeanSquare
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Complex MeasureTheory

namespace HardyTheorem

/-- The coefficient obtained by integrating the `n`th critical-line
Dirichlet monomial over an interval of length `delta`. -/
noncomputable def criticalLineShortDirichletCoeff (δ : ℝ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
    ((Complex.exp ((-I * (Real.log n : ℂ)) * δ) - 1) /
      (-I * (Real.log n : ℂ)))

/-- The integrated critical-line coefficient has the usual inverse-frequency
bound coming from cancellation of a nonconstant exponential. -/
theorem norm_criticalLineShortDirichletCoeff_le_two_div
    {δ : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    ‖criticalLineShortDirichletCoeff δ n‖ ≤
      2 / (Real.sqrt n * Real.log n) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hhalf : ‖(n : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt n := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    simp [Real.sqrt_eq_rpow]
  have hden : ‖-I * (Real.log n : ℂ)‖ = Real.log n := by
    rw [norm_mul, norm_neg, norm_I, one_mul, norm_real,
      Real.norm_eq_abs, abs_of_pos hlog]
  have hnum :
      ‖Complex.exp ((-I * (Real.log n : ℂ)) * δ) - 1‖ ≤ 2 := by
    calc
      ‖Complex.exp ((-I * (Real.log n : ℂ)) * δ) - 1‖ ≤
      ‖Complex.exp ((-I * (Real.log n : ℂ)) * δ)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        have harg :
            (-I * (Real.log n : ℂ)) * δ =
              I * (-(Real.log n * δ) : ℝ) := by
          push_cast
          ring
        rw [harg, Complex.norm_exp_I_mul_ofReal]
        norm_num
  dsimp only [criticalLineShortDirichletCoeff]
  rw [norm_mul, norm_inv, hhalf, norm_div, hden]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  calc
    (Real.sqrt n)⁻¹ *
          (‖Complex.exp ((-I * (Real.log n : ℂ)) * δ) - 1‖ /
            Real.log n) ≤
        (Real.sqrt n)⁻¹ * (2 / Real.log n) := by
      gcongr
    _ = 2 / (Real.sqrt n * Real.log n) := by field_simp

/-- Without using oscillation, the same coefficient is bounded by the interval
length divided by the square-root Dirichlet weight. -/
theorem norm_criticalLineShortDirichletCoeff_le_abs_delta
    {δ : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    ‖criticalLineShortDirichletCoeff δ n‖ ≤
      |δ| / Real.sqrt n := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hhalf : ‖(n : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt n := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    simp [Real.sqrt_eq_rpow]
  have hden : ‖-I * (Real.log n : ℂ)‖ = Real.log n := by
    rw [norm_mul, norm_neg, norm_I, one_mul, norm_real,
      Real.norm_eq_abs, abs_of_pos hlog]
  have hnum :
      ‖Complex.exp ((-I * (Real.log n : ℂ)) * δ) - 1‖ ≤
        |Real.log n * δ| := by
    convert (Real.norm_exp_I_mul_ofReal_sub_one_le
      (x := -(Real.log n * δ))) using 1
    · congr 2
      push_cast
      ring
    · rw [Real.norm_eq_abs, abs_neg]
  dsimp only [criticalLineShortDirichletCoeff]
  rw [norm_mul, norm_inv, hhalf, norm_div, hden]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  calc
    (Real.sqrt n)⁻¹ *
          (‖Complex.exp ((-I * (Real.log n : ℂ)) * δ) - 1‖ /
            Real.log n) ≤
        (Real.sqrt n)⁻¹ * (|Real.log n * δ| / Real.log n) := by
      gcongr
    _ = |δ| / Real.sqrt n := by
      rw [abs_mul, abs_of_pos hlog]
      field_simp

/-- The finite exponential polynomial representing a short integral of the
nonconstant part of the critical-line Dirichlet polynomial. -/
noncomputable def criticalLineShortDirichletPolynomial
    (δ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial (Finset.Icc 2 N)
    (criticalLineShortDirichletCoeff δ)
    (fun n => -Real.log n) t

/-- Integrating the nonconstant critical-line Dirichlet polynomial over a
sliding interval produces exactly the associated finite exponential
polynomial in the left endpoint. -/
theorem integral_criticalLineDirichletPolynomial_eq_shortPolynomial
    (δ t : ℝ) (N : ℕ) :
    (∫ u in t..t + δ,
        ∑ n ∈ Finset.Icc 2 N,
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) =
      criticalLineShortDirichletPolynomial δ N t := by
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hnmem
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnmem).1
    have hn0 : n ≠ 0 := by omega
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
    let c : ℂ := -I * (Real.log n : ℂ)
    have hc : c ≠ 0 := by
      dsimp only [c]
      exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
        (ofReal_ne_zero.mpr hlog.ne')
    rw [show (fun u : ℝ =>
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) =
      fun u : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (c * u) by
        funext u
        simpa only [c] using inv_nat_cpow_criticalLine_eq_exp hn0 u]
    have hfactor :
        (∫ u in t..t + δ,
            ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (c * u)) =
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            ∫ u in t..t + δ, Complex.exp (c * u) :=
      intervalIntegral.integral_const_mul _ _
    rw [hfactor, integral_exp_mul_complex hc]
    dsimp only [criticalLineShortDirichletCoeff]
    push_cast
    rw [← Complex.natCast_log]
    rw [show I * (-((Real.log n : ℝ) : ℂ) * (t : ℂ)) = c * t by
      dsimp only [c]
      ring]
    change ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        ((Complex.exp (c * (t + δ)) - Complex.exp (c * t)) / c) =
      ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        ((Complex.exp (c * δ) - 1) / c) * Complex.exp (c * t)
    rw [show Complex.exp (c * (t + δ)) =
        Complex.exp (c * t) * Complex.exp (c * δ) by
      rw [← Complex.exp_add]
      congr 1
      ring]
    ring
  · intro n hnmem
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hnmem).1
      omega
    rw [show (fun u : ℝ =>
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) =
      fun u : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * u) by
          funext u
          exact inv_nat_cpow_criticalLine_eq_exp hn0 u]
    apply Continuous.intervalIntegrable
    fun_prop

/-- The short critical-line Dirichlet polynomial inherits the standard
diagonal plus logarithmic-frequency-gap second-moment bound. -/
theorem integral_normSq_criticalLineShortDirichletPolynomial_le
    (δ : ℝ) (N : ℕ) {a b : ℝ} :
    (∫ t in a..b,
        Complex.normSq (criticalLineShortDirichletPolynomial δ N t)) ≤
      ∑ m ∈ Finset.Icc 2 N, ∑ n ∈ Finset.Icc 2 N,
        if m = n then
          (b - a) * Complex.normSq (criticalLineShortDirichletCoeff δ n)
        else
          2 * ‖criticalLineShortDirichletCoeff δ m‖ *
              ‖criticalLineShortDirichletCoeff δ n‖ /
            |Real.log m - Real.log n| := by
  have hfreq : ∀ m ∈ Finset.Icc 2 N, ∀ n ∈ Finset.Icc 2 N,
      m ≠ n → -Real.log m ≠ -Real.log n := by
    intro m hm n hn hmn hEq
    apply hmn
    have hlogEq : Real.log m = Real.log n := neg_injective hEq
    have hmpos : 0 < m := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hm).1
    have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
    exact_mod_cast Real.log_injOn_pos
      (show 0 < (m : ℝ) by exact_mod_cast hmpos)
      (show 0 < (n : ℝ) by exact_mod_cast hnpos) hlogEq
  simpa only [criticalLineShortDirichletPolynomial, neg_sub_neg,
    abs_sub_comm] using
    (MathlibAux.integral_normSq_exponentialPolynomial_le
      (Finset.Icc 2 N) (criticalLineShortDirichletCoeff δ)
        (fun n => -Real.log n) hfreq)

end HardyTheorem
