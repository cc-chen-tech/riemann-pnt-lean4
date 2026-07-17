import HardyTheorem.OscillatoryIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex Set

namespace HardyTheorem

private lemma inv_nat_cpow_criticalLine_eq_exp
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t) =
      ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_add _ _ hnC, one_div, mul_inv_rev]
  calc
    ((n : ℂ) ^ (I * t))⁻¹ * ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ =
        ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * ((n : ℂ) ^ (I * t))⁻¹ :=
      mul_comm _ _
    _ = ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t) := by
      congr 1
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_neg,
        ← Complex.natCast_log]
      congr 1
      ring

/-- A nonconstant term of the critical-line Dirichlet polynomial has an
interval integral bounded by its inverse logarithmic frequency. -/
theorem norm_integral_inv_nat_cpow_criticalLine_le
    {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} :
    ‖∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
      2 / (Real.sqrt n * Real.log n) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  let c : ℂ := -I * (Real.log n : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
      (ofReal_ne_zero.mpr hlog.ne')
  have hnorm_c : ‖c‖ = Real.log n := by
    dsimp [c]
    rw [norm_mul, norm_neg, norm_I, one_mul, norm_real,
      Real.norm_eq_abs, abs_of_pos hlog]
  have hexp_norm (t : ℝ) : ‖Complex.exp (c * t)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (c * (t : ℂ)).re = 0 := by
      dsimp [c]
      ring
    rw [hre, Real.exp_zero]
  have hosc : ‖∫ t in a..b, Complex.exp (c * t)‖ ≤ 2 / Real.log n := by
    rw [integral_exp_mul_complex hc]
    rw [norm_div, hnorm_c]
    apply (div_le_div_iff_of_pos_right hlog).2
    calc
      ‖Complex.exp (c * b) - Complex.exp (c * a)‖
          ≤ ‖Complex.exp (c * b)‖ + ‖Complex.exp (c * a)‖ := norm_sub_le _ _
      _ = 2 := by rw [hexp_norm, hexp_norm]; norm_num
  rw [show (fun t : ℝ => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      (fun t : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (c * t)) by
    funext t
    simpa [c] using inv_nat_cpow_criticalLine_eq_exp hn0 t]
  have hfactor :
      (∫ t in a..b,
        ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (c * t)) =
        ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          ∫ t in a..b, Complex.exp (c * t) :=
    intervalIntegral.integral_const_mul _ _
  rw [hfactor, norm_mul]
  have hhalf : ‖(n : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt n := by
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    simp [Real.sqrt_eq_rpow]
  rw [norm_inv, hhalf]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  rw [inv_eq_one_div]
  calc
    (1 / Real.sqrt n) * ‖∫ t in a..b, Complex.exp (c * t)‖
        ≤ (1 / Real.sqrt n) * (2 / Real.log n) :=
      mul_le_mul_of_nonneg_left hosc (by positivity)
    _ = 2 / (Real.sqrt n * Real.log n) := by field_simp

private lemma sum_inv_sqrt_Icc_two_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (Real.sqrt n)⁻¹ ≤
      Real.sqrt N * Real.sqrt (harmonic N : ℝ) := by
  let S := Finset.Icc 2 N
  have hcs := Real.sum_sqrt_mul_sqrt_le S
    (f := fun _ : ℕ => (1 : ℝ))
    (g := fun n : ℕ => ((n : ℝ))⁻¹)
    (fun _ => zero_le_one) (fun _ => by positivity)
  have hleft :
      (∑ n ∈ S, Real.sqrt (1 : ℝ) * Real.sqrt ((n : ℝ)⁻¹)) =
        ∑ n ∈ S, (Real.sqrt n)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Real.sqrt_one, one_mul, Real.sqrt_inv]
  have hsubset : S ⊆ Finset.Icc 1 N := by
    exact Finset.Icc_subset_Icc (by omega) le_rfl
  have hcard : (S.card : ℝ) ≤ N := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (by simp)
  have hrecip :
      (∑ n ∈ S, ((n : ℝ))⁻¹) ≤ (harmonic N : ℝ) := by
    calc
      (∑ n ∈ S, ((n : ℝ))⁻¹) ≤
          ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro n hn hnot
          positivity)
      _ = (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]
  rw [hleft] at hcs
  calc
    ∑ n ∈ Finset.Icc 2 N, (Real.sqrt n)⁻¹ =
        ∑ n ∈ S, (Real.sqrt n)⁻¹ := rfl
    _ ≤ Real.sqrt (∑ _n ∈ S, (1 : ℝ)) *
        Real.sqrt (∑ n ∈ S, ((n : ℝ))⁻¹) := hcs
    _ ≤ Real.sqrt N * Real.sqrt (harmonic N : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact mul_le_mul (Real.sqrt_le_sqrt hcard) (Real.sqrt_le_sqrt hrecip)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The nonconstant part of a finite critical-line Dirichlet polynomial has
sublinear-size interval integral.  The bound is uniform in the endpoints. -/
theorem norm_integral_criticalLineDirichletTail_le
    {N : ℕ} {a b : ℝ} :
    ‖∫ t in a..b, ∑ n ∈ Finset.Icc 2 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
      (2 / Real.log 2) *
        (Real.sqrt N * Real.sqrt (harmonic N : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsumint :
      (∫ t in a..b, ∑ n ∈ Finset.Icc 2 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      ∑ n ∈ Finset.Icc 2 N,
        ∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t) := by
    rw [intervalIntegral.integral_finset_sum]
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    rw [show (fun t : ℝ => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
        (fun t : ℝ => ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log n : ℂ)) * t)) by
      funext t
      exact inv_nat_cpow_criticalLine_eq_exp hn0 t]
    exact (by fun_prop : Continuous (fun t : ℝ =>
      ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
        Complex.exp ((-I * (Real.log n : ℂ)) * t))).intervalIntegrable
          (μ := MeasureTheory.volume) _ _
  rw [hsumint]
  calc
    ‖∑ n ∈ Finset.Icc 2 N,
        ∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ ≤
        ∑ n ∈ Finset.Icc 2 N,
          ‖∫ t in a..b, 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 2 N,
        (2 / Real.log 2) * (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
      have hlogmono : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
      refine (norm_integral_inv_nat_cpow_criticalLine_le hn2).trans ?_
      have hfreq : 2 / Real.log n ≤ 2 / Real.log 2 := by
        exact div_le_div_of_nonneg_left (by norm_num) hlog2 hlogmono
      rw [show 2 / (Real.sqrt n * Real.log n) =
          (2 / Real.log n) * (Real.sqrt n)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_right hfreq (by positivity)
    _ = (2 / Real.log 2) *
        (∑ n ∈ Finset.Icc 2 N, (Real.sqrt n)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (2 / Real.log 2) *
        (Real.sqrt N * Real.sqrt (harmonic N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_two_le N) (by positivity)

end HardyTheorem
