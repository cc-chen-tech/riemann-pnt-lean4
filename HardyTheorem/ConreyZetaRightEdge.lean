import HardyTheorem.ConreyMollifierRightEdge

/-!
# Infinite zeta tail on Conrey's moving right edge

This file proves the infinite-Dirichlet-series analogue of the finite
mollifier right-tail estimate.  It supplies only the quantitative zeta
input on `Re s = 2 log L`; it does not assert the `V₁` or global
right-vertical estimate.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- Integral comparison for the zeta tail beginning at `n = 2`. -/
theorem tsum_nat_add_two_rpow_le_rightTail
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, (n + 2 : ℝ) ^ (-sigma)) ≤
      (2 : ℝ) ^ (-sigma) * (1 + 2 / (sigma - 1)) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact Real.rpow_nonneg (by positivity) _
  · intro N
    by_cases hN : N = 0
    · subst N
      simp
      positivity
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hsumEq :
        (∑ n ∈ Finset.range N, (n + 2 : ℝ) ^ (-sigma)) =
          ∑ n ∈ Finset.Icc 2 (N + 1), (n : ℝ) ^ (-sigma) := by
      rw [show Finset.Icc 2 (N + 1) = Finset.Ico 2 (N + 2) by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega]
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      simp [add_comm]
    rw [hsumEq]
    have hraw :=
      PrimeNumberTheorem.CarlsonZeroDensity.sum_Icc_rpow_le_add_div_of_lt_neg_one
        (L := 2) (U := N + 1) (by omega) (by omega)
        (q := -sigma) (by linarith)
    have hden : 0 < sigma - 1 := by linarith
    have hUpow : 0 ≤ (N + 1 : ℝ) ^ (-sigma + 1) :=
      Real.rpow_nonneg (by positivity) _
    have hfrac :
        ((N + 1 : ℝ) ^ (-sigma + 1) - (2 : ℝ) ^ (-sigma + 1)) /
            (-sigma + 1) ≤
          (2 : ℝ) ^ (-sigma + 1) / (sigma - 1) := by
      have heq :
          ((N + 1 : ℝ) ^ (-sigma + 1) - (2 : ℝ) ^ (-sigma + 1)) /
              (-sigma + 1) =
            ((2 : ℝ) ^ (-sigma + 1) - (N + 1 : ℝ) ^ (-sigma + 1)) /
              (sigma - 1) := by
        rw [show -sigma + 1 = -(sigma - 1) by ring, div_neg, neg_sub]
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right (by linarith) hden.le
    calc
      (∑ n ∈ Finset.Icc 2 (N + 1), (n : ℝ) ^ (-sigma)) ≤
          (2 : ℝ) ^ (-sigma) +
            ((N + 1 : ℝ) ^ (-sigma + 1) - (2 : ℝ) ^ (-sigma + 1)) /
              (-sigma + 1) := by simpa using hraw
      _ ≤ (2 : ℝ) ^ (-sigma) +
            (2 : ℝ) ^ (-sigma + 1) / (sigma - 1) :=
        add_le_add le_rfl hfrac
      _ = (2 : ℝ) ^ (-sigma) * (1 + 2 / (sigma - 1)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        field_simp [hden.ne']

private theorem riemannZeta_sub_one_eq_tail {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s - 1 = ∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s := by
  have hseries : Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    rw [show (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) =
      fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s by
        funext n
        norm_num]
    exact (summable_nat_add_iff 1).mpr
      ((Complex.summable_one_div_nat_cpow).mpr hs)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hseries.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, one_cpow, div_one, add_sub_cancel_left]
  congr 1
  funext n
  congr 2
  push_cast
  ring

private theorem summable_zeta_tail {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => 1 / (n + 2 : ℂ) ^ s) := by
  have hbase := (Complex.summable_one_div_nat_cpow).mpr hs
  convert (summable_nat_add_iff 2).mpr hbase using 1 with n
  all_goals (first | rfl | norm_num)

/-- The absolutely convergent zeta Dirichlet series is quantitatively close
to its constant term throughout the half-plane `Re s > 1`. -/
theorem norm_riemannZeta_sub_one_le_rightTail
    {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s - 1‖ ≤
      (2 : ℝ) ^ (-s.re) * (1 + 2 / (s.re - 1)) := by
  rw [riemannZeta_sub_one_eq_tail hs]
  calc
    ‖∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s‖ ≤
        ∑' n : ℕ, ‖1 / (n + 2 : ℂ) ^ s‖ :=
      norm_tsum_le_tsum_norm (summable_zeta_tail hs).norm
    _ = ∑' n : ℕ, (n + 2 : ℝ) ^ (-s.re) := by
      apply tsum_congr
      intro n
      have hbase : (n + 2 : ℂ) = ((n + 2 : ℝ) : ℂ) := by norm_num
      rw [norm_div, norm_one, hbase, Complex.norm_cpow_eq_rpow_re_of_pos]
      · rw [one_div, ← Real.rpow_neg (by positivity)]
      · positivity
    _ ≤ (2 : ℝ) ^ (-s.re) * (1 + 2 / (s.re - 1)) :=
      tsum_nat_add_two_rpow_le_rightTail hs

/-- On `Re s = 2 log L`, the zeta Dirichlet series is within `3 / L` of
its constant term, uniformly in height. -/
theorem norm_riemannZeta_movingRight_sub_one_le
    {L : ℝ} (hL : Real.exp 1 ≤ L) {s : ℂ}
    (hre : s.re = 2 * Real.log L) :
    ‖riemannZeta s - 1‖ ≤ 3 / L := by
  have hLpos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hlogL : 1 ≤ Real.log L := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos 1) hLpos hL
    simpa only [Real.log_exp] using hmono
  have hs : 1 < s.re := by rw [hre]; linarith
  have htail := norm_riemannZeta_sub_one_le_rightTail hs
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9 |>.le
  have hpow :
      (2 : ℝ) ^ (-(2 * Real.log L)) ≤ 1 / L := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hexponent :
        Real.log 2 * (-(2 * Real.log L)) ≤ -Real.log L := by
      have hlogL0 : 0 ≤ Real.log L := zero_le_one.trans hlogL
      nlinarith [mul_nonneg (sub_nonneg.mpr hlogTwo) hlogL0]
    calc
      Real.exp (Real.log 2 * (-(2 * Real.log L))) ≤
          Real.exp (-Real.log L) := Real.exp_le_exp.mpr hexponent
      _ = 1 / L := by
        rw [Real.exp_neg, Real.exp_log hLpos]
        simp only [one_div]
  have hfactor :
      1 + 2 / (2 * Real.log L - 1) ≤ (3 : ℝ) := by
    have hden : 0 < 2 * Real.log L - 1 := by linarith
    have hdiv : 2 / (2 * Real.log L - 1) ≤ (2 : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith
    linarith
  have hfactor0 : 0 ≤ 1 + 2 / (2 * Real.log L - 1) := by
    have : 0 < 2 * Real.log L - 1 := by linarith
    positivity
  have hLinv0 : 0 ≤ 1 / L := by positivity
  calc
    ‖riemannZeta s - 1‖ ≤
        (2 : ℝ) ^ (-(2 * Real.log L)) *
          (1 + 2 / (2 * Real.log L - 1)) := by simpa [hre] using htail
    _ ≤ (1 / L) * 3 := mul_le_mul hpow hfactor hfactor0 hLinv0
    _ = 3 / L := by ring

end HardyTheorem
