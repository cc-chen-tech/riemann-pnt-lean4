import HardyTheorem.SelbergSqrtZetaShortExpansion

open Complex Polynomial
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Uniform bounds for the square-root-zeta mollifier

The local binomial coefficients of `(1 - X)^(1/2)` have absolute value at
most one. Multiplicativity and the linear taper preserve this bound, giving
the uniform critical-line estimate `‖M_X(1/2 + it)‖ ≤ 2 * sqrt X`.
-/

private lemma abs_ringChoose_half_le_one (k : ℕ) :
    |Ring.choose (1 / 2 : ℝ) k| ≤ 1 := by
  have hfacprod (m : ℕ) :
      (∏ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ)) =
        (m.factorial : ℝ) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
        norm_num
        ring
  have hpoch :
      (descPochhammer ℤ k).smeval (1 / 2 : ℝ) =
        ∏ j ∈ Finset.range k, ((1 / 2 : ℝ) - j) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih,
          Finset.prod_range_succ, Polynomial.smeval_sub,
          Polynomial.smeval_X, Polynomial.smeval_natCast]
        norm_num
  have hfactor : ∀ j ∈ Finset.range k,
      |(1 / 2 : ℝ) - j| ≤ (j + 1 : ℕ) := by
    intro j _hj
    by_cases hj0 : j = 0
    · subst j
      norm_num
    · have hj1 : (1 : ℝ) ≤ j := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj0)
      rw [abs_of_nonpos (by linarith)]
      norm_num
      linarith
  have hprod :
      (∏ j ∈ Finset.range k, |(1 / 2 : ℝ) - j|) ≤
        (k.factorial : ℝ) := by
    calc
      (∏ j ∈ Finset.range k, |(1 / 2 : ℝ) - j|) ≤
          ∏ j ∈ Finset.range k, ((j + 1 : ℕ) : ℝ) := by
            exact Finset.prod_le_prod (fun j _ => abs_nonneg _) hfactor
      _ = (k.factorial : ℝ) := hfacprod k
  rw [Ring.choose_eq_smul, hpoch]
  simp only [smul_eq_mul, abs_mul, abs_inv, Finset.abs_prod]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ k.factorial)]
  calc
    (k.factorial : ℝ)⁻¹ *
          ∏ x ∈ Finset.range k, |(1 / 2 : ℝ) - ↑x| ≤
        (k.factorial : ℝ)⁻¹ * (k.factorial : ℝ) := by
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 1 := by
      exact inv_mul_cancel₀ (by positivity)

theorem abs_selbergSqrtZetaLocalCoeff_le_one (k : ℕ) :
    |selbergSqrtZetaLocalCoeff k| ≤ 1 := by
  rw [show selbergSqrtZetaLocalCoeff k =
      (-1 : ℝ) ^ k * Ring.choose (1 / 2 : ℝ) k by
    simp [selbergSqrtZetaLocalCoeff, selbergSqrtZetaEulerFactor]]
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
    abs_ringChoose_half_le_one k

theorem abs_selbergSqrtZetaCoeff_le_one (n : ℕ) :
    |selbergSqrtZetaCoeff n| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [selbergSqrtZetaCoeff_apply_ne_zero hn]
  simp only [Finsupp.prod, Finset.abs_prod]
  exact Finset.prod_le_one
    (fun p _ => abs_nonneg _)
    (fun p _ => abs_selbergSqrtZetaLocalCoeff_le_one
      (n.factorization p))

theorem abs_selbergSqrtZetaTaperedCoeff_le_one
    {X n : ℕ} (hX : 2 ≤ X) (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    |selbergSqrtZetaTaperedCoeff X n| ≤ 1 := by
  have hweight :=
    selbergMoebiusWeight_mem_Icc hX hn1 hnX
  rw [selbergSqrtZetaTaperedCoeff, abs_mul,
    abs_of_nonneg hweight.1]
  calc
    |selbergSqrtZetaCoeff n| *
          selbergMoebiusWeight X n ≤
        1 * selbergMoebiusWeight X n :=
      mul_le_mul_of_nonneg_right
        (abs_selbergSqrtZetaCoeff_le_one n) hweight.1
    _ ≤ 1 * 1 :=
      mul_le_mul_of_nonneg_left hweight.2 zero_le_one
    _ = 1 := one_mul 1

theorem selbergSqrtZetaMollifierMajorant_le_two_sqrt
    {X : ℕ} (hX : 2 ≤ X) :
    selbergSqrtZetaMollifierMajorant X ≤
      2 * Real.sqrt X := by
  unfold selbergSqrtZetaMollifierMajorant
  calc
    (∑ n ∈ Finset.Icc 1 X,
        |selbergSqrtZetaTaperedCoeff X n| *
          (Real.sqrt n)⁻¹) ≤
        ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      exact mul_le_of_le_one_left
        (inv_nonneg.mpr (Real.sqrt_nonneg n))
        (abs_selbergSqrtZetaTaperedCoeff_le_one hX hn1 hnX)
    _ ≤ 2 * Real.sqrt X :=
      sum_inv_sqrt_Icc_one_le_two_sqrt X

theorem norm_selbergSqrtZetaMollifier_criticalLine_le_two_sqrt
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    ‖selbergSqrtZetaMollifier X
        ((1 / 2 : ℂ) + I * t)‖ ≤
      2 * Real.sqrt X :=
  (norm_selbergSqrtZetaMollifier_criticalLine_le_majorant
    X t).trans
    (selbergSqrtZetaMollifierMajorant_le_two_sqrt hX)

end HardyTheorem
