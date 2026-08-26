import HardyTheorem.SelbergSqrtZetaInverseMajorant

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# A lightweight uniform bound for Selberg's square-root coefficients

This module deliberately depends only on the arithmetic Euler-product layer.  The positive local
coefficient of `(1 - X)^(-1/2)` is a product of factors `(j + 1/2)/(j + 1)`, hence is at most one.
Multiplicativity gives the same bound globally, and the signed coefficient is dominated by this
positive majorant.
-/

theorem selbergSqrtZetaInverseLocalCoeff_le_one (k : ℕ) :
    selbergSqrtZetaInverseLocalCoeff k ≤ 1 := by
  have hfacprod (m : ℕ) :
      (∏ j ∈ Finset.range m, ((j + 1 : ℕ) : ℝ)) =
        (m.factorial : ℝ) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
        norm_num
        ring
  have hprod :
      (∏ j ∈ Finset.range k, ((j : ℝ) + 1 / 2)) ≤
        (k.factorial : ℝ) := by
    rw [← hfacprod k]
    apply Finset.prod_le_prod
    · intro j _hj
      positivity
    · intro j _hj
      norm_num
  rw [selbergSqrtZetaInverseLocalCoeff_eq_nonnegative_prod]
  calc
    (k.factorial : ℝ)⁻¹ *
          ∏ j ∈ Finset.range k, ((j : ℝ) + 1 / 2) ≤
        (k.factorial : ℝ)⁻¹ * (k.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)

theorem selbergSqrtZetaInverseCoeff_le_one (n : ℕ) :
    selbergSqrtZetaInverseCoeff n ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [selbergSqrtZetaInverseCoeff]
  have hmult : ArithmeticFunction.IsMultiplicative
      selbergSqrtZetaInverseCoeff :=
    selbergSqrtZetaInverseCoeff_isMultiplicative
  rw [show selbergSqrtZetaInverseCoeff n =
      n.factorization.prod fun p k =>
        selbergSqrtZetaInverseCoeff (p ^ k) from
    hmult.multiplicative_factorization selbergSqrtZetaInverseCoeff hn]
  apply Finset.prod_le_one
  · intro p hp
    have hpPrime : p.Prime := by
      apply Nat.prime_of_mem_primeFactors
      simpa only [Nat.support_factorization] using hp
    change 0 ≤ selbergSqrtZetaInverseCoeff
      (p ^ n.factorization p)
    rw [selbergSqrtZetaInverseCoeff_apply_prime_pow hpPrime]
    exact selbergSqrtZetaInverseLocalCoeff_nonneg _
  · intro p hp
    have hpPrime : p.Prime := by
      apply Nat.prime_of_mem_primeFactors
      simpa only [Nat.support_factorization] using hp
    change selbergSqrtZetaInverseCoeff
      (p ^ n.factorization p) ≤ 1
    rw [selbergSqrtZetaInverseCoeff_apply_prime_pow hpPrime]
    exact selbergSqrtZetaInverseLocalCoeff_le_one _

theorem abs_selbergSqrtZetaCoeff_le_one_light (n : ℕ) :
    |selbergSqrtZetaCoeff n| ≤ 1 :=
  (abs_selbergSqrtZetaCoeff_le_inverseCoeff n).trans
    (selbergSqrtZetaInverseCoeff_le_one n)

end HardyTheorem
