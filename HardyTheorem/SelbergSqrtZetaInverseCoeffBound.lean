import HardyTheorem.SelbergSqrtZetaCoeffBound

/-!
# Bounds for the inverse local square-root-zeta factor

The partial sums of the coefficients of `(1 - X)^(1/2)` are the
coefficients of `(1 - X)^(-1/2)`.  A generalized Pascal recurrence gives
the exact finite identity, while the product formula for the generalized
binomial coefficient gives a uniform bound by one.
-/

open Complex Polynomial
open scoped BigOperators

namespace HardyTheorem

private theorem selbergSqrtZetaLocalCoeff_eq_negOnePow_mul_choose
    (k : ℕ) :
    selbergSqrtZetaLocalCoeff k =
      (-1 : ℝ) ^ k * Ring.choose (1 / 2 : ℝ) k := by
  simp [selbergSqrtZetaLocalCoeff, selbergSqrtZetaEulerFactor]

/-- Finite binomial summation for the local square-root-zeta coefficients. -/
theorem sum_range_selbergSqrtZetaLocalCoeff_eq
    (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), selbergSqrtZetaLocalCoeff j) =
      (-1 : ℝ) ^ k * Ring.choose (-1 / 2 : ℝ) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih,
        selbergSqrtZetaLocalCoeff_eq_negOnePow_mul_choose]
      have hpascal :=
        Ring.choose_succ_succ (R := ℝ) (-1 / 2 : ℝ) k
      norm_num at hpascal
      rw [hpascal, pow_succ]
      ring_nf

private lemma abs_ringChoose_neg_half_le_one (k : ℕ) :
    |Ring.choose (-1 / 2 : ℝ) k| ≤ 1 := by
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
      (descPochhammer ℤ k).smeval (-1 / 2 : ℝ) =
        ∏ j ∈ Finset.range k, ((-1 / 2 : ℝ) - j) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih,
          Finset.prod_range_succ, Polynomial.smeval_sub,
          Polynomial.smeval_X, Polynomial.smeval_natCast]
        norm_num
  have hfactor : ∀ j ∈ Finset.range k,
      |(-1 / 2 : ℝ) - j| ≤ (j + 1 : ℕ) := by
    intro j _hj
    have hj : (0 : ℝ) ≤ j := by positivity
    rw [abs_of_nonpos (by linarith)]
    norm_num
  have hprod :
      (∏ j ∈ Finset.range k, |(-1 / 2 : ℝ) - j|) ≤
        (k.factorial : ℝ) := by
    calc
      (∏ j ∈ Finset.range k, |(-1 / 2 : ℝ) - j|) ≤
          ∏ j ∈ Finset.range k, ((j + 1 : ℕ) : ℝ) := by
            exact Finset.prod_le_prod (fun j _ => abs_nonneg _) hfactor
      _ = (k.factorial : ℝ) := hfacprod k
  rw [Ring.choose_eq_smul, hpoch]
  simp only [smul_eq_mul, abs_mul, abs_inv, Finset.abs_prod]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ k.factorial)]
  calc
    (k.factorial : ℝ)⁻¹ *
          ∏ x ∈ Finset.range k, |(-1 / 2 : ℝ) - ↑x| ≤
        (k.factorial : ℝ)⁻¹ * (k.factorial : ℝ) := by
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 1 := by
      exact inv_mul_cancel₀ (by positivity)

/-- Every partial sum of the local square-root-zeta coefficients has absolute
value at most one. -/
theorem abs_sum_range_selbergSqrtZetaLocalCoeff_le_one
    (k : ℕ) :
    |∑ j ∈ Finset.range (k + 1), selbergSqrtZetaLocalCoeff j| ≤ 1 := by
  rw [sum_range_selbergSqrtZetaLocalCoeff_eq, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul]
  exact abs_ringChoose_neg_half_le_one k

/-- At a prime power, convolution with arithmetic zeta is the partial sum of
the local square-root-zeta coefficients. -/
theorem zeta_mul_selbergSqrtZetaCoeff_apply_prime_pow
    {p k : ℕ} (hp : p.Prime) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaCoeff) (p ^ k)) =
      ∑ j ∈ Finset.range (k + 1), selbergSqrtZetaLocalCoeff j := by
  rw [mul_comm, ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j _hj
  exact selbergSqrtZetaCoeff_apply_prime_pow hp

/-- The arithmetic coefficients of `zeta^(1/2)` obtained by convolving zeta
with the square-root-zeta mollifier coefficients have absolute value at most
one. -/
theorem abs_zeta_mul_selbergSqrtZetaCoeff_le_one
    (n : ℕ) :
    |(((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaCoeff) n)| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hmult : ArithmeticFunction.IsMultiplicative
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaCoeff) :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul
      selbergSqrtZetaCoeff_isMultiplicative
  rw [hmult.multiplicative_factorization _ hn]
  simp only [Finsupp.prod, Finset.abs_prod]
  apply Finset.prod_le_one
  · intro p _hp
    exact abs_nonneg _
  · intro p hp
    have hpPrime : p.Prime := by
      apply Nat.prime_of_mem_primeFactors
      simpa only [Nat.support_factorization] using hp
    rw [zeta_mul_selbergSqrtZetaCoeff_apply_prime_pow hpPrime]
    exact abs_sum_range_selbergSqrtZetaLocalCoeff_le_one _

end HardyTheorem
