import HardyTheorem.SelbergSqrtZetaArithmetic

open Complex Polynomial
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# The positive square-root-zeta coefficient majorant

The coefficients of `ζ^(1/2)` are the Dirichlet convolution of zeta with
Selberg's `ζ^(-1/2)` coefficients.  This file proves coefficientwise
positivity and the majorization needed in Selberg's S13 estimate.
-/

/-- The nonnegative local coefficient of `(1 - X)^(-1/2)`. -/
noncomputable def selbergSqrtZetaInverseLocalCoeff (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), selbergSqrtZetaLocalCoeff j

private theorem selbergSqrtZetaLocalCoeff_eq_negOnePow_mul_choose
    (k : ℕ) :
    selbergSqrtZetaLocalCoeff k =
      (-1 : ℝ) ^ k * Ring.choose (1 / 2 : ℝ) k := by
  simp [selbergSqrtZetaLocalCoeff, selbergSqrtZetaEulerFactor]

theorem selbergSqrtZetaInverseLocalCoeff_eq (k : ℕ) :
    selbergSqrtZetaInverseLocalCoeff k =
      (-1 : ℝ) ^ k * Ring.choose (-1 / 2 : ℝ) k := by
  induction k with
  | zero => simp [selbergSqrtZetaInverseLocalCoeff]
  | succ k ih =>
      rw [selbergSqrtZetaInverseLocalCoeff, Finset.sum_range_succ]
      change selbergSqrtZetaInverseLocalCoeff k +
          selbergSqrtZetaLocalCoeff (k + 1) = _
      rw [ih,
        selbergSqrtZetaLocalCoeff_eq_negOnePow_mul_choose]
      have hpascal :=
        Ring.choose_succ_succ (R := ℝ) (-1 / 2 : ℝ) k
      norm_num at hpascal
      rw [hpascal, pow_succ]
      ring_nf

private theorem descPochhammer_smeval_eq_prod (a : ℝ) (k : ℕ) :
    (descPochhammer ℤ k).smeval a =
      ∏ j ∈ Finset.range k, (a - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih,
        Finset.prod_range_succ, Polynomial.smeval_sub,
        Polynomial.smeval_X, Polynomial.smeval_natCast]
      norm_num

private theorem prod_neg_half_sub_eq (k : ℕ) :
    (∏ j ∈ Finset.range k, ((-1 / 2 : ℝ) - j)) =
      (-1 : ℝ) ^ k *
        ∏ j ∈ Finset.range k, ((j : ℝ) + 1 / 2) := by
  calc
    (∏ j ∈ Finset.range k, ((-1 / 2 : ℝ) - j)) =
        ∏ j ∈ Finset.range k,
          ((-1 : ℝ) * ((j : ℝ) + 1 / 2)) := by
            apply Finset.prod_congr rfl
            intro j _hj
            ring
    _ = (∏ _j ∈ Finset.range k, (-1 : ℝ)) *
          ∏ j ∈ Finset.range k, ((j : ℝ) + 1 / 2) := by
            rw [Finset.prod_mul_distrib]
    _ = _ := by simp

theorem selbergSqrtZetaInverseLocalCoeff_eq_nonnegative_prod (k : ℕ) :
    selbergSqrtZetaInverseLocalCoeff k =
      (k.factorial : ℝ)⁻¹ *
        ∏ j ∈ Finset.range k, ((j : ℝ) + 1 / 2) := by
  rw [selbergSqrtZetaInverseLocalCoeff_eq, Ring.choose_eq_smul,
    descPochhammer_smeval_eq_prod, prod_neg_half_sub_eq]
  simp only [smul_eq_mul]
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℝ) ^ k *
        ((k.factorial : ℝ)⁻¹ *
          ((-1 : ℝ) ^ k *
            ∏ j ∈ Finset.range k, ((j : ℝ) + 1 / 2))) =
      ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
        ((k.factorial : ℝ)⁻¹ *
          ∏ j ∈ Finset.range k, ((j : ℝ) + 1 / 2)) := by ring
    _ = _ := by rw [hsign, one_mul]

theorem selbergSqrtZetaInverseLocalCoeff_nonneg (k : ℕ) :
    0 ≤ selbergSqrtZetaInverseLocalCoeff k := by
  rw [selbergSqrtZetaInverseLocalCoeff_eq_nonnegative_prod]
  exact mul_nonneg (by positivity) (Finset.prod_nonneg fun j _hj => by positivity)

theorem abs_selbergSqrtZetaLocalCoeff_le_inverseLocalCoeff (k : ℕ) :
    |selbergSqrtZetaLocalCoeff k| ≤
      selbergSqrtZetaInverseLocalCoeff k := by
  have hhalf : selbergSqrtZetaLocalCoeff k =
      (-1 : ℝ) ^ k * Ring.choose (1 / 2 : ℝ) k := by
    simp [selbergSqrtZetaLocalCoeff, selbergSqrtZetaEulerFactor]
  rw [hhalf, selbergSqrtZetaInverseLocalCoeff_eq_nonnegative_prod,
    Ring.choose_eq_smul, descPochhammer_smeval_eq_prod]
  simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)⁻¹),
    Finset.abs_prod]
  simp only [one_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod
  · intro j _hj
    exact abs_nonneg _
  · intro j _hj
    have hj : (0 : ℝ) ≤ j := by positivity
    by_cases h : (j : ℝ) ≤ 1 / 2
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonpos (by linarith)]
      linarith

/-- The arithmetic coefficients of `ζ^(1/2)`. -/
noncomputable def selbergSqrtZetaInverseCoeff : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * selbergSqrtZetaCoeff

theorem selbergSqrtZetaInverseCoeff_apply_prime_pow
    {p k : ℕ} (hp : p.Prime) :
    selbergSqrtZetaInverseCoeff (p ^ k) =
      selbergSqrtZetaInverseLocalCoeff k := by
  unfold selbergSqrtZetaInverseCoeff selbergSqrtZetaInverseLocalCoeff
  rw [mul_comm, ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j _hj
  exact selbergSqrtZetaCoeff_apply_prime_pow hp

theorem selbergSqrtZetaInverseCoeff_isMultiplicative :
    ArithmeticFunction.IsMultiplicative selbergSqrtZetaInverseCoeff :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    selbergSqrtZetaCoeff_isMultiplicative

theorem selbergSqrtZetaInverseCoeff_nonneg (n : ℕ) :
    0 ≤ selbergSqrtZetaInverseCoeff n := by
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
  apply Finset.prod_nonneg
  intro p hp
  have hpPrime : p.Prime := by
    apply Nat.prime_of_mem_primeFactors
    simpa only [Nat.support_factorization] using hp
  change 0 ≤ selbergSqrtZetaInverseCoeff (p ^ n.factorization p)
  rw [selbergSqrtZetaInverseCoeff_apply_prime_pow hpPrime]
  exact selbergSqrtZetaInverseLocalCoeff_nonneg _

theorem abs_selbergSqrtZetaCoeff_le_inverseCoeff (n : ℕ) :
    |selbergSqrtZetaCoeff n| ≤ selbergSqrtZetaInverseCoeff n := by
  by_cases hn : n = 0
  · subst n
    simp [selbergSqrtZetaInverseCoeff]
  have hcoeff : ArithmeticFunction.IsMultiplicative selbergSqrtZetaCoeff :=
    selbergSqrtZetaCoeff_isMultiplicative
  have hinv : ArithmeticFunction.IsMultiplicative
      selbergSqrtZetaInverseCoeff :=
    selbergSqrtZetaInverseCoeff_isMultiplicative
  rw [show selbergSqrtZetaCoeff n =
      n.factorization.prod fun p k => selbergSqrtZetaCoeff (p ^ k) from
    hcoeff.multiplicative_factorization selbergSqrtZetaCoeff hn,
    show selbergSqrtZetaInverseCoeff n =
      n.factorization.prod fun p k =>
        selbergSqrtZetaInverseCoeff (p ^ k) from
      hinv.multiplicative_factorization selbergSqrtZetaInverseCoeff hn]
  simp only [Finsupp.prod, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro p _hp
    exact abs_nonneg _
  · intro p hp
    have hpPrime : p.Prime := by
      apply Nat.prime_of_mem_primeFactors
      simpa only [Nat.support_factorization] using hp
    rw [selbergSqrtZetaCoeff_apply_prime_pow hpPrime,
      selbergSqrtZetaInverseCoeff_apply_prime_pow hpPrime]
    exact abs_selbergSqrtZetaLocalCoeff_le_inverseLocalCoeff _

/-- Squaring the positive majorant coefficients recovers arithmetic zeta. -/
theorem selbergSqrtZetaInverseCoeff_mul_self :
    selbergSqrtZetaInverseCoeff * selbergSqrtZetaInverseCoeff =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
  unfold selbergSqrtZetaInverseCoeff
  calc
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * selbergSqrtZetaCoeff) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * selbergSqrtZetaCoeff) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
          (selbergSqrtZetaCoeff * selbergSqrtZetaCoeff) := by ac_rfl
    _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) *
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
            rw [selbergSqrtZetaCoeff_mul_self]
    _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
      rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]

end HardyTheorem
