import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators ArithmeticFunction.sigma

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The fourfold divisor function, written as the Dirichlet convolution of
two ordinary divisor-counting functions. -/
def fourfoldDivisorCount (n : ℕ) : ℕ :=
  (ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) n

/-- The threefold divisor function used in the summatory recurrence for the
fourfold divisor function. -/
def tripleDivisorCount (n : ℕ) : ℕ :=
  (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta) n

/-- Divisor pairs and divisors have the same cardinality. -/
theorem card_divisorsAntidiagonal_eq_card_divisors (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  have h := congrArg Finset.card (Nat.map_div_right_divisors (n := n))
  simpa using h.symm

/-- On every prime power, the square of the divisor count is bounded by the
fourfold divisor count. -/
theorem card_divisors_sq_le_fourfoldDivisorCount_prime_pow
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).divisors.card ^ 2 ≤ fourfoldDivisorCount (p ^ k) := by
  have hfour :
      fourfoldDivisorCount (p ^ k) =
        ∑ j ∈ Finset.range (k + 1), (j + 1) * (k - j + 1) := by
    unfold fourfoldDivisorCount
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal
        (fun a b => ArithmeticFunction.sigma 0 a *
          ArithmeticFunction.sigma 0 b),
      Nat.sum_divisors_prime_pow hp]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      Nat.pow_div hjk hp.pos,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  rw [show (p ^ k).divisors.card = k + 1 by
    simpa [Nat.divisors_prime_pow hp]]
  rw [hfour]
  calc
    (k + 1) ^ 2 = ∑ _j ∈ Finset.range (k + 1), (k + 1) := by
      simp [pow_two]
    _ ≤ ∑ j ∈ Finset.range (k + 1), (j + 1) * (k - j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hsub : k - j + j = k := Nat.sub_add_cancel hjk
      nlinarith [Nat.zero_le (j * (k - j))]

/-- For every positive integer, `d(n)^2` is bounded by the fourfold divisor
function.  This turns the Carlson coefficient problem into a fourfold-product
counting problem. -/
theorem card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount
    {n : ℕ} (hn : n ≠ 0) :
    n.divisorsAntidiagonal.card ^ 2 ≤ fourfoldDivisorCount n := by
  let d : ArithmeticFunction ℕ := ArithmeticFunction.sigma 0
  let d4 : ArithmeticFunction ℕ := d * d
  have hd : d.IsMultiplicative := ArithmeticFunction.isMultiplicative_sigma
  have hd4 : d4.IsMultiplicative := hd.mul hd
  rw [card_divisorsAntidiagonal_eq_card_divisors,
    ← ArithmeticFunction.sigma_zero_apply]
  change d n ^ 2 ≤ d4 n
  rw [hd.multiplicative_factorization d hn,
    hd4.multiplicative_factorization d4 hn]
  simp only [Finsupp.prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    have hpPrime : p.Prime := by
      apply Nat.prime_of_mem_primeFactors
      simpa [Nat.support_factorization] using hp
    have hprime :=
      card_divisors_sq_le_fourfoldDivisorCount_prime_pow hpPrime
        (n.factorization p)
    rw [← ArithmeticFunction.sigma_zero_apply] at hprime
    simpa [d, d4, fourfoldDivisorCount] using hprime

/-- A weighted divisor-square sum is bounded termwise by the corresponding
fourfold-divisor sum. -/
theorem weightedDivisorSquareSum_le_fourfoldDivisorCount
    {L U : ℕ} (hL : 0 < L) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) *
          ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 ≤
      ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
          ((n : ℝ) ^ (-sigma)) ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le hL (Finset.mem_Icc.mp hn).1
  have hcardNat := card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount hnpos.ne'
  have hcard :
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 ≤
        (fourfoldDivisorCount n : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((n : ℝ) + 1) *
        ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 =
      ((n : ℝ) + 1) *
        ((n.divisorsAntidiagonal.card : ℝ) ^ 2 *
          ((n : ℝ) ^ (-sigma)) ^ 2) := by ring
    _ ≤ ((n : ℝ) + 1) *
        ((fourfoldDivisorCount n : ℝ) * ((n : ℝ) ^ (-sigma)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
        ((n : ℝ) ^ (-sigma)) ^ 2 := by ring

/-- The prefix sum of the threefold divisor function is the divisor-count
sum weighted by integer quotients. -/
theorem sum_Ioc_tripleDivisorCount_eq_sum_div (Y : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Y, tripleDivisorCount n =
      ∑ n ∈ Finset.Ioc 0 Y,
        ArithmeticFunction.sigma 0 n * (Y / n) := by
  unfold tripleDivisorCount
  exact ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.sigma 0) Y

/-- The prefix sum of the fourfold divisor function is the threefold-divisor
sum weighted by integer quotients. -/
theorem sum_Ioc_fourfoldDivisorCount_eq_sum_div (Y : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Y, fourfoldDivisorCount n =
      ∑ n ∈ Finset.Ioc 0 Y, tripleDivisorCount n * (Y / n) := by
  have hsigma :
      ArithmeticFunction.sigma 0 =
        ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma,
      ArithmeticFunction.pow_zero_eq_zeta]
  have hfunctions :
      ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0 =
        (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta) *
          ArithmeticFunction.zeta := by
    rw [hsigma]
    simp only [mul_assoc]
  unfold fourfoldDivisorCount tripleDivisorCount
  rw [hfunctions]
  exact ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta) Y

end CarlsonZeroDensity
end PrimeNumberTheorem
