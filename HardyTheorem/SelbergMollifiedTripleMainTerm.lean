import HardyTheorem.SelbergMollifiedTripleConstant
import HardyTheorem.SelbergMollifiedCoefficientArithmetic

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Closed form of the Selberg main coefficient

The zero-frequency coefficient of `P_N M_X * conj(M_X)` is the main term of
Selberg's mollified first moment.  For `X ≤ N` this file evaluates it in
closed form.  Collecting the admissible pairs `(m,n)` by their product
`k = m * n ≤ X`, the tapered Moebius divisor sum collapses to
`vonMangoldt k / log X`, and the joint Moebius–von-Mangoldt support
collapses to the primes.  The coefficient is therefore exactly

```
1 - (∑_{p ≤ X} (1 - log p / log X) * log p / p) / log X
  = 1 - (∑_{p ≤ X} log p / p) / log X
      + (∑_{p ≤ X} (log p)^2 / p) / (log X)^2 .
```

The remaining analytic input for Selberg's first-moment lower bound is now
exactly a Mertens-type estimate for the two prime sums above; no such
estimate is claimed in this file.
-/

/-- On the constant-pair finset, fixing the product `k ≤ X ≤ N` gives exactly
all positive multiplicative factorizations of `k`. -/
theorem selbergMollifiedTripleConstantPairs_filter_prod_eq_divisorsAntidiagonal
    {N X k : ℕ} (hNX : X ≤ N) (hk1 : 1 ≤ k) (hkX : k ≤ X) :
    (selbergMollifiedTripleConstantPairs N X).filter
        (fun p => p.1 * p.2 = k) = k.divisorsAntidiagonal := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨-, hprod⟩
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, by omega⟩
  · intro hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hk0⟩
    have hp1 : 1 ≤ p.1 := by
      by_contra h
      rw [not_le, Nat.lt_one_iff] at h
      rw [h, Nat.zero_mul] at hprod
      omega
    have hp2 : 1 ≤ p.2 := by
      by_contra h
      rw [not_le, Nat.lt_one_iff] at h
      rw [h, Nat.mul_zero] at hprod
      omega
    have hp1k : p.1 ≤ k := by
      calc p.1 = p.1 * 1 := (Nat.mul_one p.1).symm
      _ ≤ p.1 * p.2 := Nat.mul_le_mul_left p.1 hp2
      _ = k := hprod
    have hp2k : p.2 ≤ k := by
      calc p.2 = 1 * p.2 := (Nat.one_mul p.2).symm
      _ ≤ p.1 * p.2 := Nat.mul_le_mul_right p.2 hp1
      _ = k := hprod
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hp1, hp1k.trans (hkX.trans hNX)⟩,
            Finset.mem_Icc.mpr ⟨hp2, hp2k.trans hkX⟩⟩,
          by omega⟩,
        hprod⟩

/-- Collecting the constant-pair sum by the product `k = m * n` gives the
divisor-sum form of the main coefficient. -/
theorem selbergMollifiedTripleConstantPairs_sum_eq_divisorSum
    {N X : ℕ} (hNX : X ≤ N) :
    ∑ p ∈ selbergMollifiedTripleConstantPairs N X,
        selbergMoebiusCoeff X p.2 * selbergMoebiusCoeff X (p.1 * p.2) /
          (p.1 * p.2 : ℝ) =
      ∑ k ∈ Finset.Icc 1 X, (selbergMoebiusCoeff X k / (k : ℝ)) *
        ∑ n ∈ k.divisors, selbergMoebiusCoeff X n := by
  classical
  have hmaps : ∀ p ∈ selbergMollifiedTripleConstantPairs N X,
      p.1 * p.2 ∈ Finset.Icc 1 X := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpair, hle⟩
    rcases Finset.mem_product.mp hpair with ⟨hm, hn⟩
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1, hle⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => selbergMoebiusCoeff X p.2 * selbergMoebiusCoeff X (p.1 * p.2) /
      (p.1 * p.2 : ℝ))]
  apply Finset.sum_congr rfl
  intro k hk
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hkX⟩
  rw [selbergMollifiedTripleConstantPairs_filter_prod_eq_divisorsAntidiagonal
    hNX hk1 hkX]
  rw [Nat.sum_divisorsAntidiagonal' (fun m n =>
    selbergMoebiusCoeff X n * selbergMoebiusCoeff X (m * n) / (m * n : ℝ))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hkn : k / n * n = k := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hn)
  rw [← Nat.cast_mul, hkn]
  ring

/-- The divisor-sum main coefficient splits off its unit term, leaving the
von-Mangoldt-weighted sum over `2 ≤ k ≤ X`. -/
theorem selbergMollifiedTripleMainTerm_divisorSum_eq_one_add {X : ℕ}
    (hX : 1 ≤ X) :
    ∑ k ∈ Finset.Icc 1 X, (selbergMoebiusCoeff X k / (k : ℝ)) *
        ∑ n ∈ k.divisors, selbergMoebiusCoeff X n =
      1 + (∑ k ∈ Finset.Icc 2 X,
          selbergMoebiusCoeff X k * ArithmeticFunction.vonMangoldt k /
            (k : ℝ)) / Real.log X := by
  have hsplit : Finset.Icc 1 X = insert 1 (Finset.Icc 2 X) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have h1 : (selbergMoebiusCoeff X 1 / ((1 : ℕ) : ℝ)) *
      ∑ n ∈ (1 : ℕ).divisors, selbergMoebiusCoeff X n = 1 := by
    simp [Nat.divisors_one]
  have hterm : ∀ k ∈ Finset.Icc 2 X,
      (selbergMoebiusCoeff X k / (k : ℝ)) *
          ∑ n ∈ k.divisors, selbergMoebiusCoeff X n =
        (selbergMoebiusCoeff X k * ArithmeticFunction.vonMangoldt k /
          (k : ℝ)) / Real.log X := by
    intro k hk
    have hk2 : 1 < k := (Finset.mem_Icc.mp hk).1
    rw [sum_selbergMoebiusCoeff_divisors_eq_vonMangoldt_div_log hk2]
    ring
  rw [hsplit, Finset.sum_insert (by simp), h1, Finset.sum_congr rfl hterm,
    ← Finset.sum_div]

/-- On a prime, the tapered Moebius coefficient times `vonMangoldt` is the
negative logarithmic weight. -/
theorem selbergMoebiusCoeff_mul_vonMangoldt_of_prime {X p : ℕ}
    (hp : p.Prime) :
    selbergMoebiusCoeff X p * ArithmeticFunction.vonMangoldt p =
      -(selbergMoebiusWeight X p * Real.log p) := by
  have hmu : (ArithmeticFunction.moebius p : ℝ) = -1 := by
    exact_mod_cast ArithmeticFunction.moebius_apply_prime hp
  rw [selbergMoebiusCoeff, ArithmeticFunction.vonMangoldt_apply_prime hp, hmu]
  ring

/-- A non-prime has Moebius-von-Mangoldt product zero: prime powers with
exponent at least two are not squarefree. -/
theorem selbergMoebiusCoeff_mul_vonMangoldt_eq_zero_of_not_prime {X k : ℕ}
    (h : ¬ k.Prime) :
    selbergMoebiusCoeff X k * ArithmeticFunction.vonMangoldt k = 0 := by
  by_cases hpp : IsPrimePow k
  · obtain ⟨p, j, hp, hj0, hjk⟩ := hpp
    have hpN : p.Prime := Nat.prime_iff.mpr hp
    have hjp : j ≠ 1 := by
      intro hj1
      apply h
      have hkpeq : k = p := by rw [← hjk, hj1, pow_one]
      rw [hkpeq]
      exact hpN
    have hnotsq : ¬ Squarefree k := by
      intro hsq
      rw [← hjk] at hsq
      rw [Nat.squarefree_pow_iff hp.ne_one hj0.ne'] at hsq
      exact hjp hsq.2
    have hmu : (ArithmeticFunction.moebius k : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        hnotsq
    rw [selbergMoebiusCoeff, hmu]
    ring
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    ring

/-- The von-Mangoldt-weighted sum over `2 ≤ k ≤ X` collapses to the negative
weighted prime sum. -/
theorem selbergMollifiedTripleMainTerm_vonMangoldtSum_eq_neg_primeSum
    (X : ℕ) :
    ∑ k ∈ Finset.Icc 2 X,
        selbergMoebiusCoeff X k * ArithmeticFunction.vonMangoldt k /
          (k : ℝ) =
      -∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        selbergMoebiusWeight X p * Real.log p / (p : ℝ) := by
  rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hpk : k.Prime
  · rw [if_pos hpk,
      selbergMoebiusCoeff_mul_vonMangoldt_of_prime hpk]
    ring
  · rw [if_neg hpk,
      selbergMoebiusCoeff_mul_vonMangoldt_eq_zero_of_not_prime hpk]
    ring

/-- The closed prime-sum form of the Selberg main coefficient: the
zero-frequency collected coefficient of `P_N M_X * conj(M_X)` is exactly one
minus the linearly weighted prime logarithm sum, normalized by `log X`. -/
theorem selbergMollifiedTripleCollectedCoeff_one_eq_primeMainTerm
    {N X : ℕ} (hX : 1 ≤ X) (hNX : X ≤ N) :
    selbergMollifiedTripleCollectedCoeff N X 1 =
      ((1 - (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
            selbergMoebiusWeight X p * Real.log p / (p : ℝ)) /
          Real.log X : ℝ) : ℂ) := by
  rw [selbergMollifiedTripleCollectedCoeff_one_eq_real_sum,
    selbergMollifiedTripleConstantPairs_sum_eq_divisorSum hNX,
    selbergMollifiedTripleMainTerm_divisorSum_eq_one_add hX,
    selbergMollifiedTripleMainTerm_vonMangoldtSum_eq_neg_primeSum]
  congr 1
  ring

/-- The expanded Mertens form of the Selberg main coefficient: one minus the
prime `log p / p` average plus the prime `(log p)^2 / p` average at the
second order.  A Mertens-type bound for these two sums is the remaining
analytic input for Selberg's first-moment lower bound. -/
theorem selbergMollifiedTripleCollectedCoeff_one_eq_mertensForm
    {N X : ℕ} (hX : 1 ≤ X) (hNX : X ≤ N) :
    selbergMollifiedTripleCollectedCoeff N X 1 =
      ((1 - (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
            (Real.log p) / (p : ℝ)) / Real.log X +
        (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
            (Real.log p) ^ 2 / (p : ℝ)) / Real.log X ^ 2 : ℝ) : ℂ) := by
  rw [selbergMollifiedTripleCollectedCoeff_one_eq_primeMainTerm hX hNX]
  congr 1
  have hterm : ∀ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
      selbergMoebiusWeight X p * Real.log p / (p : ℝ) =
        (Real.log p) / (p : ℝ) -
          ((Real.log p) ^ 2 / (p : ℝ)) / Real.log X := by
    intro p hp
    rw [selbergMoebiusWeight]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div]
  ring

end HardyTheorem
