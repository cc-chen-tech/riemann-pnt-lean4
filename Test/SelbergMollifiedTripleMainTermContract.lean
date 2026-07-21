import HardyTheorem.SelbergMollifiedTripleMainTerm

open scoped BigOperators

namespace HardyTheorem

/-!
# Contract test for the Selberg main-coefficient closed form

Checks the factorization reindexing, the prime collapse, the closed prime-sum
form, the expanded Mertens form, and a concrete numeric evaluation at
`X = N = 2`, where the mollifier is trivial and the main coefficient is one.
-/

example {N X k : ℕ} (hNX : X ≤ N) (hk1 : 1 ≤ k) (hkX : k ≤ X) :
    (selbergMollifiedTripleConstantPairs N X).filter
        (fun p => p.1 * p.2 = k) = k.divisorsAntidiagonal :=
  selbergMollifiedTripleConstantPairs_filter_prod_eq_divisorsAntidiagonal
    hNX hk1 hkX

example {N X : ℕ} (hNX : X ≤ N) :
    ∑ p ∈ selbergMollifiedTripleConstantPairs N X,
        selbergMoebiusCoeff X p.2 * selbergMoebiusCoeff X (p.1 * p.2) /
          (p.1 * p.2 : ℝ) =
      ∑ k ∈ Finset.Icc 1 X, (selbergMoebiusCoeff X k / (k : ℝ)) *
        ∑ n ∈ k.divisors, selbergMoebiusCoeff X n :=
  selbergMollifiedTripleConstantPairs_sum_eq_divisorSum hNX

example {X : ℕ} (hX : 1 ≤ X) :
    ∑ k ∈ Finset.Icc 1 X, (selbergMoebiusCoeff X k / (k : ℝ)) *
        ∑ n ∈ k.divisors, selbergMoebiusCoeff X n =
      1 + (∑ k ∈ Finset.Icc 2 X,
          selbergMoebiusCoeff X k * ArithmeticFunction.vonMangoldt k /
            (k : ℝ)) / Real.log X :=
  selbergMollifiedTripleMainTerm_divisorSum_eq_one_add hX

example {X p : ℕ} (hp : p.Prime) :
    selbergMoebiusCoeff X p * ArithmeticFunction.vonMangoldt p =
      -(selbergMoebiusWeight X p * Real.log p) :=
  selbergMoebiusCoeff_mul_vonMangoldt_of_prime hp

example {X k : ℕ} (h : ¬ k.Prime) :
    selbergMoebiusCoeff X k * ArithmeticFunction.vonMangoldt k = 0 :=
  selbergMoebiusCoeff_mul_vonMangoldt_eq_zero_of_not_prime h

example (X : ℕ) :
    ∑ k ∈ Finset.Icc 2 X,
        selbergMoebiusCoeff X k * ArithmeticFunction.vonMangoldt k /
          (k : ℝ) =
      -∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        selbergMoebiusWeight X p * Real.log p / (p : ℝ) :=
  selbergMollifiedTripleMainTerm_vonMangoldtSum_eq_neg_primeSum X

example {N X : ℕ} (hX : 1 ≤ X) (hNX : X ≤ N) :
    selbergMollifiedTripleCollectedCoeff N X 1 =
      ((1 - (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
            selbergMoebiusWeight X p * Real.log p / (p : ℝ)) /
          Real.log X : ℝ) : ℂ) :=
  selbergMollifiedTripleCollectedCoeff_one_eq_primeMainTerm hX hNX

example {N X : ℕ} (hX : 1 ≤ X) (hNX : X ≤ N) :
    selbergMollifiedTripleCollectedCoeff N X 1 =
      ((1 - (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
            (Real.log p) / (p : ℝ)) / Real.log X +
        (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
            (Real.log p) ^ 2 / (p : ℝ)) / Real.log X ^ 2 : ℝ) : ℂ) :=
  selbergMollifiedTripleCollectedCoeff_one_eq_mertensForm hX hNX

/-- At `X = N = 2` the linear cutoff kills the only prime term, so the main
coefficient of the trivial mollifier is exactly one. -/
example : selbergMollifiedTripleCollectedCoeff 2 2 1 = 1 := by
  rw [selbergMollifiedTripleCollectedCoeff_one_eq_primeMainTerm
    (N := 2) (X := 2) (by norm_num) le_rfl]
  have hset : (Finset.Icc 2 2).filter Nat.Prime = {2} := by decide
  have hlog2 : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
    have h : Real.log (2 : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    exact_mod_cast h
  have hw22 : selbergMoebiusWeight 2 2 = 0 := by
    rw [selbergMoebiusWeight, div_self hlog2, sub_self]
  rw [hset, Finset.sum_singleton, hw22]
  norm_num

#print axioms selbergMollifiedTripleConstantPairs_filter_prod_eq_divisorsAntidiagonal
#print axioms selbergMollifiedTripleConstantPairs_sum_eq_divisorSum
#print axioms selbergMollifiedTripleMainTerm_divisorSum_eq_one_add
#print axioms selbergMoebiusCoeff_mul_vonMangoldt_of_prime
#print axioms selbergMoebiusCoeff_mul_vonMangoldt_eq_zero_of_not_prime
#print axioms selbergMollifiedTripleMainTerm_vonMangoldtSum_eq_neg_primeSum
#print axioms selbergMollifiedTripleCollectedCoeff_one_eq_primeMainTerm
#print axioms selbergMollifiedTripleCollectedCoeff_one_eq_mertensForm

end HardyTheorem
