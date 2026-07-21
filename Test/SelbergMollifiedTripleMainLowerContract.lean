import HardyTheorem.SelbergMollifiedTripleMainLower

open scoped BigOperators

namespace HardyTheorem

/-!
# Contract test for the Selberg main-coefficient lower bound

Checks the lower Mertens bound, the two-scale log-weighted lower bound, the
prime-to-von-Mangoldt comparison, the telescoping identity, the quantitative
`1/4 - C / log X` lower bound for the main coefficient, and the `1/8`
corollary for large `log X`.
-/

example {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤
      ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
  log_sub_one_le_vonMangoldt_sum_div hN

example {X : ℕ} (hX : 2 ≤ X) :
    (Real.log (X : ℝ)) ^ 2 / 4 - ((Real.log 4 + 6) / 2) * Real.log (X : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ) :=
  vonMangoldt_log_sum_div_ge hX

example {X : ℕ} (hX : 2 ≤ X) :
    ∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
        selbergMoebiusWeight X p * Real.log p / (p : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 X,
        selbergMoebiusWeight X n * ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
  weighted_primeLogSum_le_weighted_vonMangoldt hX

example (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X,
        selbergMoebiusWeight X n * ArithmeticFunction.vonMangoldt n / (n : ℝ) =
      (∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        (∑ n ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt n * Real.log n / (n : ℝ)) /
          Real.log X :=
  weighted_vonMangoldt_sum_eq X

example {X : ℕ} (hX : 2 ≤ X) :
    (1 : ℝ) / 4 - ((3 * Real.log 4 + 16) / 2) / Real.log X ≤
      1 - (∑ p ∈ (Finset.Icc 2 X).filter Nat.Prime,
          selbergMoebiusWeight X p * Real.log p / (p : ℝ)) / Real.log X :=
  one_sub_primeLogSum_div_ge hX

example {N X : ℕ} (hX : 2 ≤ X) (hNX : X ≤ N) :
    (1 : ℝ) / 4 - ((3 * Real.log 4 + 16) / 2) / Real.log X ≤
      (selbergMollifiedTripleCollectedCoeff N X 1).re :=
  selbergMollifiedTripleCollectedCoeff_one_re_ge hX hNX

example {N X : ℕ} (hX : 2 ≤ X) (hNX : X ≤ N)
    (hXL : 12 * Real.log 4 + 64 ≤ Real.log X) :
    (1 : ℝ) / 8 ≤ (selbergMollifiedTripleCollectedCoeff N X 1).re :=
  selbergMollifiedTripleCollectedCoeff_one_re_ge_one_eighth hX hNX hXL

/-- At `X = N = 2` the coefficient is exactly one, and the lower bound is
vacuous because its right-hand side is negative. -/
example : (selbergMollifiedTripleCollectedCoeff 2 2 1).re = 1 := by
  have h : selbergMollifiedTripleCollectedCoeff 2 2 1 = 1 := by
    rw [selbergMollifiedTripleCollectedCoeff_one_eq_primeMainTerm
      (N := 2) (X := 2) (by norm_num) le_rfl]
    have hset : (Finset.Icc 2 2).filter Nat.Prime = {2} := by decide
    have hlog2 : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
      have h2 : Real.log (2 : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
      exact_mod_cast h2
    have hw22 : selbergMoebiusWeight 2 2 = 0 := by
      rw [selbergMoebiusWeight, div_self hlog2, sub_self]
    rw [hset, Finset.sum_singleton, hw22]
    norm_num
  rw [h]
  rfl

#print axioms log_sub_one_le_vonMangoldt_sum_div
#print axioms vonMangoldt_log_sum_div_ge
#print axioms weighted_primeLogSum_le_weighted_vonMangoldt
#print axioms weighted_vonMangoldt_sum_eq
#print axioms one_sub_primeLogSum_div_ge
#print axioms selbergMollifiedTripleCollectedCoeff_one_re_ge
#print axioms selbergMollifiedTripleCollectedCoeff_one_re_ge_one_eighth

end HardyTheorem
