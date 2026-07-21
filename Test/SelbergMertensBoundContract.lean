import HardyTheorem.SelbergMertensBound

open scoped BigOperators

namespace HardyTheorem

/-!
# Contract test for the explicit Mertens upper bound

Checks the integral comparisons, the divisor count, the exact factorial
identity, the von-Mangoldt Mertens bound, the prime Mertens bound, and the
trivial evaluation at `N = 1` where the prime sum vanishes.
-/

example (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log n ≤
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N :=
  log_sum_Icc_le N

example {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N + 1 ≤ ∑ n ∈ Finset.Icc 1 N, Real.log n :=
  le_log_sum_Icc hN

example {N d : ℕ} (hd : 1 ≤ d) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d :=
  card_Icc_filter_dvd hd

example (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log n =
      ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) :=
  log_sum_Icc_eq_sum_vonMangoldt_mul_div N

example {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      Real.log N + (Real.log 4 + 5) :=
  vonMangoldt_sum_div_le_log_add hN

example {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / (p : ℝ) ≤
      Real.log N + (Real.log 4 + 5) :=
  primeLogSum_div_le_log_add hN

/-- At `N = 1` the prime range is empty and the prime log sum vanishes. -/
example : ∑ p ∈ (Finset.Icc 2 1).filter Nat.Prime, Real.log p / (p : ℝ) = 0 := by
  rw [show (Finset.Icc 2 1).filter Nat.Prime = ∅ by decide, Finset.sum_empty]

/-- The `N = 1` bound is then the trivial inequality `0 ≤ log 4 + 5`. -/
example : (0 : ℝ) ≤ Real.log 1 + (Real.log 4 + 5) := by
  have h := primeLogSum_div_le_log_add (N := 1) le_rfl
  rw [show (Finset.Icc 2 1).filter Nat.Prime = ∅ by decide, Finset.sum_empty,
    Nat.cast_one] at h
  exact h

#print axioms log_sum_Icc_le
#print axioms le_log_sum_Icc
#print axioms card_Icc_filter_dvd
#print axioms log_sum_Icc_eq_sum_vonMangoldt_mul_div
#print axioms vonMangoldt_sum_div_le_log_add
#print axioms primeLogSum_div_le_log_add

end HardyTheorem
