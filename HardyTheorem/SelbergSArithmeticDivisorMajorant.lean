import HardyTheorem.SelbergSArithmeticSummability

open scoped BigOperators

namespace HardyTheorem

/-!
# Selberg S-arith: divisor-sum majorant

The finite Euler product is first expanded over divisors of the radical.
Since the radical divides the original positive integer and all coefficients
are nonnegative, it is bounded by the corresponding full divisor sum.
-/

theorem selbergNineProduct_le_divisorSum {r : ℕ} (hr : r ≠ 0) :
    (∏ p ∈ r.primeFactors, (1 + 9 * (p : ℝ)⁻¹)) ≤
      ∑ d ∈ r.divisors, selbergNineSquarefreeDivisorCoeff d := by
  rw [selbergNineProduct_eq_squarefreeDivisorSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Nat.divisors_subset_of_dvd hr (Nat.prod_primeFactors_dvd r)) ?_
  intro d _ _
  exact selbergNineSquarefreeDivisorCoeff_nonneg d

end HardyTheorem
