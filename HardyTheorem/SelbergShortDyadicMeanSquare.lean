import HardyTheorem.SelbergShortTopRangeVanishing
import MathlibAux.DyadicNegativeLogPolynomialMeanSquare

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-!
# Dyadic mean square for the collected Selberg short error

After removing its constant term, the collected Selberg short Dirichlet
polynomial has precisely the negative logarithmic frequencies required by the
dyadic logarithmic mean-square estimate.  This file specializes that general
estimate without discarding the separate energy of each dyadic coefficient
block.
-/

/-- The collected nonconstant Selberg short polynomial has a dyadically
weighted mean-square bound.  The hypothesis `hbound` is deliberately stated
on its actual nonconstant support; callers may obtain it from either the
formal endpoint or the sharper effective endpoint. -/
theorem integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_dyadic
    {N X K : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    (hbound : ∀ k ∈ Finset.Ioc 1 (N * X * X), k < 2 ^ K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (selbergShortDirichletCollectedPolynomial N X t - 1)) ≤
      (K : ℝ) *
        ∑ j ∈ Finset.range K,
          ((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ k ∈ MathlibAux.dyadicBlock (Finset.Ioc 1 (N * X * X)) j,
              Complex.normSq (selbergShortDirichletCollectedCoeff N X k) := by
  simp_rw [selbergShortDirichletCollectedPolynomial_sub_one_eq hN hX]
  apply MathlibAux.integral_normSq_negLogExponentialPolynomial_le_dyadic
  · intro k hk
    exact Nat.ne_of_gt (lt_trans zero_lt_one (Finset.mem_Ioc.mp hk).1)
  · exact hbound
  · exact hab

end HardyTheorem
