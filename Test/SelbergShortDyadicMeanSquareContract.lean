import HardyTheorem.SelbergShortDyadicMeanSquare

open Complex MeasureTheory
open scoped BigOperators

namespace Test.SelbergShortDyadicMeanSquareContract

example {N X K : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    (hbound : ∀ k ∈ Finset.Ioc 1 (N * X * X), k < 2 ^ K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (HardyTheorem.selbergShortDirichletCollectedPolynomial N X t - 1)) ≤
      (K : ℝ) *
        ∑ j ∈ Finset.range K,
          ((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ k ∈ MathlibAux.dyadicBlock (Finset.Ioc 1 (N * X * X)) j,
              Complex.normSq
                (HardyTheorem.selbergShortDirichletCollectedCoeff N X k) := by
  exact HardyTheorem.integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_dyadic
    hN hX hbound hab

#print axioms HardyTheorem.integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_dyadic

end Test.SelbergShortDyadicMeanSquareContract
