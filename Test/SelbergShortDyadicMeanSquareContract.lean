import HardyTheorem.SelbergShortDyadicMeanSquare

open Complex MeasureTheory
open scoped BigOperators

namespace Test.SelbergShortDyadicMeanSquareContract

example {N X K : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hbound : ∀ k ∈ Finset.Ioc 1 (N * X * (X - 1)), k < 2 ^ K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (HardyTheorem.selbergShortDirichletCollectedPolynomial N X t - 1)) ≤
      (K : ℝ) *
        ∑ j ∈ Finset.range K,
          ((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ k ∈ MathlibAux.dyadicBlock
                (Finset.Ioc 1 (N * X * (X - 1))) j,
              Complex.normSq
                (HardyTheorem.selbergShortDirichletCollectedCoeff N X k) := by
  exact HardyTheorem.integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_dyadic
    hN hX hbound hab

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (HardyTheorem.selbergShortDirichletCollectedPolynomial N X t - 1)) ≤
      (HardyTheorem.selbergShortEffectiveDyadicExponent N X : ℝ) *
        ∑ j ∈ Finset.range
            (HardyTheorem.selbergShortEffectiveDyadicExponent N X),
          ((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ k ∈ MathlibAux.dyadicBlock
                (Finset.Ioc 1 (N * X * (X - 1))) j,
              Complex.normSq
                (HardyTheorem.selbergShortDirichletCollectedCoeff N X k) := by
  exact HardyTheorem.integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_effectiveDyadic
    hN hX hab

#print axioms HardyTheorem.integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_dyadic
#print axioms HardyTheorem.selbergShortDirichletCollectedPolynomial_sub_one_eq_effectiveSupport
#print axioms HardyTheorem.integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_effectiveDyadic

end Test.SelbergShortDyadicMeanSquareContract
