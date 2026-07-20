import HardyTheorem.SelbergShortTopRangeVanishing
import MathlibAux.DyadicNegativeLogPolynomialMeanSquare

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-!
# Dyadic mean square for the collected Selberg short error

After removing its constant term and the ineffective top range, the collected
Selberg short Dirichlet polynomial has precisely the negative logarithmic
frequencies required by the dyadic logarithmic mean-square estimate.  This
file specializes that general estimate without discarding the separate energy
of each dyadic coefficient block.
-/

/-- Removing the constant term and the coefficients killed by the endpoint
zero leaves exactly the effective nonconstant product support. -/
theorem selbergShortDirichletCollectedPolynomial_sub_one_eq_effectiveSupport
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (t : ℝ) :
    selbergShortDirichletCollectedPolynomial N X t - 1 =
      MathlibAux.exponentialPolynomial
        (Finset.Ioc 1 (N * X * (X - 1)))
        (selbergShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency t := by
  rw [selbergShortDirichletCollectedPolynomial_sub_one_eq hN (by omega)]
  unfold MathlibAux.exponentialPolynomial
  symm
  apply Finset.sum_subset
  · intro k hk
    have hkData := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr
      ⟨hkData.1, hkData.2.trans
        (Nat.mul_le_mul_left (N * X) (Nat.sub_le X 1))⟩
  · intro k hkFormal hkEffective
    have hkTop : N * X * (X - 1) < k := by
      by_contra hle
      exact hkEffective (Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hkFormal).1, Nat.le_of_not_gt hle⟩)
    rw [selbergShortDirichletCollectedCoeff_eq_zero_of_topRange hX hkTop,
      zero_mul]

/-- The collected nonconstant Selberg short polynomial has a dyadically
weighted mean-square bound on its effective support. -/
theorem integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_dyadic
    {N X K : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hbound : ∀ k ∈ Finset.Ioc 1 (N * X * (X - 1)), k < 2 ^ K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (selbergShortDirichletCollectedPolynomial N X t - 1)) ≤
      (K : ℝ) *
        ∑ j ∈ Finset.range K,
          ((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ k ∈ MathlibAux.dyadicBlock
                (Finset.Ioc 1 (N * X * (X - 1))) j,
              Complex.normSq (selbergShortDirichletCollectedCoeff N X k) := by
  simp_rw [selbergShortDirichletCollectedPolynomial_sub_one_eq_effectiveSupport
    hN hX]
  apply MathlibAux.integral_normSq_negLogExponentialPolynomial_le_dyadic
  · intro k hk
    exact Nat.ne_of_gt (lt_trans zero_lt_one (Finset.mem_Ioc.mp hk).1)
  · exact hbound
  · exact hab

end HardyTheorem
