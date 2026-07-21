import MathlibAux.DyadicNegativeLogPolynomialMeanSquare

open Complex MeasureTheory
open scoped BigOperators

namespace Test.DyadicNegativeLogPolynomialMeanSquareContract

example (s : Finset ℕ) (coeff : ℕ → ℂ) {K : ℕ}
    (hpositive : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (MathlibAux.exponentialPolynomial s coeff
            (fun n ↦ -Real.log n) t)) ≤
      (K : ℝ) *
        ∑ j ∈ Finset.range K,
          ((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ n ∈ MathlibAux.dyadicBlock s j,
              Complex.normSq (coeff n) := by
  exact
    MathlibAux.integral_normSq_negLogExponentialPolynomial_le_dyadic
      s coeff hpositive hbound hab

#print axioms MathlibAux.integral_normSq_negLogExponentialPolynomial_le_dyadic

end Test.DyadicNegativeLogPolynomialMeanSquareContract
