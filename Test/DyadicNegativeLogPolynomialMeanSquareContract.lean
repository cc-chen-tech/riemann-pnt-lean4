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

example (s : Finset ℕ) (coeff : ℕ → ℂ) {K : ℕ}
    (weight : ℕ → ℝ)
    (hweight : ∀ j ∈ Finset.range K, 0 < weight j)
    (hpositive : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (MathlibAux.exponentialPolynomial s coeff
            (fun n ↦ -Real.log n) t)) ≤
      (∑ j ∈ Finset.range K, weight j) *
        ∑ j ∈ Finset.range K,
          (((b - a) +
              2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
            ∑ n ∈ MathlibAux.dyadicBlock s j,
              Complex.normSq (coeff n)) / weight j := by
  exact
    MathlibAux.integral_normSq_negLogExponentialPolynomial_le_weighted_dyadic
      s coeff weight hweight hpositive hbound hab

example (s : Finset ℕ) (coeff : ℕ → ℂ) {K : ℕ}
    (hpositive : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b,
        Complex.normSq
          (MathlibAux.exponentialPolynomial s coeff
            (fun n ↦ -Real.log n) t)) ≤
      2 *
        ∑ j ∈ Finset.range K,
          (((j + 1 : ℕ) : ℝ) ^ 2) *
            (((b - a) +
                2 * ((5 * Real.pi + 3) * ((2 ^ j : ℕ) : ℝ))) *
              ∑ n ∈ MathlibAux.dyadicBlock s j,
                Complex.normSq (coeff n)) := by
  exact
    MathlibAux.integral_normSq_negLogExponentialPolynomial_le_squareWeighted_dyadic
      s coeff hpositive hbound hab

#print axioms MathlibAux.integral_normSq_negLogExponentialPolynomial_le_dyadic
#print axioms MathlibAux.integral_normSq_negLogExponentialPolynomial_le_weighted_dyadic
#print axioms MathlibAux.integral_normSq_negLogExponentialPolynomial_le_squareWeighted_dyadic

end Test.DyadicNegativeLogPolynomialMeanSquareContract
