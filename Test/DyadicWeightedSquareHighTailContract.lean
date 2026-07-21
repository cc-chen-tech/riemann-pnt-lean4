import MathlibAux.DyadicWeightedSquareHighTail

open scoped BigOperators

example (s : Finset ℕ) (K L : ℕ) (f : ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hlower : ∀ n ∈ s, 2 ^ K ≤ n)
    (hupper : ∀ n ∈ s, n < 2 ^ L)
    (hdecay : ∀ k, K ≤ k → k < L →
      ∀ n ∈ MathlibAux.dyadicBlock s k,
        (f n) ^ 2 ≤ A * (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹)) :
    (∑ n ∈ s, ((n : ℝ))⁻¹ * (f n) ^ 2) ≤ 2 * A :=
  MathlibAux.sum_inv_mul_sq_le_of_high_dyadic_decay
    s K L f hA hpos hlower hupper hdecay

#print axioms MathlibAux.sum_inv_mul_sq_le_of_high_dyadic_decay
