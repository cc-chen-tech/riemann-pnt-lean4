import MathlibAux.DyadicWeightedSquareTail

open scoped BigOperators

example (s : Finset ℕ) (K : ℕ) (f : ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K)
    (hdecay : ∀ k < K, ∀ n ∈ MathlibAux.dyadicBlock s k,
      (f n) ^ 2 ≤ A * ((((K - k : ℕ) : ℝ) ^ 2)⁻¹)) :
    (∑ n ∈ s, ((n : ℝ))⁻¹ * (f n) ^ 2) ≤ 2 * A :=
  MathlibAux.sum_inv_mul_sq_le_of_dyadic_decay
    s K f hA hpos hbound hdecay

#print axioms MathlibAux.sum_inv_mul_sq_le_of_dyadic_decay
