import MathlibAux.MinReciprocalSquareSum

open scoped BigOperators

#check MathlibAux.sum_sq_min_div_le

example (K : ℕ) {delta B : ℝ} (hdelta : 0 < delta) (hB : 0 ≤ B) :
    (∑ j ∈ Finset.Icc 1 K, (min delta (B / j)) ^ 2) ≤
      3 * B * delta := by
  exact MathlibAux.sum_sq_min_div_le K hdelta hB

#print axioms MathlibAux.sum_sq_min_div_le
