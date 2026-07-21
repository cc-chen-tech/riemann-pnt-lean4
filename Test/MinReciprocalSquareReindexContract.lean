import MathlibAux.MinReciprocalSquareReindex

open scoped BigOperators

#check MathlibAux.sum_sq_min_div_nat_sub_left_le
#check MathlibAux.sum_sq_min_div_nat_sub_right_le

example (s : Finset ℕ) (base : ℕ) {delta B : ℝ}
    (hdelta : 0 < delta) (hB : 0 ≤ B)
    (hleft : ∀ n ∈ s, n < base) :
    (∑ n ∈ s, (min delta (B / (base - n : ℕ))) ^ 2) ≤
      3 * B * delta :=
  MathlibAux.sum_sq_min_div_nat_sub_left_le
    s base hdelta hB hleft

example (s : Finset ℕ) (base N : ℕ) {delta B : ℝ}
    (hdelta : 0 < delta) (hB : 0 ≤ B)
    (hright : ∀ n ∈ s, base < n)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s, (min delta (B / (n - base : ℕ))) ^ 2) ≤
      3 * B * delta :=
  MathlibAux.sum_sq_min_div_nat_sub_right_le
    s base N hdelta hB hright hupper

#print axioms MathlibAux.sum_sq_min_div_nat_sub_left_le
#print axioms MathlibAux.sum_sq_min_div_nat_sub_right_le
