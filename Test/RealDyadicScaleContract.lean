import MathlibAux.RealDyadicScale

example {r : ℝ} (hr : 1 ≤ r) :
    ∃ K : ℕ, (2 : ℝ) ^ K ≤ r ∧ r < (2 : ℝ) ^ (K + 1) :=
  MathlibAux.exists_nat_pow_two_le_lt_pow_two hr

#print axioms MathlibAux.exists_nat_pow_two_le_lt_pow_two
