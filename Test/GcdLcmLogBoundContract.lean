import MathlibAux.GcdLcmLogBound

open scoped BigOperators

#check MathlibAux.sum_inv_multiples_eq_inv_mul_harmonic
#check MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_harmonic
#check MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_log_cube
#check MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_log_cube_six

example (a : ℕ → ℝ) (M : ℕ) (c : ℝ) (hM : 2 ≤ M)
    (ha : ∀ n ∈ Finset.Icc 1 M, |a n| ≤ 1) :
    |∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s * (Nat.lcm r s : ℝ)⁻¹ *
          (c + 2 * Real.log (Nat.gcd r s) - Real.log r - Real.log s)| ≤
      (|c| + 4 * Real.log M) * (1 + Real.log M) ^ 3 := by
  exact MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_log_cube
    a M c hM ha

#print axioms MathlibAux.sum_inv_multiples_eq_inv_mul_harmonic
#print axioms MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_harmonic
#print axioms MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_log_cube
#print axioms MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_log_cube_six
