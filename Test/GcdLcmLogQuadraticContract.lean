import MathlibAux.GcdLcmLogQuadratic

open scoped BigOperators

#check MathlibAux.gcdLogWeight
#check MathlibAux.gcdLogWeight_eq_sum
#check MathlibAux.sum_gcdLogWeight_divisors
#check MathlibAux.sum_reciprocal_lcm_bilinear_eq_totient_products
#check MathlibAux.sum_reciprocal_lcm_log_left_eq_totient_products
#check MathlibAux.sum_reciprocal_lcm_log_gcd_eq_gcdLogWeight_squares
#check MathlibAux.sum_reciprocal_lcm_log_kernel_eq

example : MathlibAux.gcdLogWeight 1 = 0 := by
  exact MathlibAux.gcdLogWeight_one

example : MathlibAux.gcdLogWeight 2 = 2 * Real.log 2 := by
  exact MathlibAux.gcdLogWeight_two

#print axioms MathlibAux.sum_gcdLogWeight_divisors
#print axioms MathlibAux.sum_reciprocal_lcm_bilinear_eq_totient_products
#print axioms MathlibAux.sum_reciprocal_lcm_log_left_eq_totient_products
#print axioms MathlibAux.sum_reciprocal_lcm_log_gcd_eq_gcdLogWeight_squares
#print axioms MathlibAux.sum_reciprocal_lcm_log_kernel_eq
