import HardyTheorem.SelbergSqrtZetaSignedRationalSeparation

open HardyTheorem

#check one_div_sq_nat_mul_le_abs_sub_of_mem_selbergSqrtZetaSignedRationalSupport
#check one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport

example {N X : ℕ} {q r : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hne : q ≠ r) :
    1 / (((N * X : ℕ) : ℝ) ^ 2) ≤
      |(q : ℝ) - (r : ℝ)| :=
  one_div_sq_nat_mul_le_abs_sub_of_mem_selbergSqrtZetaSignedRationalSupport
    hq hr hne

example {N X : ℕ} {q r : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hne : q ≠ r) :
    1 / ((N * X ^ 2 : ℕ) : ℝ) ≤
      |selbergSqrtZetaSignedRationalFrequency q -
        selbergSqrtZetaSignedRationalFrequency r| :=
  one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
    hq hr hne

#print axioms
  one_div_sq_nat_mul_le_abs_sub_of_mem_selbergSqrtZetaSignedRationalSupport
#print axioms
  one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
