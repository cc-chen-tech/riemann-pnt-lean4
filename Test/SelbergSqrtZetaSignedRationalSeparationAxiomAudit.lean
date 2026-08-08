import HardyTheorem.SelbergSqrtZetaSignedRationalSeparation

open HardyTheorem

#check one_div_sq_nat_mul_le_abs_sub_of_mem_selbergSqrtZetaSignedRationalSupport
#check one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
#check selbergSqrtZetaSignedNearFrequencySupport
#check card_selbergSqrtZetaSignedNearFrequencySupport_le_one
#check selbergSqrtZetaSignedNearStationarySupport
#check card_selbergSqrtZetaSignedNearStationarySupport_le_one
#check one_div_two_mul_nat_mul_sq_le_abs_thetaDerivative_add_frequency_of_mem_not_near
#check two_div_abs_thetaDerivative_add_frequency_le_four_mul_nat_mul_sq_of_mem_not_near

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

example {N X : ℕ} (hN : 0 < N) (hX : 0 < X) (xi : ℝ) :
    (selbergSqrtZetaSignedNearFrequencySupport N X xi).card ≤ 1 :=
  card_selbergSqrtZetaSignedNearFrequencySupport_le_one hN hX xi

example {N X : ℕ} (hN : 0 < N) (hX : 0 < X) (t : ℝ) :
    (selbergSqrtZetaSignedNearStationarySupport N X t).card ≤ 1 :=
  card_selbergSqrtZetaSignedNearStationarySupport_le_one hN hX t

example {N X : ℕ} {q : ℚ} {t : ℝ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hqfar : q ∉ selbergSqrtZetaSignedNearStationarySupport N X t) :
    1 / (2 * ((N * X ^ 2 : ℕ) : ℝ)) ≤
      |deriv thetaModel t + selbergSqrtZetaSignedRationalFrequency q| :=
  one_div_two_mul_nat_mul_sq_le_abs_thetaDerivative_add_frequency_of_mem_not_near
    hq hqfar

example {N X : ℕ} {q : ℚ} {t : ℝ}
    (hN : 0 < N) (hX : 0 < X)
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hqfar : q ∉ selbergSqrtZetaSignedNearStationarySupport N X t) :
    2 / |deriv thetaModel t + selbergSqrtZetaSignedRationalFrequency q| ≤
      4 * ((N * X ^ 2 : ℕ) : ℝ) :=
  two_div_abs_thetaDerivative_add_frequency_le_four_mul_nat_mul_sq_of_mem_not_near
    hN hX hq hqfar

#print axioms
  one_div_sq_nat_mul_le_abs_sub_of_mem_selbergSqrtZetaSignedRationalSupport
#print axioms
  one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
#print axioms card_selbergSqrtZetaSignedNearFrequencySupport_le_one
#print axioms card_selbergSqrtZetaSignedNearStationarySupport_le_one
#print axioms
  one_div_two_mul_nat_mul_sq_le_abs_thetaDerivative_add_frequency_of_mem_not_near
#print axioms
  two_div_abs_thetaDerivative_add_frequency_le_four_mul_nat_mul_sq_of_mem_not_near
