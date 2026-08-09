import HardyTheorem.SelbergSqrtZetaSignedRationalPacking

open HardyTheorem

#check selbergSqrtZetaSignedRationalFrequencyBallSupport
#check card_sub_one_div_nat_mul_sq_le_two_mul_radius

example {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    (xi : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (((selbergSqrtZetaSignedRationalFrequencyBallSupport N X xi r).card - 1 :
        ℕ) : ℝ) *
        (1 / ((N * X ^ 2 : ℕ) : ℝ)) ≤
      2 * r :=
  card_sub_one_div_nat_mul_sq_le_two_mul_radius hN hX xi hr

#print axioms card_sub_one_div_nat_mul_sq_le_two_mul_radius
