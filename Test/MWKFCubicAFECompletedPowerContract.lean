import PrimeNumberTheorem.MWKFCubicAFECompletedPower

open PrimeNumberTheorem.MWKFCubic

#check cubicAFECompletionLowerEndpoint_pos
#check cubicAFECompletionWeight_zero_of_first_le
#check cubicAFECompletionWeight_zero_of_second_le
#check integrable_cubicAFECompletedHalfLinePower
#check cubicAFECompletionWeight_mul_product_rpow_le

-- Both endpoints are included in the exact vanishing condition.
example (y : ℝ) : cubicAFEDyadicCompletionWeight 2 (1 / 8) y = 0 :=
  cubicAFECompletionWeight_zero_of_first_le 2
    (by norm_num [cubicAFECompletionLowerEndpoint]) y

example (x : ℝ) : cubicAFEDyadicCompletionWeight 2 x (1 / 8) = 0 :=
  cubicAFECompletionWeight_zero_of_second_le 2 x
    (by norm_num [cubicAFECompletionLowerEndpoint])

example (X : ℝ) : cubicAFECompletedHalfLinePower X 0 = cubicAFEHalfLinePower X := by
  funext x
  simp only [cubicAFECompletedHalfLinePower, cubicAFEHalfLinePower,
    cubicAFECompletionLowerEndpoint, pow_zero, mul_one]

example (x y : ℝ) : cubicAFEDyadicCompletionWeight 2 x y * (x * y) ^ (-3 / 2 : ℝ) ≤
    (1 / 8 : ℝ) ^ (-3 / 2 : ℝ) * cubicAFECompletedHalfLinePower 1 2 x := by
  simpa only [show -(1 : ℝ) - 1 / 2 = -3 / 2 by norm_num,
    show cubicAFECompletionLowerEndpoint 2 = 1 / 8 by norm_num [cubicAFECompletionLowerEndpoint] ]
    using cubicAFECompletionWeight_mul_product_rpow_le (X := 1) (by norm_num) 2 x y
