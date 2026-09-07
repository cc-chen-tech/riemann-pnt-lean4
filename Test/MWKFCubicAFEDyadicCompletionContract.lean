import PrimeNumberTheorem.MWKFCubicAFEDyadicCompletion

open PrimeNumberTheorem.MWKFCubic

#check hasSum_cubicAFEDyadicCompletionWeight
#check cubicAFEDyadicCompletionWeight_eq_one_of_one_le
#check eventually_cubicAFEDyadicCompletionWeight_eq_one
#check cubicAFEDyadicCompletionCorrection_eq_zero_on_progression

-- Identical integer masses do not imply identical continuous masses.
example : cubicAFEDyadicCompletionWeight 0 (1 / 4) (5 / 4) = 0 := by
  rw [cubicAFEDyadicCompletionWeight_zero, cubicAFEDyadicLowerWeight_zero (by norm_num), zero_mul]

example : cubicAFEDyadicCompletionWeight 2 (1 / 4) (5 / 4) = 1 := by
  unfold cubicAFEDyadicCompletionWeight
  rw [cubicAFEDyadicLowerWeight_one (by norm_num), cubicAFEDyadicLowerWeight_one (by norm_num)]
  norm_num

example (J : ℕ) : cubicAFEDyadicCompletionWeight J 1 7 = 1 :=
  cubicAFEDyadicCompletionWeight_eq_one_of_one_le J (by norm_num) (by norm_num)
