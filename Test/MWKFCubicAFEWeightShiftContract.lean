import PrimeNumberTheorem.MWKFCubicAFEWeightShift

open PrimeNumberTheorem.MWKFCubic

#check exists_norm_cubicAFEWeightMellinKernel_horizontal_le
#check tendsto_cubicAFEWeightMellinKernel_horizontalIntegral
#check cubicAFERealProductWeightVertical_eq_one_add
#check norm_cubicAFERealProductWeightVertical_le_one_add

-- This tests the residue sign and the exact quarter-power, not only a name.
example (t : ℝ) {P : ℝ} (hP : 0 < P) :
    cubicAFERealProductWeightVertical t (3 / 4) P =
      1 + cubicAFERealProductWeightVertical t (-1 / 4) P :=
  cubicAFERealProductWeightVertical_eq_one_add t hP (by norm_num)
    (by norm_num) (by norm_num)

example (t : ℝ) {P : ℝ} (hP : 0 < P) :
    ‖cubicAFERealProductWeightVertical t (3 / 4) P‖ ≤
      1 + cubicAFEWeightNormMass t (-1 / 4) * P ^ (1 / 4 : ℝ) := by
  simpa only [neg_div, neg_neg] using norm_cubicAFERealProductWeightVertical_le_one_add t hP
    (a := -1 / 4) (b := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
