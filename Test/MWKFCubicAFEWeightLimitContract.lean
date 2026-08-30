import PrimeNumberTheorem.MWKFCubicAFEWeightLimit

open PrimeNumberTheorem.MWKFCubic

#check integrable_cubicAFERealProductMellinIntegrand
#check tendsto_cubicAFERealProductWeightFinite
#check norm_cubicAFERealProductWeightVertical_le
#check norm_cubicAFERealProductWeightFinite_le_normMass

example (t : ℝ) {P : ℝ} (hP : 0 < P) :
    Filter.Tendsto (fun V : ℝ ↦ cubicAFERealProductWeightFinite t (-1 / 4) V P)
      Filter.atTop (nhds (cubicAFERealProductWeightVertical t (-1 / 4) P)) :=
  tendsto_cubicAFERealProductWeightFinite t (by norm_num) (by norm_num) hP
