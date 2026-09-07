import PrimeNumberTheorem.MWKFCubicAFEWeightEndpoint

open PrimeNumberTheorem.MWKFCubic

#check stronglyMeasurable_cubicAFERealProductWeightVertical
#check norm_cubicAFERealProductWeightVertical_le_of_le_one
#check integrableOn_cubicAFERealProductWeightVertical_weighted

example (t : ℝ) {P : ℝ} (hP : 0 < P) (hP1 : P ≤ 1) :
    ‖cubicAFERealProductWeightVertical t (3 / 4) P‖ ≤
      1 + cubicAFEWeightNormMass t (-1 / 4) :=
  norm_cubicAFERealProductWeightVertical_le_of_le_one t (by norm_num) hP hP1

-- The norm, not merely a possibly conditionally convergent integral, is integrable.
example (t : ℝ) : MeasureTheory.IntegrableOn
    (fun P : ℝ ↦ ‖((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * cubicAFERealProductWeightVertical t (3 / 4) P‖)
    (Set.Ioi 0) :=
  (integrableOn_cubicAFERealProductWeightVertical_weighted t (by norm_num)).norm
