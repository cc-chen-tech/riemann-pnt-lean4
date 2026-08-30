import PrimeNumberTheorem.MWKFCubicAFECompletedBoundary

open PrimeNumberTheorem.MWKFCubic

#check cubicAFECompletedLowerScale_index_bound
#check exists_cubicAFECompletedLowerScale_bound
#check cubicAFECompletedLowerScaleBoxes
#check cubicAFEProgressionCompletedCutoff_zero_outside_lowerBoxes

-- Finite support bound at negative shift; no shift/modulus coprimality is assumed.
example : 2 * (2 : ℝ)^2 * cubicAFECompletedBoundarySize 2 4 (-6) < (2 : ℝ)^7 := by
  norm_num [cubicAFECompletedBoundarySize]

example : cubicAFECompletedLowerScaleBoxes 0 7 = ∅ := by
  simp [cubicAFECompletedLowerScaleBoxes]
