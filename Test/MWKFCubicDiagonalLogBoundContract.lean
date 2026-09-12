import PrimeNumberTheorem.MWKFCubicDiagonalLogBound

open PrimeNumberTheorem.MWKFCubic

#check abs_cubicReciprocalLcmLogKernel_le_harmonic
#check abs_cubicReciprocalLcmLogKernel_le_log_cube
#check abs_cubicReciprocalLcmLogKernel_le_log_cube_six
#check abs_cubicReciprocalLcmLogKernel_le_log_cube_of_two_le_cube

example (T c : ℝ) (hT : (2 : ℝ) ≤ T ^ 3) :
    |cubicReciprocalLcmLogKernel T c| ≤
      (|c| + 4 * Real.log (cubicMollifierLength T)) *
        (1 + Real.log (cubicMollifierLength T)) ^ 3 := by
  exact abs_cubicReciprocalLcmLogKernel_le_log_cube_of_two_le_cube T c hT

#print axioms abs_cubicReciprocalLcmLogKernel_le_harmonic
#print axioms abs_cubicReciprocalLcmLogKernel_le_log_cube
#print axioms abs_cubicReciprocalLcmLogKernel_le_log_cube_six
#print axioms abs_cubicReciprocalLcmLogKernel_le_log_cube_of_two_le_cube
