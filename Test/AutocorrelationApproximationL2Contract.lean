import MathlibAux.AutocorrelationApproximationL2

open MeasureTheory Set

namespace MathlibAux

#check abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq_of_continuousOn
#check abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq
#check abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn_L2

example {F : ℝ → ℝ} (hF : Continuous F) {A B : ℝ} (hAB : A ≤ B) :
    |∫ x in A..B, F x| ≤
      Real.sqrt (B - A) * Real.sqrt (∫ x in A..B, F x ^ 2) :=
  abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq hF hAB

example
    {F P : ℝ → ℝ} {A B tau eps MF MP : ℝ}
    (hF : ContinuousOn F
      (Icc (min A (A + tau)) (max B (B + tau))))
    (hP : ContinuousOn P
      (Icc (min A (A + tau)) (max B (B + tau))))
    (hAB : A ≤ B) (heps : 0 ≤ eps)
    (happrox : ∀ x ∈ Icc (min A (A + tau)) (max B (B + tau)),
      |F x - P x| ≤ eps)
    (hFsq :
      (∫ x in min A (A + tau)..max B (B + tau), F x ^ 2) ≤ MF)
    (hPsq :
      (∫ x in min A (A + tau)..max B (B + tau), P x ^ 2) ≤ MP) :
    |(∫ x in A..B, F x * F (x + tau)) -
        ∫ x in A..B, P x * P (x + tau)| ≤
      eps * Real.sqrt (B - A) *
        (Real.sqrt MF + Real.sqrt MP) :=
  abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn_L2
    hF hP hAB heps happrox hFsq hPsq

#print axioms abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq_of_continuousOn
#print axioms abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq
#print axioms abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn_L2

end MathlibAux
