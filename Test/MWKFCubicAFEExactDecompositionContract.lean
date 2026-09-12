import PrimeNumberTheorem.MWKFCubicAFEExactDecomposition

open Filter Asymptotics

namespace PrimeNumberTheorem.MWKFCubic

#check cubicAFEFixedDepthPrincipalPart
#check cubicAFEFixedDepthRemainder
#check cubicAFECompletionSchedulePrincipalPart
#check cubicAFECompletionScheduleRemainder
#check cubicMollifiedSecondMoment_zero
#check cubicMollifiedSecondMoment_eq_completionSchedule_principal_remainder
#check cubicMollifiedSecondMoment_eq_fixedDepth_principal_remainder
#check cubic_actual_long_mollifier_asymptotic_of_completionSchedule_estimates
#check cubic_actual_long_mollifier_asymptotic_of_fixedDepth_estimates

example (W : CubicTestWeight) (J : ℕ) :
    cubicAFEFixedDepthPrincipalPart W J 0 = 0 := by
  simp [cubicAFEFixedDepthPrincipalPart,
    cubicAFECompletionSchedulePrincipalPart]

example (W : CubicTestWeight) (J : ℕ) :
    cubicAFEFixedDepthRemainder W J 0 = 0 := by
  simp [cubicAFEFixedDepthRemainder,
    cubicAFECompletionScheduleRemainder]

example (W : CubicTestWeight) (J : ℕ) (T : ℝ) (hT : T ≠ 0) :
    cubicAFEFixedDepthRemainder W J T = cubicAFECompletedRemainder W T 1 J := by
  simp [cubicAFEFixedDepthRemainder,
    cubicAFECompletionScheduleRemainder, hT]

example (W : CubicTestWeight) (J : ℕ) (T : ℝ) :
    cubicMollifiedSecondMoment W T =
      T * cubicAFEFixedDepthPrincipalPart W J T +
        cubicAFEFixedDepthRemainder W J T := by
  exact cubicMollifiedSecondMoment_eq_fixedDepth_principal_remainder W J T

example (W : CubicTestWeight) (J : ℝ → ℕ) (T : ℝ) :
    cubicMollifiedSecondMoment W T =
      T * cubicAFECompletionSchedulePrincipalPart W J T +
        cubicAFECompletionScheduleRemainder W J T := by
  exact cubicMollifiedSecondMoment_eq_completionSchedule_principal_remainder W J T

end PrimeNumberTheorem.MWKFCubic
