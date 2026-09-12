import PrimeNumberTheorem.MWKFCubicDoublePerron

open PrimeNumberTheorem.MWKFCubic

#check cubicPerronLogWeight
#check cubicPerronVerticalIntegral
#check cubicPerronVerticalIntegral_eq_logWeight
#check cubicMollifierCoefficient_eq_moebius_mul_perronLogWeight_div
#check cubicDoublePerronQuadratic
#check cubicDoublePerronLogKernel
#check cubicReciprocalLcmQuadratic_eq_doublePerron
#check cubicReciprocalLcmLogKernel_eq_doublePerron

example {T sigma : ℝ} (hsigma : 0 < sigma)
    (hN : 2 ≤ cubicMollifierLength T) :
    (cubicReciprocalLcmQuadratic T : ℂ) =
      cubicDoublePerronQuadratic T sigma /
        (Real.log (cubicMollifierLength T : ℝ) : ℂ) ^ 2 := by
  exact cubicReciprocalLcmQuadratic_eq_doublePerron hsigma hN

example {T sigma c : ℝ} (hsigma : 0 < sigma)
    (hN : 2 ≤ cubicMollifierLength T) :
    (cubicReciprocalLcmLogKernel T c : ℂ) =
      cubicDoublePerronLogKernel T sigma c /
        (Real.log (cubicMollifierLength T : ℝ) : ℂ) ^ 2 := by
  exact cubicReciprocalLcmLogKernel_eq_doublePerron hsigma hN

#print axioms cubicPerronVerticalIntegral_eq_logWeight
#print axioms cubicMollifierCoefficient_eq_moebius_mul_perronLogWeight_div
#print axioms cubicReciprocalLcmQuadratic_eq_doublePerron
#print axioms cubicReciprocalLcmLogKernel_eq_doublePerron
