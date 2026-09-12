import PrimeNumberTheorem.MWKFCubicDiagonalLogKernel

open PrimeNumberTheorem.MWKFCubic

#check cubicMollifierDivisorMass
#check cubicMollifierLogDivisorMass
#check cubicReciprocalLcmQuadratic
#check cubicReciprocalLcmLogKernel
#check cubicReciprocalLcmQuadratic_eq_totient
#check cubicReciprocalLcmLogKernel_eq

example (T : ℝ) :
    cubicReciprocalLcmQuadratic T =
      ∑ d ∈ cubicMollifierSupport T,
        (d.totient : ℝ) * cubicMollifierDivisorMass T d ^ 2 := by
  exact cubicReciprocalLcmQuadratic_eq_totient T

example (T c : ℝ) :
    cubicReciprocalLcmLogKernel T c =
      ∑ d ∈ cubicMollifierSupport T,
        ((c * (d.totient : ℝ) + 2 * MathlibAux.gcdLogWeight d) *
            cubicMollifierDivisorMass T d ^ 2 -
          2 * (d.totient : ℝ) * cubicMollifierDivisorMass T d *
            cubicMollifierLogDivisorMass T d) := by
  exact cubicReciprocalLcmLogKernel_eq T c

#print axioms PrimeNumberTheorem.MWKFCubic.cubicReciprocalLcmQuadratic_eq_totient
#print axioms PrimeNumberTheorem.MWKFCubic.cubicReciprocalLcmLogKernel_eq
