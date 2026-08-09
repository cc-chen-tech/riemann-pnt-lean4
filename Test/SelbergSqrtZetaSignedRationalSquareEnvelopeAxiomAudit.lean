import HardyTheorem.SelbergSqrtZetaSignedRationalSquareEnvelope

open scoped BigOperators

open HardyTheorem

#check sum_sq_stationaryMinReciprocalEnvelope_rationalSupport_le

example {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    {H t : ℝ} (hH : 0 ≤ H) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        (MathlibAux.stationaryMinReciprocalEnvelope
          H (-deriv thetaModel t)
          (selbergSqrtZetaSignedRationalFrequency q)) ^ 2) ≤
      H ^ 2 + 12 * H * ((N * X ^ 2 : ℕ) : ℝ) := by
  exact
    sum_sq_stationaryMinReciprocalEnvelope_rationalSupport_le
      hN hX hH

#print axioms
  HardyTheorem.sum_sq_stationaryMinReciprocalEnvelope_rationalSupport_le
