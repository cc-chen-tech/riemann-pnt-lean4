import HardyTheorem.SelbergHardyLagLinearization

open Set
open HardyTheorem

#check thetaLagPhase
#check thetaLagReferenceFrequency
#check hasDerivAt_thetaLagPhase
#check deriv_thetaLagPhase_zero
#check thetaLagReferenceFrequency_eq
#check abs_deriv_thetaLagPhase_sub_referenceFrequency_le
#check abs_thetaLagPhase_sub_linearized_le
#check abs_thetaLagPhase_sub_linearized_le_window_sq
#check abs_cos_thetaLagPhase_sub_cos_linearized_le
#check abs_cos_thetaLagPhase_shift_sub_cos_frozen_le
#check abs_squareIntegral_cos_thetaLagPhase_le
#check abs_squareIntegral_cos_thetaLagPhase_shift_le
#check abs_squareIntegral_cos_thetaLagPhase_shift_le_stationaryEnvelope

example (omega : ℝ) {x : ℝ} (hx : 0 < x) :
    thetaLagReferenceFrequency omega x =
      -((1 / 2 : ℝ) * Real.log (x / (2 * Real.pi)) + omega) :=
  thetaLagReferenceFrequency_eq omega hx

example (omega : ℝ) {T H x tau : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Set.Icc T (2 * T)) (htau : |tau| ≤ H) :
    |deriv (thetaLagPhase omega x) tau -
        thetaLagReferenceFrequency omega x| ≤
      |tau| / (2 * (T - H)) :=
  abs_deriv_thetaLagPhase_sub_referenceFrequency_le
    omega hT hH hHT hx htau

example (omega : ℝ) {T H x tau : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Set.Icc T (2 * T)) (htau : |tau| ≤ H) :
    |thetaLagPhase omega x tau -
        thetaLagReferenceFrequency omega x * tau| ≤
      H * |tau| / (2 * (T - H)) :=
  abs_thetaLagPhase_sub_linearized_le
    omega hT hH hHT hx htau

example (omega : ℝ) {T H x tau : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Set.Icc T (2 * T)) (htau : |tau| ≤ H) :
    |thetaLagPhase omega x tau -
        thetaLagReferenceFrequency omega x * tau| ≤
      H ^ 2 / (2 * (T - H)) :=
  abs_thetaLagPhase_sub_linearized_le_window_sq
    omega hT hH hHT hx htau

example (omega : ℝ) {T H x tau : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Set.Icc T (2 * T)) (htau : |tau| ≤ H) :
    |Real.cos (thetaLagPhase omega x tau) -
        Real.cos (thetaLagReferenceFrequency omega x * tau)| ≤
      H ^ 2 / (2 * (T - H)) :=
  abs_cos_thetaLagPhase_sub_cos_linearized_le
    omega hT hH hHT hx htau

example (omega : ℝ) {T H x : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hHT : H ≤ T / 2)
    (hx : x ∈ Set.Icc T (2 * T - H)) :
    |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H,
        Real.cos (thetaLagPhase omega (x + v) (w - v))| ≤
      (MathlibAux.stationaryMinReciprocalEnvelope
          H (-deriv thetaModel x) omega) ^ 2 +
        (H ^ 2 / (T - H)) * H ^ 2 :=
  abs_squareIntegral_cos_thetaLagPhase_shift_le_stationaryEnvelope
    omega hT hH hHT hx
