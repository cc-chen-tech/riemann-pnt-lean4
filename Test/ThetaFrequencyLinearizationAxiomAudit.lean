import HardyTheorem.ThetaFrequencyLinearization

open Complex
open HardyTheorem

#check thetaFrequencyShortIntegral
#check thetaFrequencyLinearizedShortIntegral
#check norm_thetaFrequencyShortIntegral_sub_linearized_le
#check norm_thetaFrequencyShortIntegral_le_min_add_linearization_error

example (omega : ℝ) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta) :
    ‖thetaFrequencyShortIntegral omega delta t -
        thetaFrequencyLinearizedShortIntegral omega delta t‖ ≤
      delta ^ 3 / (2 * T) :=
  norm_thetaFrequencyShortIntegral_sub_linearized_le
    omega hT hTt hdelta

example (omega : ℝ) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta)
    (hfreq : deriv thetaModel t + omega ≠ 0) :
    ‖thetaFrequencyShortIntegral omega delta t‖ ≤
      min delta (2 / |deriv thetaModel t + omega|) +
        delta ^ 3 / (2 * T) :=
  norm_thetaFrequencyShortIntegral_le_min_add_linearization_error
    omega hT hTt hdelta hfreq

#print axioms norm_thetaFrequencyShortIntegral_sub_linearized_le
#print axioms norm_thetaFrequencyShortIntegral_le_min_add_linearization_error
