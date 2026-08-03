import HardyTheorem.ThetaFrequencyLinearization

open Complex

namespace HardyTheorem

noncomputable example (omega delta t : ℝ) : ℂ :=
  thetaFrequencyShortIntegral omega delta t

noncomputable example (omega delta t : ℝ) : ℂ :=
  thetaFrequencyLinearizedShortIntegral omega delta t

noncomputable example (omega T delta t : ℝ) : ℝ :=
  thetaFrequencyShortIntegralEnvelope omega T delta t

example (omega : ℝ) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    ‖thetaFrequencyShortIntegral omega delta t‖ ≤ delta :=
  norm_thetaFrequencyShortIntegral_le_length omega hdelta

example (omega : ℝ) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta) :
    ‖thetaFrequencyShortIntegral omega delta t -
        thetaFrequencyLinearizedShortIntegral omega delta t‖ ≤
      delta ^ 3 / (2 * T) :=
  norm_thetaFrequencyShortIntegral_sub_linearized_le
    omega hT hTt hdelta

example (omega : ℝ) {delta t : ℝ} (hdelta : 0 ≤ delta)
    (hfreq : deriv thetaModel t + omega ≠ 0) :
    ‖thetaFrequencyLinearizedShortIntegral omega delta t‖ ≤
      min delta (2 / |deriv thetaModel t + omega|) :=
  norm_thetaFrequencyLinearizedShortIntegral_le_min
    omega hdelta hfreq

example (omega : ℝ) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta)
    (hfreq : deriv thetaModel t + omega ≠ 0) :
    ‖thetaFrequencyShortIntegral omega delta t‖ ≤
      min delta (2 / |deriv thetaModel t + omega|) +
        delta ^ 3 / (2 * T) :=
  norm_thetaFrequencyShortIntegral_le_min_add_linearization_error
    omega hT hTt hdelta hfreq

example (omega : ℝ) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta) :
    ‖thetaFrequencyShortIntegral omega delta t‖ ≤
      thetaFrequencyShortIntegralEnvelope omega T delta t :=
  norm_thetaFrequencyShortIntegral_le_envelope
    omega hT hTt hdelta

end HardyTheorem
