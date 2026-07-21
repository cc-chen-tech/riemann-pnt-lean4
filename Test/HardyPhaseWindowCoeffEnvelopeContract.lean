import HardyTheorem.HardyPhaseWindowCoeffEnvelope

#check HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le_min
#check HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le_trivial

example {n : ℕ} (hn : 0 < n) {delta t : ℝ}
    (hdelta : 0 ≤ delta) (ht : 0 < t)
    (hfreq : deriv HardyTheorem.thetaModel t - Real.log n ≠ 0) :
    ‖deriv (HardyTheorem.hardyPhaseWindowCoeff n delta) t‖ ≤
      (Real.sqrt n)⁻¹ * (1 / (2 * t)) *
        min (delta ^ 2 / 2)
          (delta / |deriv HardyTheorem.thetaModel t - Real.log n| +
            2 / (deriv HardyTheorem.thetaModel t - Real.log n) ^ 2) :=
  HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le_min
    hn hdelta ht hfreq

#print axioms HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le_min
#print axioms HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le_trivial
