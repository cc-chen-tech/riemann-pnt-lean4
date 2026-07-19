import HardyTheorem.HardyPhaseAdditiveEnvelope

#check HardyTheorem.hardyPhaseAdditiveEnvelope
#check HardyTheorem.hardyPhaseLinearizedEnvelope_le_additiveEnvelope
#check HardyTheorem.normSq_hardyPhaseLinearizedCoeff_le_additiveEnvelope

example {n : ℕ} (hn : 0 < n) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta) :
    Complex.normSq (HardyTheorem.hardyPhaseLinearizedCoeff n delta t) ≤
      ((Real.sqrt n)⁻¹ *
        HardyTheorem.hardyPhaseAdditiveEnvelope n delta t) ^ 2 :=
  HardyTheorem.normSq_hardyPhaseLinearizedCoeff_le_additiveEnvelope
    hn ht hdelta

#print axioms HardyTheorem.hardyPhaseLinearizedEnvelope_le_additiveEnvelope
#print axioms HardyTheorem.normSq_hardyPhaseLinearizedCoeff_le_additiveEnvelope
