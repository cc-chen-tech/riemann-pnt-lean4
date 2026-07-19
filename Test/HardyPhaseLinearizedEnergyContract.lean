import HardyTheorem.HardyPhaseLinearizedEnergy

#check HardyTheorem.hardyPhaseLinearizedCoeff
#check HardyTheorem.hardyPhaseLinearizedEnvelope
#check HardyTheorem.norm_hardyPhaseLinearizedCoeff_le_min
#check HardyTheorem.norm_hardyPhaseLinearizedCoeff_le_length
#check HardyTheorem.normSq_hardyPhaseLinearizedCoeff_le
#check HardyTheorem.hardyPhaseLinearizedEnvelope_nonneg
#check HardyTheorem.norm_hardyPhaseLinearizedCoeff_le_envelope
#check HardyTheorem.normSq_hardyPhaseLinearizedCoeff_le_envelope

example {n : ℕ} (hn : 0 < n) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    Complex.normSq (HardyTheorem.hardyPhaseLinearizedCoeff n delta t) ≤
      ((Real.sqrt n)⁻¹ *
        HardyTheorem.hardyPhaseLinearizedEnvelope n delta t) ^ 2 :=
  HardyTheorem.normSq_hardyPhaseLinearizedCoeff_le_envelope hn hdelta

#print axioms HardyTheorem.norm_hardyPhaseLinearizedCoeff_le_min
#print axioms HardyTheorem.norm_hardyPhaseLinearizedCoeff_le_length
#print axioms HardyTheorem.normSq_hardyPhaseLinearizedCoeff_le
#print axioms HardyTheorem.normSq_hardyPhaseLinearizedCoeff_le_envelope
