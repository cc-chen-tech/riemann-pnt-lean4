import HardyTheorem.HardyPhaseCorrelation

#check HardyTheorem.OscillatoryIntegral.hardyPhaseCorrelation
#check HardyTheorem.OscillatoryIntegral.deriv_hardyPhaseCorrelation
#check HardyTheorem.OscillatoryIntegral.iteratedDeriv_two_hardyPhaseCorrelation
#check HardyTheorem.OscillatoryIntegral.deriv_hardyPhaseCorrelation_same_shift

example (m n : ℕ) (v w t : ℝ) :
    HardyTheorem.OscillatoryIntegral.hardyPhaseCorrelation m n v w t =
      HardyTheorem.OscillatoryIntegral.hardyPhase m (t + v) -
        HardyTheorem.OscillatoryIntegral.hardyPhase n (t + w) :=
  rfl

#print axioms HardyTheorem.OscillatoryIntegral.deriv_hardyPhaseCorrelation
#print axioms HardyTheorem.OscillatoryIntegral.iteratedDeriv_two_hardyPhaseCorrelation
#print axioms HardyTheorem.OscillatoryIntegral.deriv_hardyPhaseCorrelation_same_shift
