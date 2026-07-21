import HardyTheorem.HardyPhaseStationaryScale

#check HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale
#check HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale_pos
#check HardyTheorem.OscillatoryIntegral.deriv_hardyPhase_eq_log_stationaryScale_div
#check HardyTheorem.OscillatoryIntegral.abs_deriv_hardyPhase_eq_abs_log_stationaryScale_div

example {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    deriv (HardyTheorem.OscillatoryIntegral.hardyPhase n) t =
      Real.log
        (HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t / n) :=
  HardyTheorem.OscillatoryIntegral.deriv_hardyPhase_eq_log_stationaryScale_div
    hn ht

#print axioms HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale_pos
#print axioms HardyTheorem.OscillatoryIntegral.deriv_hardyPhase_eq_log_stationaryScale_div
#print axioms HardyTheorem.OscillatoryIntegral.abs_deriv_hardyPhase_eq_abs_log_stationaryScale_div
