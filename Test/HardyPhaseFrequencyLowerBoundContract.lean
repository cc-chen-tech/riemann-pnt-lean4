import HardyTheorem.HardyPhaseFrequencyLowerBound

#check HardyTheorem.OscillatoryIntegral.abs_sub_stationaryScale_div_max_le_abs_deriv_hardyPhase
#check HardyTheorem.OscillatoryIntegral.two_div_abs_deriv_hardyPhase_le

example {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t)
    (haway : HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t ≠
      (n : ℝ)) :
    2 / |deriv (HardyTheorem.OscillatoryIntegral.hardyPhase n) t| ≤
      2 * max
          (HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t) n /
        |HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t - n| :=
  HardyTheorem.OscillatoryIntegral.two_div_abs_deriv_hardyPhase_le hn ht haway

#print axioms HardyTheorem.OscillatoryIntegral.abs_sub_stationaryScale_div_max_le_abs_deriv_hardyPhase
#print axioms HardyTheorem.OscillatoryIntegral.two_div_abs_deriv_hardyPhase_le
