import HardyTheorem.HardyPhaseStationaryScale
import MathlibAux.LogRatioLowerBound

open Complex

namespace HardyTheorem.OscillatoryIntegral

/-- Additive distance from the stationary real index gives a lower bound for
the Hardy phase frequency. -/
theorem abs_sub_stationaryScale_div_max_le_abs_deriv_hardyPhase
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    |hardyPhaseStationaryScale t - n| /
        max (hardyPhaseStationaryScale t) n ≤
      |deriv (hardyPhase n) t| := by
  rw [abs_deriv_hardyPhase_eq_abs_log_stationaryScale_div hn ht]
  exact MathlibAux.abs_sub_div_max_le_abs_log_div
    (hardyPhaseStationaryScale_pos ht) (by exact_mod_cast Nat.pos_of_ne_zero hn)

/-- Away from the stationary real index, the reciprocal-frequency factor is
bounded by a rational additive-distance envelope. -/
theorem two_div_abs_deriv_hardyPhase_le
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t)
    (haway : hardyPhaseStationaryScale t ≠ (n : ℝ)) :
    2 / |deriv (hardyPhase n) t| ≤
      2 * max (hardyPhaseStationaryScale t) n /
        |hardyPhaseStationaryScale t - n| := by
  have hdist : 0 < |hardyPhaseStationaryScale t - n| :=
    abs_pos.mpr (sub_ne_zero.mpr haway)
  have hmax : 0 < max (hardyPhaseStationaryScale t) n :=
    (hardyPhaseStationaryScale_pos ht).trans_le
      (le_max_left _ _)
  have hratio :
      0 < |hardyPhaseStationaryScale t - n| /
        max (hardyPhaseStationaryScale t) n := div_pos hdist hmax
  have hlower :=
    abs_sub_stationaryScale_div_max_le_abs_deriv_hardyPhase hn ht
  calc
    2 / |deriv (hardyPhase n) t| ≤
        2 / (|hardyPhaseStationaryScale t - n| /
          max (hardyPhaseStationaryScale t) n) :=
      div_le_div_of_nonneg_left (by norm_num) hratio hlower
    _ = 2 * max (hardyPhaseStationaryScale t) n /
        |hardyPhaseStationaryScale t - n| := by
      field_simp

end HardyTheorem.OscillatoryIntegral
