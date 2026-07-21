import HardyTheorem.HardyPhaseLinearizedEnergy

open Complex

namespace HardyTheorem.OscillatoryIntegral

/-- The real Dirichlet index at which the first Hardy phase is stationary at
height `t`. -/
noncomputable def hardyPhaseStationaryScale (t : ℝ) : ℝ :=
  Real.sqrt (t / (2 * Real.pi))

theorem hardyPhaseStationaryScale_pos {t : ℝ} (ht : 0 < t) :
    0 < hardyPhaseStationaryScale t := by
  unfold hardyPhaseStationaryScale
  positivity

/-- The Hardy phase frequency is exactly the logarithmic distance from the
stationary real index. -/
theorem deriv_hardyPhase_eq_log_stationaryScale_div
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    deriv (hardyPhase n) t =
      Real.log (hardyPhaseStationaryScale t / n) := by
  rw [deriv_hardyPhase hn ht]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : ((n : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 hnreal
  have htwoPi : 2 * Real.pi ≠ 0 := by positivity
  have hratio : 0 ≤ t / (2 * Real.pi) := by positivity
  have hsqrt : Real.sqrt (t / (2 * Real.pi)) ≠ 0 := by positivity
  unfold hardyPhaseStationaryScale
  rw [Real.log_div hsqrt hnreal, Real.log_sqrt hratio,
    Real.log_div (ne_of_gt ht) htwoPi,
    Real.log_div (ne_of_gt ht) (mul_ne_zero htwoPi hn2),
    Real.log_mul htwoPi hn2, Real.log_pow]
  push_cast
  ring

theorem abs_deriv_hardyPhase_eq_abs_log_stationaryScale_div
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    |deriv (hardyPhase n) t| =
      |Real.log (hardyPhaseStationaryScale t / n)| := by
  rw [deriv_hardyPhase_eq_log_stationaryScale_div hn ht]

end HardyTheorem.OscillatoryIntegral
