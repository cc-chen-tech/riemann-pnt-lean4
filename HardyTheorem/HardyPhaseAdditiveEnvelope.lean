import HardyTheorem.HardyPhaseFrequencyLowerBound
import HardyTheorem.HardyPhaseLinearizedEnergy

open Complex

namespace HardyTheorem

open OscillatoryIntegral

/-- The Hardy short-window envelope expressed only through additive distance
from the stationary real index. -/
noncomputable def hardyPhaseAdditiveEnvelope
    (n : ℕ) (delta t : ℝ) : ℝ :=
  if hardyPhaseStationaryScale t = (n : ℝ) then delta
  else min delta
    (2 * max (hardyPhaseStationaryScale t) n /
      |hardyPhaseStationaryScale t - n|)

theorem hardyPhaseLinearizedEnvelope_le_length
    (n : ℕ) {delta t : ℝ} :
    hardyPhaseLinearizedEnvelope n delta t ≤ delta := by
  unfold hardyPhaseLinearizedEnvelope
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private theorem deriv_hardyPhase_ne_zero_of_stationaryScale_ne
    {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t)
    (haway : hardyPhaseStationaryScale t ≠ (n : ℝ)) :
    deriv (hardyPhase n) t ≠ 0 := by
  intro hzero
  have hlog : Real.log (hardyPhaseStationaryScale t / n) = 0 := by
    rw [← deriv_hardyPhase_eq_log_stationaryScale_div hn ht]
    exact hzero
  have hratioPos : 0 < hardyPhaseStationaryScale t / (n : ℝ) :=
    div_pos (hardyPhaseStationaryScale_pos ht)
      (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have hratio : hardyPhaseStationaryScale t / (n : ℝ) = 1 :=
    Real.eq_one_of_pos_of_log_eq_zero hratioPos hlog
  apply haway
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnreal] at hratio
  exact hratio

/-- The frequency envelope is bounded by the additive stationary-distance
envelope, including the exact stationary case. -/
theorem hardyPhaseLinearizedEnvelope_le_additiveEnvelope
    {n : ℕ} (hn : n ≠ 0) {delta t : ℝ}
    (ht : 0 < t) :
    hardyPhaseLinearizedEnvelope n delta t ≤
      hardyPhaseAdditiveEnvelope n delta t := by
  by_cases haway : hardyPhaseStationaryScale t = (n : ℝ)
  · rw [hardyPhaseAdditiveEnvelope, if_pos haway]
    exact hardyPhaseLinearizedEnvelope_le_length n
  · rw [hardyPhaseAdditiveEnvelope, if_neg haway,
      hardyPhaseLinearizedEnvelope,
      if_neg (deriv_hardyPhase_ne_zero_of_stationaryScale_ne hn ht haway)]
    exact min_le_min_left delta
      (two_div_abs_deriv_hardyPhase_le hn ht haway)

theorem hardyPhaseAdditiveEnvelope_nonneg
    (n : ℕ) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ hardyPhaseAdditiveEnvelope n delta t := by
  unfold hardyPhaseAdditiveEnvelope
  split_ifs
  · exact hdelta
  · exact le_min hdelta (by positivity)

theorem hardyPhaseAdditiveEnvelope_le_length
    (n : ℕ) {delta t : ℝ} :
    hardyPhaseAdditiveEnvelope n delta t ≤ delta := by
  unfold hardyPhaseAdditiveEnvelope
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- Each linearized Hardy coefficient is controlled by the purely additive
stationary-distance envelope. -/
theorem normSq_hardyPhaseLinearizedCoeff_le_additiveEnvelope
    {n : ℕ} (hn : 0 < n) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta) :
    Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
      ((Real.sqrt n)⁻¹ * hardyPhaseAdditiveEnvelope n delta t) ^ 2 := by
  refine (normSq_hardyPhaseLinearizedCoeff_le_envelope hn hdelta).trans ?_
  have hleft : 0 ≤ (Real.sqrt n)⁻¹ *
      hardyPhaseLinearizedEnvelope n delta t :=
    mul_nonneg (by positivity)
      (hardyPhaseLinearizedEnvelope_nonneg n hdelta)
  have hright : 0 ≤ (Real.sqrt n)⁻¹ *
      hardyPhaseAdditiveEnvelope n delta t :=
    mul_nonneg (by positivity)
      (hardyPhaseAdditiveEnvelope_nonneg n hdelta)
  have hle : (Real.sqrt n)⁻¹ *
      hardyPhaseLinearizedEnvelope n delta t ≤
      (Real.sqrt n)⁻¹ * hardyPhaseAdditiveEnvelope n delta t :=
    mul_le_mul_of_nonneg_left
      (hardyPhaseLinearizedEnvelope_le_additiveEnvelope
        (Nat.ne_of_gt hn) ht) (by positivity)
  exact (sq_le_sq₀ hleft hright).2 hle

/-- The unconditional length-energy estimate used for the one or two integer
indices nearest the stationary real scale. -/
theorem normSq_hardyPhaseLinearizedCoeff_le_length
    {n : ℕ} (hn : 0 < n) {delta t : ℝ} (hdelta : 0 ≤ delta) :
    Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
      ((Real.sqrt n)⁻¹ * delta) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have hleft : 0 ≤ ‖hardyPhaseLinearizedCoeff n delta t‖ := norm_nonneg _
  have hright : 0 ≤ (Real.sqrt n)⁻¹ * delta :=
    mul_nonneg (by positivity) hdelta
  exact (sq_le_sq₀ hleft hright).2
    (norm_hardyPhaseLinearizedCoeff_le_length hn hdelta)

end HardyTheorem
