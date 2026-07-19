import HardyTheorem.HardyPhaseStationaryScale
import MathlibAux.RealDyadicScale

namespace HardyTheorem

open OscillatoryIntegral

/-- Select dyadic cutoffs which isolate the low and high tails around the
Hardy-phase stationary scale and also dominate a prescribed finite cutoff. -/
theorem exists_hardyPhaseDyadicCutoffs
    {t : ℝ} (ht : 0 < t)
    (hscale : 8 ≤ hardyPhaseStationaryScale t) (N : ℕ) :
    ∃ Klow Khigh L : ℕ,
      (2 : ℝ) ^ (Klow + 1) ≤ hardyPhaseStationaryScale t ∧
      (∀ n : ℕ, (n : ℝ) < hardyPhaseStationaryScale t / 8 →
        n < 2 ^ Klow) ∧
      2 * hardyPhaseStationaryScale t ≤ (2 : ℝ) ^ Khigh ∧
      (2 : ℝ) ^ Khigh ≤ 4 * hardyPhaseStationaryScale t ∧
      (∀ n : ℕ, 8 * hardyPhaseStationaryScale t < (n : ℝ) →
        2 ^ Khigh ≤ n) ∧
      N < 2 ^ L := by
  let r := hardyPhaseStationaryScale t
  have hrpos : 0 < r := by
    dsimp only [r]
    exact hardyPhaseStationaryScale_pos ht
  have hlowOne : 1 ≤ r / 8 := by
    dsimp only [r] at hscale ⊢
    nlinarith [hrpos]
  obtain ⟨Jlow, hJlowLower, hJlowUpper⟩ :=
    MathlibAux.exists_nat_pow_two_le_lt_pow_two hlowOne

  have hhighOne : 1 ≤ 2 * r := by linarith
  obtain ⟨Jhigh, hJhighLower, hJhighUpper⟩ :=
    MathlibAux.exists_nat_pow_two_le_lt_pow_two hhighOne

  have hNOne : 1 ≤ (N : ℝ) + 1 := by norm_num
  obtain ⟨Jlast, -, hJlastUpper⟩ :=
    MathlibAux.exists_nat_pow_two_le_lt_pow_two hNOne

  refine ⟨Jlow + 1, Jhigh + 1, Jlast + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [r] at hJlowLower ⊢
    rw [pow_succ, pow_succ]
    nlinarith
  · intro n hn
    have hnreal : (n : ℝ) < (2 : ℝ) ^ (Jlow + 1) :=
      hn.trans hJlowUpper
    exact_mod_cast hnreal
  · exact hJhighUpper.le
  · rw [pow_succ]
    nlinarith
  · intro n hn
    have hpow : (2 : ℝ) ^ (Jhigh + 1) ≤ 4 * r := by
      rw [pow_succ]
      nlinarith
    have hnreal : (2 : ℝ) ^ (Jhigh + 1) ≤ (n : ℝ) := by
      exact hpow.trans (by linarith)
    exact_mod_cast hnreal
  · have hNreal : (N : ℝ) < (2 : ℝ) ^ (Jlast + 1) := by
      exact (by linarith : (N : ℝ) < (N : ℝ) + 1).trans hJlastUpper
    exact_mod_cast hNreal

end HardyTheorem
