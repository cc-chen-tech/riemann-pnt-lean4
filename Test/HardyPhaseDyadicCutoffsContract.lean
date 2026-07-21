import HardyTheorem.HardyPhaseDyadicCutoffs

open HardyTheorem.OscillatoryIntegral

example {t : ℝ} (ht : 0 < t)
    (hscale : 8 ≤ hardyPhaseStationaryScale t) (N : ℕ) :
    ∃ Klow Khigh L : ℕ,
      (2 : ℝ) ^ (Klow + 1) ≤ hardyPhaseStationaryScale t ∧
      (∀ n : ℕ, (n : ℝ) < hardyPhaseStationaryScale t / 8 →
        n < 2 ^ Klow) ∧
      2 * hardyPhaseStationaryScale t ≤ (2 : ℝ) ^ Khigh ∧
      (2 : ℝ) ^ Khigh ≤ 4 * hardyPhaseStationaryScale t ∧
      (∀ n : ℕ, 8 * hardyPhaseStationaryScale t < (n : ℝ) →
        2 ^ Khigh ≤ n) ∧
      N < 2 ^ L :=
  HardyTheorem.exists_hardyPhaseDyadicCutoffs ht hscale N

#print axioms HardyTheorem.exists_hardyPhaseDyadicCutoffs
