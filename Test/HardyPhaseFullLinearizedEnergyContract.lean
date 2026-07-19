import HardyTheorem.HardyPhaseFullLinearizedEnergy

open scoped BigOperators

#check HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_full_le
#check HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_full_le_mul

example (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 < delta)
    (hscale : 8 ≤
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s,
      Complex.normSq (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤
      96 * delta +
        16 * delta ^ 2 /
          HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t +
        16 / (Real.log 2) ^ 2 :=
  HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_full_le
    s N ht hdelta hscale hpos hupper

example (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 1 ≤ delta)
    (hscale : 8 ≤
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t)
    (hwindow : delta ≤
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s,
      Complex.normSq (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤
      200 * delta :=
  HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_full_le_mul
    s N ht hdelta hscale hwindow hpos hupper

#print axioms HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_full_le
#print axioms HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_full_le_mul
