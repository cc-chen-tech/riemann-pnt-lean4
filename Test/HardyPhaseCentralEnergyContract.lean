import HardyTheorem.HardyPhaseCentralEnergy

open scoped BigOperators

#check HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_le

example (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 < delta)
    (hscale : 1 ≤ HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t)
    (hupperNat : ∀ n ∈ s, n ≤ N)
    (hlower : ∀ n ∈ s,
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t / 8 ≤ n)
    (hupper : ∀ n ∈ s,
      (n : ℝ) ≤ 8 *
        HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t) :
    (∑ n ∈ s,
      Complex.normSq (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤
      96 * delta + 16 * delta ^ 2 /
        HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t :=
  HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_le
    s N ht hdelta hscale hupperNat hlower hupper

#print axioms HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_le
