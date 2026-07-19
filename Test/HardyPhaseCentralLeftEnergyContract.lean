import HardyTheorem.HardyPhaseCentralLeftEnergy

open scoped BigOperators

#check HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_left_le

example (s : Finset ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 < delta)
    (hscale : 1 ≤ HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t)
    (hleft : ∀ n ∈ s,
      n < Nat.floor (HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t))
    (hcentral : ∀ n ∈ s,
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t / 8 ≤ n) :
    (∑ n ∈ s,
      Complex.normSq (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤
      48 * delta :=
  HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_left_le
    s ht hdelta hscale hleft hcentral

#print axioms HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_left_le
