import HardyTheorem.HardyPhaseCentralRightEnergy

open scoped BigOperators

#check HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_right_le

example (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 < delta)
    (hscale : 1 ≤ HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t)
    (hright : ∀ n ∈ s,
      Nat.floor (HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t) + 1 < n)
    (hupperNat : ∀ n ∈ s, n ≤ N)
    (hcentral : ∀ n ∈ s,
      (n : ℝ) ≤ 8 * HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t) :
    (∑ n ∈ s,
      Complex.normSq (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤
      48 * delta :=
  HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_right_le
    s N ht hdelta hscale hright hupperNat hcentral

#print axioms HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_central_right_le
