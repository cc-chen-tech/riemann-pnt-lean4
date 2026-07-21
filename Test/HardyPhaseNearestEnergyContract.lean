import HardyTheorem.HardyPhaseNearestEnergy

open scoped BigOperators

#check HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_nearest_le

example {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta)
    (hscale : 1 ≤
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t) :
    (∑ n ∈ ({
        Nat.floor
          (HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t),
        Nat.floor
          (HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t) + 1
      } : Finset ℕ),
      Complex.normSq
        (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤
      16 * delta ^ 2 /
        HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t :=
  HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_nearest_le
    ht hdelta hscale

#print axioms HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_nearest_le
