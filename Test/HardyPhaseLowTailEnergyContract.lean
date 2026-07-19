import HardyTheorem.HardyPhaseLowTailEnergy

open scoped BigOperators

open Complex

example (s : Finset ℕ) (K : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta)
    (hscale : (2 : ℝ) ^ (K + 1) ≤
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K) :
    (∑ n ∈ s,
      Complex.normSq
        (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤
      8 / (Real.log 2) ^ 2 :=
  HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_far_low_le
    s K ht hdelta hscale hpos hbound

#print axioms HardyTheorem.logTwo_mul_dyadicDistance_le_abs_deriv_hardyPhase
#print axioms HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_far_low_le
