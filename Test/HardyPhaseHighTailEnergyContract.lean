import HardyTheorem.HardyPhaseHighTailEnergy

open scoped BigOperators

open Complex

example {K k n : ℕ} (hKk : K ≤ k) (hn : 0 < n) {t : ℝ}
    (ht : 0 < t)
    (hscale : 2 *
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t ≤
        (2 : ℝ) ^ K)
    (hnlower : 2 ^ k ≤ n) :
    (((k - K + 1 : ℕ) : ℝ) * Real.log 2) ≤
      |deriv (HardyTheorem.OscillatoryIntegral.hardyPhase n) t| :=
  HardyTheorem.highDyadicDistance_mul_logTwo_le_abs_deriv_hardyPhase
    hKk hn ht hscale hnlower

example (s : Finset ℕ) (K L : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta)
    (hscale : 2 *
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t ≤
        (2 : ℝ) ^ K)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hlower : ∀ n ∈ s, 2 ^ K ≤ n)
    (hupper : ∀ n ∈ s, n < 2 ^ L) :
    (∑ n ∈ s,
      Complex.normSq
        (HardyTheorem.hardyPhaseLinearizedCoeff n delta t)) ≤
      8 / (Real.log 2) ^ 2 :=
  HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_far_high_le
    s K L ht hdelta hscale hpos hlower hupper

#print axioms HardyTheorem.highDyadicDistance_mul_logTwo_le_abs_deriv_hardyPhase
#print axioms HardyTheorem.sum_normSq_hardyPhaseLinearizedCoeff_far_high_le
