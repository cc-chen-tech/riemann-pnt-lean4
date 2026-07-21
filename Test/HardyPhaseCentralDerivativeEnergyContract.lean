import HardyTheorem.HardyPhaseCentralDerivativeEnergy

open scoped BigOperators

#check HardyTheorem.sum_inv_nat_central_annulus_le
#check HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_central_annulus_le

example (s : Finset ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta)
    (hscale : 1 ≤ HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t)
    (hlower : ∀ n ∈ s,
      HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t / 8 ≤ n)
    (hupper : ∀ n ∈ s,
      (n : ℝ) ≤ 8 *
        HardyTheorem.OscillatoryIntegral.hardyPhaseStationaryScale t) :
    (∑ n ∈ s,
      Complex.normSq
        (deriv (HardyTheorem.hardyPhaseWindowCoeff n delta) t)) ≤
      4 * delta ^ 4 / t ^ 2 :=
  HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_central_annulus_le
    s ht hdelta hscale hlower hupper

#print axioms HardyTheorem.sum_inv_nat_central_annulus_le
#print axioms
  HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_central_annulus_le
