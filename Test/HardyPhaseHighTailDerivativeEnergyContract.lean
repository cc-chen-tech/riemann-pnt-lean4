import HardyTheorem.HardyPhaseHighTailDerivativeEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

example (s : Finset ℕ) (K L : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 1 ≤ delta)
    (hscale : 2 * hardyPhaseStationaryScale t ≤ (2 : ℝ) ^ K)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hlower : ∀ n ∈ s, 2 ^ K ≤ n)
    (hupper : ∀ n ∈ s, n < 2 ^ L) :
    (∑ n ∈ s, Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
      25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) :=
  sum_normSq_deriv_hardyPhaseWindowCoeff_far_high_le
    s K L ht hdelta hscale hpos hlower hupper

#print axioms HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_far_high_le

end HardyTheorem
