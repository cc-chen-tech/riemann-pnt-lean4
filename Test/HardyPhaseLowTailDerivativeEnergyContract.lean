import HardyTheorem.HardyPhaseLowTailDerivativeEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

example (s : Finset ℕ) (K : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 1 ≤ delta)
    (hscale : (2 : ℝ) ^ (K + 1) ≤ hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K) :
    (∑ n ∈ s, Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
      25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) :=
  sum_normSq_deriv_hardyPhaseWindowCoeff_far_low_le
    s K ht hdelta hscale hpos hbound

#print axioms HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_far_low_le

end HardyTheorem
