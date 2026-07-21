import HardyTheorem.HardyPhaseFullDerivativeEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

example (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 1 ≤ delta)
    (hscale : 8 ≤ hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s,
      Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
      204 * delta ^ 4 / t ^ 2 :=
  sum_normSq_deriv_hardyPhaseWindowCoeff_full_le_mul
    s N ht hdelta hscale hpos hupper

#print axioms HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_full_le
#print axioms HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_full_le_mul

end HardyTheorem
