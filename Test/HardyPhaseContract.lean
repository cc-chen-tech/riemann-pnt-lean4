import HardyTheorem.OscillatoryIntegral

open Complex Set

namespace HardyTheorem.OscillatoryIntegral

noncomputable section

example (n : ℕ) (t : ℝ) : ℝ := hardyPhase n t

example {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    deriv (hardyPhase n) t =
      (1 / 2) * Real.log (t / (2 * Real.pi * ((n : ℝ) ^ 2))) :=
  deriv_hardyPhase hn ht

example {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (hardyPhase n) t = 1 / (2 * t) :=
  iteratedDeriv_two_hardyPhase hn ht

end

end HardyTheorem.OscillatoryIntegral
