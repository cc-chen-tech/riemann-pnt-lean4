import HardyTheorem.OscillatoryIntegral

open Complex Set
open scoped Interval

namespace HardyTheorem.OscillatoryIntegral

example {F : ℝ → ℝ} {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hF : ContDiff ℝ 2 F)
    (hsecond : (∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 F x) ∨
      (∀ x ∈ Icc a b, iteratedDeriv 2 F x ≤ -r)) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤
      12 / Real.sqrt r :=
  norm_integral_cexp_phase_le_of_second_deriv hab hr hF hsecond

example {n : ℕ} (hn : n ≠ 0) {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..(2 * T), Complex.exp (I * hardyPhase n t)‖ ≤
      12 * Real.sqrt (4 * T) :=
  norm_integral_cexp_hardyPhase_le hn hT

end HardyTheorem.OscillatoryIntegral
