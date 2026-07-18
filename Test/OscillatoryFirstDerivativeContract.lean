import HardyTheorem.OscillatoryIntegral

open Complex Set
open scoped Interval

namespace HardyTheorem.OscillatoryIntegral

example {F : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hF : ContDiff ℝ 2 F)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 4 / m :=
  norm_integral_cexp_phase_le_of_monotone_deriv hab hm hF hmono haway

end HardyTheorem.OscillatoryIntegral
