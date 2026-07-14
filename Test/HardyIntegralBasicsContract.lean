import HardyTheorem

open Complex Filter Set Topology
open scoped Interval

namespace HardyTheorem

example (t : ℝ) :
    |hardyZ t| = ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ :=
  abs_hardyZ_eq_norm_riemannZeta t

example {T : ℝ} (hT : 0 ≤ T)
    (h_sign :
      (∀ t ∈ Set.Icc T (2 * T), 0 ≤ hardyZ t) ∨
        (∀ t ∈ Set.Icc T (2 * T), hardyZ t ≤ 0)) :
    |∫ t in T..(2 * T), hardyZ t| =
      ∫ t in T..(2 * T), |hardyZ t| :=
  abs_integral_hardyZ_eq_integral_abs_of_const_sign hT h_sign

example (h_bdd : Bornology.IsBounded {t : ℝ | hardyZ t = 0}) :
    ∀ᶠ T : ℝ in atTop,
      |∫ t in T..(2 * T), hardyZ t| =
        ∫ t in T..(2 * T),
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ :=
  eventually_abs_integral_hardyZ_eq_integral_norm_zeta_of_bounded_zeros h_bdd

end HardyTheorem
