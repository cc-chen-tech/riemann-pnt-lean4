import HardyTheorem.ConreyZetaRightEdge

open Complex
open scoped BigOperators

namespace HardyTheorem

example {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, (n + 2 : ℝ) ^ (-sigma)) ≤
      (2 : ℝ) ^ (-sigma) * (1 + 2 / (sigma - 1)) :=
  tsum_nat_add_two_rpow_le_rightTail hsigma

example {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s - 1‖ ≤
      (2 : ℝ) ^ (-s.re) * (1 + 2 / (s.re - 1)) :=
  norm_riemannZeta_sub_one_le_rightTail hs

example {L : ℝ} (hL : Real.exp 1 ≤ L) {s : ℂ}
    (hre : s.re = 2 * Real.log L) :
    ‖riemannZeta s - 1‖ ≤ 3 / L :=
  norm_riemannZeta_movingRight_sub_one_le hL hre

#print axioms tsum_nat_add_two_rpow_le_rightTail
#print axioms norm_riemannZeta_sub_one_le_rightTail
#print axioms norm_riemannZeta_movingRight_sub_one_le

end HardyTheorem
