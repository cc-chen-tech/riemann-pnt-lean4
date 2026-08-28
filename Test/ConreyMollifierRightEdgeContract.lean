import HardyTheorem.ConreyMollifierRightEdge

open Complex Set

namespace HardyTheorem

example {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |conreyExplicitP x| ≤ 1 :=
  abs_conreyExplicitP_le_one hx

example {Y : ℕ} {sigma0 : ℝ} {P : ℝ → ℝ} {s : ℂ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hP1 : P 1 = 1)
    (hP : ∀ x ∈ Set.Icc (0 : ℝ) 1, |P x| ≤ 1)
    (hs : 1 < s.re) :
    ‖conreyMollifier Y sigma0 P s - 1‖ ≤
      (2 : ℝ) ^ (-s.re) * (1 + 2 / (s.re - 1)) :=
  norm_conreyMollifier_sub_one_le_rightTail hY hsigma0 hP1 hP hs

example {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : Real.exp 1 ≤ L) :
    ‖conreyMollifier Y sigma0 conreyExplicitP
        ((2 * Real.log L : ℂ) + I * t) - 1‖ ≤ 3 / L :=
  norm_conreyExplicitMollifier_movingRight_sub_one_le hY hsigma0 hL t

#print axioms abs_conreyExplicitP_le_one
#print axioms norm_conreyMollifier_sub_one_le_rightTail
#print axioms norm_conreyExplicitMollifier_movingRight_sub_one_le

end HardyTheorem
