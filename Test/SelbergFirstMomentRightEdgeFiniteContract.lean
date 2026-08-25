import HardyTheorem.SelbergFirstMomentRightEdgeFinite

open Complex

namespace HardyTheorem

#check selbergFirstMomentRightTriplePolynomial
#check finiteZeta_mul_sqrtZetaMollifier_sq_rightLine_eq
#check norm_intervalIntegral_selbergFirstMomentRightTriplePolynomial_sub_one_le

example {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (a b : ℝ) :
    ‖∫ t in a..b,
        (selbergFirstMomentRightTriplePolynomial N X t - 1)‖ ≤
      16 / Real.log 2 :=
  norm_intervalIntegral_selbergFirstMomentRightTriplePolynomial_sub_one_le
    hN hX

#print axioms finiteZeta_mul_sqrtZetaMollifier_sq_rightLine_eq
#print axioms norm_intervalIntegral_selbergFirstMomentRightTriplePolynomial_sub_one_le

end HardyTheorem
