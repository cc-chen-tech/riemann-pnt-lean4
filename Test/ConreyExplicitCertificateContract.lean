import HardyTheorem.ConreyExplicitCertificate

namespace HardyTheorem

/-!
# Contract for the explicit Conrey two-fifths numerical certificate

This catches an incorrect mollifier-length comparison, a weakened exponential
estimate, or a sign error in the final logarithmic proportion calculation.
-/

example : conreyExplicitTheta < (4 : ℝ) / 7 :=
  conreyExplicitTheta_lt_four_sevenths

example : conreyExplicitMeanSquareConstant < Real.exp (18 / 25 : ℝ) :=
  conreyExplicitMeanSquareConstant_lt_exp

example : (2 : ℝ) / 5 < 1 - Real.log conreyExplicitMeanSquareConstant / (6 / 5) :=
  conreyExplicitProportion_gt_two_fifths

#print axioms conreyExplicitTheta_lt_four_sevenths
#print axioms conreyExplicitMeanSquareConstant_lt_exp
#print axioms conreyExplicitProportion_gt_two_fifths

end HardyTheorem
