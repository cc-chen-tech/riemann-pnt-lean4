import HardyTheorem.ConreyExplicitIntegralBridge

namespace HardyTheorem

/-!
# Contract for the explicit Conrey mean-square integral

This catches a wrong coefficient, derivative sign, endpoint normalization,
or exponential antiderivative in the bridge from Conrey's double integral to
the independently certified closed-form constant.
-/

example :
    conreyExplicitMeanSquareIntegral =
      conreyExplicitMeanSquareConstant :=
  conreyExplicitMeanSquareIntegral_eq_constant

example :
    conreyExplicitMeanSquareIntegral < Real.exp (18 / 25 : ℝ) :=
  conreyExplicitMeanSquareIntegral_lt_exp

example :
    (2 : ℝ) / 5 <
      1 - Real.log conreyExplicitMeanSquareIntegral / conreyExplicitR :=
  conreyExplicitIntegralProportion_gt_two_fifths

#print axioms conreyExplicitInnerIntegral_eq
#print axioms conreyExplicitMeanSquareIntegral_eq_constant
#print axioms conreyExplicitIntegralProportion_gt_two_fifths

end HardyTheorem
