import PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightNumericalCore

namespace PrimeNumberTheorem

example (sigma : ℝ) :
    carlsonTwoHeightDensityExponent sigma =
      4 * sigma * (1 - sigma) := rfl

example (sigma alpha : ℝ) :
    carlsonTwoHeightBalancedCut sigma alpha =
      carlsonTwoHeightDensityExponent sigma * alpha /
        (carlsonTwoHeightDensityExponent sigma + 1) := rfl

example (beta sigma tau gamma : ℝ) :
    targetAmplitudeCarlsonTwoHeightLowExponent beta sigma tau gamma =
      carlsonTwoHeightDensityExponent sigma * gamma + tau - beta := rfl

example (beta sigma tau alpha gamma : ℝ) :
    targetAmplitudeCarlsonTwoHeightHighExponent
        beta sigma tau alpha gamma =
      carlsonTwoHeightDensityExponent sigma * alpha + tau - beta - gamma := rfl

example (sigma : ℝ) :
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma =
      carlsonTwoHeightDensityExponent sigma ^ 2 /
        (carlsonTwoHeightDensityExponent sigma + 1) := rfl

example (beta sigma tau alpha : ℝ) :
    targetAmplitudeCarlsonTwoHeightBalancedExponent beta sigma tau alpha =
      tau - beta +
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma * alpha := rfl

#check carlsonTwoHeightDensityExponent_pos
#check carlsonTwoHeightDensityExponent_lt_one
#check carlsonTwoHeightBalancedCut_pos
#check carlsonTwoHeightBalancedCut_lt_alpha
#check targetAmplitudeCarlsonTwoHeightLowExponent_balanced
#check targetAmplitudeCarlsonTwoHeightHighExponent_balanced
#check targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
#check targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half

end PrimeNumberTheorem
