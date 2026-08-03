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

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    0 < carlsonTwoHeightDensityExponent sigma :=
  carlsonTwoHeightDensityExponent_pos hhalf hone

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    carlsonTwoHeightDensityExponent sigma < 1 :=
  carlsonTwoHeightDensityExponent_lt_one hhalf

example {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    0 < carlsonTwoHeightBalancedCut sigma alpha :=
  carlsonTwoHeightBalancedCut_pos hhalf hone halpha

example {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    carlsonTwoHeightBalancedCut sigma alpha < alpha :=
  carlsonTwoHeightBalancedCut_lt_alpha hhalf hone halpha

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
  targetAmplitudeCarlsonTwoHeightBalancedSlope_pos hhalf hone

example {beta sigma tau alpha : ℝ}
    (hden : carlsonTwoHeightDensityExponent sigma + 1 ≠ 0) :
    targetAmplitudeCarlsonTwoHeightLowExponent beta sigma tau
        (carlsonTwoHeightBalancedCut sigma alpha) =
      targetAmplitudeCarlsonTwoHeightBalancedExponent
        beta sigma tau alpha :=
  targetAmplitudeCarlsonTwoHeightLowExponent_balanced hden

example {beta sigma tau alpha : ℝ}
    (hden : carlsonTwoHeightDensityExponent sigma + 1 ≠ 0) :
    targetAmplitudeCarlsonTwoHeightHighExponent beta sigma tau alpha
        (carlsonTwoHeightBalancedCut sigma alpha) =
      targetAmplitudeCarlsonTwoHeightBalancedExponent
        beta sigma tau alpha :=
  targetAmplitudeCarlsonTwoHeightHighExponent_balanced hden

example {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma < 1 / 2 :=
  targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half hhalf hone

end PrimeNumberTheorem
