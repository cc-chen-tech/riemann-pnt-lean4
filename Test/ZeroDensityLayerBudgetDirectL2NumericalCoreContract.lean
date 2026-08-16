import PrimeNumberTheorem.ZeroDensityLayerBudgetDirectL2NumericalCore

namespace PrimeNumberTheorem

example (beta lambda theta gamma sigma : ℝ) :
    directL2RightPowerExponent beta lambda theta gamma sigma =
      2 * lambda * (sigma - beta) +
        gamma * (carlsonTwoHeightDensityExponent sigma - 2 + theta) := rfl

example (beta theta gamma sigma : ℝ) :
    directL2LeftPowerExponent beta theta gamma sigma =
      2 * (sigma - beta) +
        gamma * (carlsonTwoHeightDensityExponent sigma - 2 + theta) := rfl

example (beta lambda theta : ℝ) :
    directL2CriticalRightHeight beta lambda theta =
      2 * lambda * (1 - beta) / (2 - theta) := rfl

example (beta theta : ℝ) :
    directL2FeasibilityGap beta theta = 4 * beta - 2 - theta := rfl

example (beta lambda theta : ℝ) :
    directL2RightHeightWitness beta lambda theta =
      (directL2CriticalRightHeight beta lambda theta + lambda / 2) / 2 := rfl

example (beta lambda theta : ℝ) :
    directL2RightPowerMargin beta lambda theta =
      lambda * directL2FeasibilityGap beta theta / 4 := rfl

example : directL2LeftHeight = (1 / 8 : ℝ) := rfl

example (beta theta : ℝ) :
    directL2LeftPowerMargin beta theta =
      (4 * (1 - beta) ^ 2 + directL2FeasibilityGap beta theta) / 8 := rfl

example (beta lambda theta gamma sigma : ℝ) :
    directL2RightPowerExponent beta lambda theta gamma 1 -
        directL2RightPowerExponent beta lambda theta gamma sigma =
      2 * (1 - sigma) * (lambda - 2 * gamma * sigma) :=
  directL2RightPowerExponent_one_sub beta lambda theta gamma sigma

example (beta lambda theta gamma : ℝ) (htheta : theta ≠ 2) :
    directL2RightPowerExponent beta lambda theta gamma 1 =
      (2 - theta) *
        (directL2CriticalRightHeight beta lambda theta - gamma) :=
  directL2RightPowerExponent_one_eq_criticalGap beta lambda theta gamma htheta

example (beta lambda theta : ℝ) (hlambda : 0 < lambda) (htheta : theta < 2) :
    directL2CriticalRightHeight beta lambda theta < lambda / 2 ↔
      theta < 4 * beta - 2 :=
  directL2CriticalRightHeight_lt_half_iff beta lambda theta hlambda htheta

example (beta theta : ℝ) (hbeta : beta < 1)
    (hfeasible : theta < 4 * beta - 2) : theta < 2 :=
  directL2_theta_lt_two_of_feasible beta theta hbeta hfeasible

example (beta lambda theta : ℝ) (hbeta : beta < 1) (hlambda : 0 < lambda)
    (hfeasible : theta < 4 * beta - 2) :
    0 < directL2RightHeightWitness beta lambda theta :=
  directL2RightHeightWitness_pos beta lambda theta hbeta hlambda hfeasible

example (beta lambda theta : ℝ) (hbeta : beta < 1) (hlambda : 0 < lambda)
    (hfeasible : theta < 4 * beta - 2) :
    directL2RightHeightWitness beta lambda theta < lambda / 2 :=
  directL2RightHeightWitness_lt_half beta lambda theta hbeta hlambda hfeasible

example (beta lambda theta : ℝ) (hlambda : 0 < lambda)
    (hfeasible : theta < 4 * beta - 2) :
    0 < directL2RightPowerMargin beta lambda theta :=
  directL2RightPowerMargin_pos beta lambda theta hlambda hfeasible

example (beta lambda theta : ℝ) (hbeta : beta < 1)
    (hfeasible : theta < 4 * beta - 2) :
    directL2RightPowerExponent beta lambda theta
        (directL2RightHeightWitness beta lambda theta) 1 =
      -directL2RightPowerMargin beta lambda theta :=
  directL2RightPowerExponent_witness_one beta lambda theta hbeta hfeasible

example (beta lambda theta sigma : ℝ)
    (hbetaHalf : 1 / 2 < beta) (hbetaOne : beta < 1)
    (hlambda : 0 < lambda) (hfeasible : theta < 4 * beta - 2)
    (hbetaSigma : beta ≤ sigma) (hsigmaOne : sigma ≤ 1) :
    directL2RightPowerExponent beta lambda theta
        (directL2RightHeightWitness beta lambda theta) sigma ≤
      -directL2RightPowerMargin beta lambda theta :=
  directL2RightPowerExponent_witness_le_neg_margin beta lambda theta sigma
    hbetaHalf hbetaOne hlambda hfeasible hbetaSigma hsigmaOne

example (beta theta gamma sigma : ℝ) :
    directL2LeftPowerExponent beta theta gamma beta -
        directL2LeftPowerExponent beta theta gamma sigma =
      2 * (beta - sigma) *
        (1 + 2 * gamma * (1 - beta - sigma)) :=
  directL2LeftPowerExponent_beta_sub beta theta gamma sigma

example (beta theta : ℝ) :
    directL2LeftPowerExponent beta theta directL2LeftHeight beta =
      -directL2LeftPowerMargin beta theta :=
  directL2LeftPowerExponent_fixed_beta beta theta

example (beta theta : ℝ) (hfeasible : theta < 4 * beta - 2) :
    0 < directL2LeftPowerMargin beta theta :=
  directL2LeftPowerMargin_pos beta theta hfeasible

example (beta theta sigma : ℝ) (hbetaOne : beta < 1)
    (hfeasible : theta < 4 * beta - 2)
    (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaBeta : sigma ≤ beta) :
    directL2LeftPowerExponent beta theta directL2LeftHeight sigma ≤
      -directL2LeftPowerMargin beta theta :=
  directL2LeftPowerExponent_fixed_le_neg_margin beta theta sigma
    hbetaOne hfeasible hsigmaHalf hsigmaBeta

example (beta lambda theta gamma : ℝ) (hbeta : beta < 1)
    (hlambda : 0 < lambda) (hgammaNonneg : 0 ≤ gamma)
    (hgammaHalf : gamma < lambda / 2)
    (hnegative : directL2RightPowerExponent beta lambda theta gamma 1 < 0) :
    theta < 4 * beta - 2 :=
  directL2_theta_lt_four_beta_sub_two_of_right_endpoint_neg
    beta lambda theta gamma hbeta hlambda hgammaNonneg hgammaHalf hnegative

example (beta lambda theta : ℝ) (hbeta : beta < 1) (hlambda : 0 < lambda) :
    (∃ gamma : ℝ,
      0 ≤ gamma ∧ gamma < lambda / 2 ∧
        directL2RightPowerExponent beta lambda theta gamma 1 < 0) ↔
      theta < 4 * beta - 2 :=
  exists_directL2_rightHeight_iff beta lambda theta hbeta hlambda

example (beta lambda : ℝ) (hbeta : beta < 1) :
    directL2CriticalRightHeight beta lambda (4 * beta - 2) = lambda / 2 :=
  directL2CriticalRightHeight_boundary beta lambda hbeta

example (beta lambda : ℝ) :
    directL2RightPowerExponent beta lambda (4 * beta - 2) (lambda / 2) 1 = 0 :=
  directL2RightPowerExponent_boundary_half beta lambda

example (beta lambda gamma : ℝ) (hbeta : beta < 1)
    (hgamma : gamma < lambda / 2) :
    0 < directL2RightPowerExponent beta lambda (4 * beta - 2) gamma 1 :=
  directL2RightPowerExponent_boundary_pos_of_lt_half beta lambda gamma hbeta hgamma

example (beta lambda theta : ℝ)
    (hbetaHalf : 1 / 2 < beta) (hbetaOne : beta < 1)
    (hlambda : 0 < lambda) (hfeasible : theta < 4 * beta - 2) :
    ∃ gammaLeft gammaRight etaLeft etaRight : ℝ,
      gammaLeft = directL2LeftHeight ∧
      gammaRight = directL2RightHeightWitness beta lambda theta ∧
      etaLeft = directL2LeftPowerMargin beta theta ∧
      etaRight = directL2RightPowerMargin beta lambda theta ∧
      0 < gammaLeft ∧ 0 < gammaRight ∧ gammaRight < lambda / 2 ∧
      0 < etaLeft ∧ 0 < etaRight ∧
      (∀ sigma : ℝ, 1 / 2 ≤ sigma → sigma ≤ beta →
        directL2LeftPowerExponent beta theta gammaLeft sigma ≤ -etaLeft) ∧
      (∀ sigma : ℝ, beta ≤ sigma → sigma ≤ 1 →
        directL2RightPowerExponent beta lambda theta gammaRight sigma ≤ -etaRight) :=
  exists_directL2_twoSidedParameters beta lambda theta
    hbetaHalf hbetaOne hlambda hfeasible

example (beta lambda theta gamma width sigma : ℝ) :
    directL2RightStripPowerExponent beta lambda theta gamma width sigma =
      2 * lambda * (sigma + width - beta) +
        gamma * (carlsonTwoHeightDensityExponent sigma - 2 + theta) := rfl

example (beta theta gamma width sigma : ℝ) :
    directL2LeftStripPowerExponent beta theta gamma width sigma =
      2 * (sigma + width - beta) +
        gamma * (carlsonTwoHeightDensityExponent sigma - 2 + theta) := rfl

example (beta theta gamma sigma : ℝ) :
    directL2CoarsePowerExponent beta theta gamma sigma =
      2 * (sigma - beta) + gamma * (theta - 1) := rfl

example : directL2HundredthWidth = (1 / 100 : ℝ) := rfl
example : directL2UniformPowerMargin = (1 / 20 : ℝ) := rfl

example (beta lambda : ℝ) :
    directL2PolylogBaseHeight beta lambda = lambda * (1 - beta) := rfl

example (beta lambda : ℝ) :
    directL2PolylogRightHeight beta lambda =
      (directL2PolylogBaseHeight beta lambda + lambda / 2) / 2 := rfl

example (beta lambda : ℝ) :
    directL2PolylogOuterHeight beta lambda =
      (1 + directL2PolylogBaseHeight beta lambda) / 2 := rfl

example (beta lambda : ℝ) :
    directL2PolylogSmoothingExponent beta lambda =
      (1 - directL2PolylogBaseHeight beta lambda) / 8 := rfl

example (beta lambda theta gamma width sigma : ℝ) :
    directL2RightStripPowerExponent beta lambda theta gamma width sigma =
      directL2RightPowerExponent beta lambda theta gamma sigma +
        2 * lambda * width :=
  directL2RightStripPowerExponent_eq beta lambda theta gamma width sigma

example (beta theta gamma width sigma : ℝ) :
    directL2LeftStripPowerExponent beta theta gamma width sigma =
      directL2LeftPowerExponent beta theta gamma sigma + 2 * width :=
  directL2LeftStripPowerExponent_eq beta theta gamma width sigma

example (beta lambda : ℝ) :
    directL2CriticalRightHeight beta lambda 0 =
      directL2PolylogBaseHeight beta lambda :=
  directL2CriticalRightHeight_zero beta lambda

example (beta lambda : ℝ) :
    directL2PolylogRightHeight beta lambda =
      directL2RightHeightWitness beta lambda 0 :=
  directL2PolylogRightHeight_eq_witness beta lambda

example (beta lambda : ℝ) (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1) (hlambdaPos : 0 < lambda)
    (hlambdaTwo : lambda < 2) :
    0 < directL2PolylogBaseHeight beta lambda ∧
      directL2PolylogBaseHeight beta lambda < directL2PolylogRightHeight beta lambda ∧
      directL2PolylogRightHeight beta lambda < lambda / 2 ∧
      directL2PolylogRightHeight beta lambda < directL2PolylogOuterHeight beta lambda ∧
      directL2PolylogOuterHeight beta lambda < 1 ∧
      0 < directL2PolylogSmoothingExponent beta lambda ∧
      directL2PolylogSmoothingExponent beta lambda <
        directL2PolylogOuterHeight beta lambda :=
  directL2Polylog_parameter_order beta lambda
    hbetaHalf hbetaOne hlambdaPos hlambdaTwo

example (beta lambda : ℝ) :
    directL2PolylogOuterHeight beta lambda - directL2PolylogRightHeight beta lambda =
      (2 - lambda) / 4 :=
  directL2Polylog_outer_sub_right beta lambda

example (beta lambda : ℝ) :
    directL2RightPowerExponent beta lambda 0
        (directL2PolylogRightHeight beta lambda) 1 =
      -lambda * (beta - 1 / 2) :=
  directL2Polylog_right_endpoint beta lambda

example (beta lambda : ℝ) (hbeta : 2 / 3 < beta) (hlambda : 1 ≤ lambda) :
    1 / 6 < lambda * (beta - 1 / 2) :=
  one_sixth_lt_directL2Polylog_rightMargin beta lambda hbeta hlambda

example (beta : ℝ) (hbeta : 2 / 3 < beta) :
    5 / 36 < directL2LeftPowerMargin beta 0 :=
  five_thirtySixths_lt_directL2Polylog_leftMargin beta hbeta

example (beta lambda sigma : ℝ) (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) (hlambdaOne : 1 ≤ lambda)
    (hlambdaTwo : lambda < 2) (hbetaSigma : beta ≤ sigma)
    (hsigmaOne : sigma ≤ 1) :
    directL2RightStripPowerExponent beta lambda 0
        (directL2PolylogRightHeight beta lambda) directL2HundredthWidth sigma ≤
      -directL2UniformPowerMargin :=
  directL2Polylog_rightHundredthStrip_le beta lambda sigma
    hbeta hbetaOne hlambdaOne hlambdaTwo hbetaSigma hsigmaOne

example (beta sigma : ℝ) (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaBeta : sigma ≤ beta) :
    directL2LeftStripPowerExponent beta 0 directL2LeftHeight
        directL2HundredthWidth sigma ≤ -directL2UniformPowerMargin :=
  directL2Polylog_leftHundredthStrip_le beta sigma
    hbeta hbetaOne hsigmaHalf hsigmaBeta

example (beta : ℝ) (hbeta : 2 / 3 < beta) :
    directL2CoarsePowerExponent beta 0 directL2LeftHeight (13 / 25) < -(2 / 5) :=
  directL2Polylog_coarseThirteenTwentyFifths_lt beta hbeta

example (beta lambda : ℝ) :
    lambda * (1 - beta) + 2 * directL2PolylogSmoothingExponent beta lambda -
        2 * directL2PolylogOuterHeight beta lambda =
      -(3 + directL2PolylogBaseHeight beta lambda) / 4 :=
  directL2Polylog_centeredContourExponent beta lambda

example (beta lambda : ℝ) (hbeta : beta < 1) (hlambda : 0 < lambda) :
    lambda * (1 - beta) + 2 * directL2PolylogSmoothingExponent beta lambda -
        2 * directL2PolylogOuterHeight beta lambda < 0 :=
  directL2Polylog_centeredContourExponent_neg beta lambda hbeta hlambda

end PrimeNumberTheorem
