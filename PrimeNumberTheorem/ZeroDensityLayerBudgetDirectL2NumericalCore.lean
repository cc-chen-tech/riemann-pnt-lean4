import PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightNumericalCore

/-!
# Direct-L2 Carlson numerical core

This file isolates the exact polynomial exponents needed when a dyadic Carlson
square-capacity estimate is multiplied by an Occupancy estimate.  In
particular, it proves that the strict condition `theta < 4 * beta - 2` is both
necessary and sufficient for a right-hand cutoff below `lambda / 2`.

The exponents in this file are independent of the existing L1 two-height cuts.
They must not be used to rename or reinterpret `gammaLow` or `gammaHigh`.
-/

namespace PrimeNumberTheorem

/-- Polynomial exponent for right-anchored direct-L2 Carlson blocks. -/
def directL2RightPowerExponent
    (beta lambda theta gamma sigma : ℝ) : ℝ :=
  2 * lambda * (sigma - beta) +
    gamma * (carlsonTwoHeightDensityExponent sigma - 2 + theta)

/-- Polynomial exponent for left-anchored direct-L2 Carlson blocks. -/
def directL2LeftPowerExponent
    (beta theta gamma sigma : ℝ) : ℝ :=
  2 * (sigma - beta) +
    gamma * (carlsonTwoHeightDensityExponent sigma - 2 + theta)

/-- Critical right height at which the endpoint exponent is zero. -/
def directL2CriticalRightHeight
    (beta lambda theta : ℝ) : ℝ :=
  2 * lambda * (1 - beta) / (2 - theta)

/-- Strict direct-L2 feasibility gap. -/
def directL2FeasibilityGap (beta theta : ℝ) : ℝ :=
  4 * beta - 2 - theta

/-- Midpoint witness between the critical height and `lambda / 2`. -/
def directL2RightHeightWitness
    (beta lambda theta : ℝ) : ℝ :=
  (directL2CriticalRightHeight beta lambda theta + lambda / 2) / 2

/-- Exact right-endpoint margin supplied by the midpoint witness. -/
def directL2RightPowerMargin
    (beta lambda theta : ℝ) : ℝ :=
  lambda * directL2FeasibilityGap beta theta / 4

/-- Fixed left cutoff used by the first direct-L2 specialization. -/
def directL2LeftHeight : ℝ :=
  1 / 8

/-- Uniform left-side margin for the fixed cutoff `1 / 8`. -/
def directL2LeftPowerMargin (beta theta : ℝ) : ℝ :=
  (4 * (1 - beta) ^ 2 + directL2FeasibilityGap beta theta) / 8

/-- Exact comparison of a right-strip exponent with its endpoint value. -/
theorem directL2RightPowerExponent_one_sub
    (beta lambda theta gamma sigma : ℝ) :
    directL2RightPowerExponent beta lambda theta gamma 1 -
        directL2RightPowerExponent beta lambda theta gamma sigma =
      2 * (1 - sigma) * (lambda - 2 * gamma * sigma) := by
  simp [directL2RightPowerExponent, carlsonTwoHeightDensityExponent]
  ring

/-- The endpoint exponent factors through the critical-height gap. -/
theorem directL2RightPowerExponent_one_eq_criticalGap
    (beta lambda theta gamma : ℝ)
    (htheta : theta ≠ 2) :
    directL2RightPowerExponent beta lambda theta gamma 1 =
      (2 - theta) *
        (directL2CriticalRightHeight beta lambda theta - gamma) := by
  have hden : 2 - theta ≠ 0 := sub_ne_zero.mpr htheta.symm
  simp [directL2RightPowerExponent, carlsonTwoHeightDensityExponent,
    directL2CriticalRightHeight]
  field_simp [hden]
  ring

/-- A critical right height lies below `lambda / 2` exactly in the strict
direct-L2 feasibility range. -/
theorem directL2CriticalRightHeight_lt_half_iff
    (beta lambda theta : ℝ)
    (hlambda : 0 < lambda)
    (htheta : theta < 2) :
    directL2CriticalRightHeight beta lambda theta < lambda / 2 ↔
      theta < 4 * beta - 2 := by
  have hden : 0 < 2 - theta := sub_pos.mpr htheta
  constructor
  · intro h
    have hmul := (div_lt_iff₀ hden).mp h
    have hscaled :
        lambda * (4 * (1 - beta)) < lambda * (2 - theta) := by
      nlinarith
    have hcancel : 4 * (1 - beta) < 2 - theta :=
      (mul_lt_mul_left hlambda).mp hscaled
    nlinarith
  · intro h
    have hbase : 4 * (1 - beta) < 2 - theta := by
      nlinarith
    have hscaled :
        lambda * (4 * (1 - beta)) < lambda * (2 - theta) :=
      (mul_lt_mul_left hlambda).mpr hbase
    apply (div_lt_iff₀ hden).mpr
    nlinarith

/-- The strict feasibility gap forces `theta < 2` when `beta < 1`. -/
theorem directL2_theta_lt_two_of_feasible
    (beta theta : ℝ)
    (hbeta : beta < 1)
    (hfeasible : theta < 4 * beta - 2) :
    theta < 2 := by
  nlinarith

/-- The midpoint witness is positive. -/
theorem directL2RightHeightWitness_pos
    (beta lambda theta : ℝ)
    (hbeta : beta < 1)
    (hlambda : 0 < lambda)
    (hfeasible : theta < 4 * beta - 2) :
    0 < directL2RightHeightWitness beta lambda theta := by
  have htheta : theta < 2 :=
    directL2_theta_lt_two_of_feasible beta theta hbeta hfeasible
  have hcritical :
      0 < directL2CriticalRightHeight beta lambda theta := by
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hlambda) (sub_pos.mpr hbeta))
      (sub_pos.mpr htheta)
  simp only [directL2RightHeightWitness]
  nlinarith

/-- The midpoint witness remains strictly below `lambda / 2`. -/
theorem directL2RightHeightWitness_lt_half
    (beta lambda theta : ℝ)
    (hbeta : beta < 1)
    (hlambda : 0 < lambda)
    (hfeasible : theta < 4 * beta - 2) :
    directL2RightHeightWitness beta lambda theta < lambda / 2 := by
  have htheta : theta < 2 :=
    directL2_theta_lt_two_of_feasible beta theta hbeta hfeasible
  have hcritical :
      directL2CriticalRightHeight beta lambda theta < lambda / 2 :=
    (directL2CriticalRightHeight_lt_half_iff beta lambda theta hlambda htheta).2
      hfeasible
  simp only [directL2RightHeightWitness]
  nlinarith

/-- The right power margin is strictly positive in the feasible range. -/
theorem directL2RightPowerMargin_pos
    (beta lambda theta : ℝ)
    (hlambda : 0 < lambda)
    (hfeasible : theta < 4 * beta - 2) :
    0 < directL2RightPowerMargin beta lambda theta := by
  dsimp [directL2RightPowerMargin, directL2FeasibilityGap]
  positivity

/-- The midpoint witness gives the exact negative endpoint margin. -/
theorem directL2RightPowerExponent_witness_one
    (beta lambda theta : ℝ)
    (hbeta : beta < 1)
    (hfeasible : theta < 4 * beta - 2) :
    directL2RightPowerExponent beta lambda theta
        (directL2RightHeightWitness beta lambda theta) 1 =
      -directL2RightPowerMargin beta lambda theta := by
  have htheta : theta < 2 :=
    directL2_theta_lt_two_of_feasible beta theta hbeta hfeasible
  rw [directL2RightPowerExponent_one_eq_criticalGap]
  · simp [directL2RightHeightWitness, directL2RightPowerMargin,
      directL2FeasibilityGap, directL2CriticalRightHeight]
    field_simp [ne_of_gt (sub_pos.mpr htheta)]
    ring
  · exact ne_of_lt htheta

/-- Every right-strip exponent is bounded by the same strict midpoint margin. -/
theorem directL2RightPowerExponent_witness_le_neg_margin
    (beta lambda theta sigma : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hlambda : 0 < lambda)
    (hfeasible : theta < 4 * beta - 2)
    (hbetaSigma : beta ≤ sigma)
    (hsigmaOne : sigma ≤ 1) :
    directL2RightPowerExponent beta lambda theta
        (directL2RightHeightWitness beta lambda theta) sigma ≤
      -directL2RightPowerMargin beta lambda theta := by
  have hgammaPos :
      0 < directL2RightHeightWitness beta lambda theta :=
    directL2RightHeightWitness_pos beta lambda theta hbetaOne hlambda hfeasible
  have hgammaHalf :
      directL2RightHeightWitness beta lambda theta < lambda / 2 :=
    directL2RightHeightWitness_lt_half beta lambda theta hbetaOne hlambda hfeasible
  have hgammaSigma :
      directL2RightHeightWitness beta lambda theta * sigma ≤
        directL2RightHeightWitness beta lambda theta := by
    calc
      directL2RightHeightWitness beta lambda theta * sigma ≤
          directL2RightHeightWitness beta lambda theta * 1 :=
        mul_le_mul_of_nonneg_left hsigmaOne (le_of_lt hgammaPos)
      _ = directL2RightHeightWitness beta lambda theta := by ring
  have hfactor :
      0 ≤ 2 * (1 - sigma) *
        (lambda - 2 * directL2RightHeightWitness beta lambda theta * sigma) := by
    have hfirst : 0 ≤ 2 * (1 - sigma) := by nlinarith
    have hsecond :
        0 < lambda -
          2 * directL2RightHeightWitness beta lambda theta * sigma := by
      nlinarith
    exact mul_nonneg hfirst (le_of_lt hsecond)
  have hdiff := directL2RightPowerExponent_one_sub beta lambda theta
    (directL2RightHeightWitness beta lambda theta) sigma
  have hone := directL2RightPowerExponent_witness_one beta lambda theta
    hbetaOne hfeasible
  nlinarith

/-- Exact monotonicity identity for the left-anchored exponent. -/
theorem directL2LeftPowerExponent_beta_sub
    (beta theta gamma sigma : ℝ) :
    directL2LeftPowerExponent beta theta gamma beta -
        directL2LeftPowerExponent beta theta gamma sigma =
      2 * (beta - sigma) *
        (1 + 2 * gamma * (1 - beta - sigma)) := by
  simp [directL2LeftPowerExponent, carlsonTwoHeightDensityExponent]
  ring

/-- The fixed left witness gives the exact endpoint margin. -/
theorem directL2LeftPowerExponent_fixed_beta
    (beta theta : ℝ) :
    directL2LeftPowerExponent beta theta directL2LeftHeight beta =
      -directL2LeftPowerMargin beta theta := by
  simp [directL2LeftPowerExponent, carlsonTwoHeightDensityExponent,
    directL2LeftHeight, directL2LeftPowerMargin, directL2FeasibilityGap]
  ring

/-- The fixed left power margin is positive in the feasible range. -/
theorem directL2LeftPowerMargin_pos
    (beta theta : ℝ)
    (hfeasible : theta < 4 * beta - 2) :
    0 < directL2LeftPowerMargin beta theta := by
  have hsquare : 0 ≤ (1 - beta) ^ 2 := sq_nonneg (1 - beta)
  dsimp [directL2LeftPowerMargin, directL2FeasibilityGap]
  nlinarith

/-- Every left strip is bounded by the fixed strict left margin. -/
theorem directL2LeftPowerExponent_fixed_le_neg_margin
    (beta theta sigma : ℝ)
    (hbetaOne : beta < 1)
    (hfeasible : theta < 4 * beta - 2)
    (hsigmaHalf : 1 / 2 ≤ sigma)
    (hsigmaBeta : sigma ≤ beta) :
    directL2LeftPowerExponent beta theta directL2LeftHeight sigma ≤
      -directL2LeftPowerMargin beta theta := by
  have hfactorPos :
      0 < 1 + 2 * directL2LeftHeight * (1 - beta - sigma) := by
    dsimp [directL2LeftHeight]
    nlinarith
  have hproduct :
      0 ≤ 2 * (beta - sigma) *
        (1 + 2 * directL2LeftHeight * (1 - beta - sigma)) :=
    mul_nonneg (by nlinarith) (le_of_lt hfactorPos)
  have hdiff := directL2LeftPowerExponent_beta_sub beta theta
    directL2LeftHeight sigma
  have hbeta := directL2LeftPowerExponent_fixed_beta beta theta
  nlinarith

/-- A negative right endpoint below `lambda / 2` forces the strict feasibility
condition. -/
theorem directL2_theta_lt_four_beta_sub_two_of_right_endpoint_neg
    (beta lambda theta gamma : ℝ)
    (hbeta : beta < 1)
    (hlambda : 0 < lambda)
    (hgammaNonneg : 0 ≤ gamma)
    (hgammaHalf : gamma < lambda / 2)
    (hnegative : directL2RightPowerExponent beta lambda theta gamma 1 < 0) :
    theta < 4 * beta - 2 := by
  have hformula :
      directL2RightPowerExponent beta lambda theta gamma 1 =
        2 * lambda * (1 - beta) + gamma * (theta - 2) := by
    simp [directL2RightPowerExponent, carlsonTwoHeightDensityExponent]
    ring
  by_contra hnot
  have hthetaLower : 4 * beta - 2 ≤ theta := le_of_not_gt hnot
  by_cases hthetaTwo : theta < 2
  · have hthetaGap : 0 < 2 - theta := sub_pos.mpr hthetaTwo
    have hmulStrict :
        gamma * (2 - theta) < (lambda / 2) * (2 - theta) :=
      mul_lt_mul_of_pos_right hgammaHalf hthetaGap
    have hbase : 2 - theta ≤ 4 * (1 - beta) := by
      nlinarith
    have hlambdaHalf : 0 ≤ lambda / 2 := by positivity
    have hmulWeak :
        (lambda / 2) * (2 - theta) ≤
          (lambda / 2) * (4 * (1 - beta)) :=
      mul_le_mul_of_nonneg_left hbase hlambdaHalf
    rw [hformula] at hnegative
    nlinarith
  · have hthetaTwo' : 2 ≤ theta := le_of_not_gt hthetaTwo
    have hbasePos : 0 < 2 * lambda * (1 - beta) := by positivity
    have htailNonneg : 0 ≤ gamma * (theta - 2) :=
      mul_nonneg hgammaNonneg (sub_nonneg.mpr hthetaTwo')
    rw [hformula] at hnegative
    nlinarith

/-- Exact necessary-and-sufficient right-height criterion. -/
theorem exists_directL2_rightHeight_iff
    (beta lambda theta : ℝ)
    (hbeta : beta < 1)
    (hlambda : 0 < lambda) :
    (∃ gamma : ℝ,
      0 ≤ gamma ∧ gamma < lambda / 2 ∧
        directL2RightPowerExponent beta lambda theta gamma 1 < 0) ↔
      theta < 4 * beta - 2 := by
  constructor
  · rintro ⟨gamma, hgammaNonneg, hgammaHalf, hnegative⟩
    exact directL2_theta_lt_four_beta_sub_two_of_right_endpoint_neg
      beta lambda theta gamma hbeta hlambda hgammaNonneg hgammaHalf hnegative
  · intro hfeasible
    refine ⟨directL2RightHeightWitness beta lambda theta,
      le_of_lt (directL2RightHeightWitness_pos beta lambda theta
        hbeta hlambda hfeasible),
      directL2RightHeightWitness_lt_half beta lambda theta
        hbeta hlambda hfeasible, ?_⟩
    rw [directL2RightPowerExponent_witness_one beta lambda theta hbeta hfeasible]
    exact neg_neg_of_pos
      (directL2RightPowerMargin_pos beta lambda theta hlambda hfeasible)

/-- At the boundary, the critical height is exactly `lambda / 2`. -/
theorem directL2CriticalRightHeight_boundary
    (beta lambda : ℝ)
    (hbeta : beta < 1) :
    directL2CriticalRightHeight beta lambda (4 * beta - 2) = lambda / 2 := by
  have hne : 1 - beta ≠ 0 := ne_of_gt (sub_pos.mpr hbeta)
  simp [directL2CriticalRightHeight]
  field_simp [hne]
  ring

/-- The polynomial exponent is exactly zero at the critical boundary. -/
theorem directL2RightPowerExponent_boundary_half
    (beta lambda : ℝ) :
    directL2RightPowerExponent beta lambda (4 * beta - 2) (lambda / 2) 1 = 0 := by
  simp [directL2RightPowerExponent, carlsonTwoHeightDensityExponent]
  ring

/-- Below `lambda / 2`, the boundary endpoint exponent is strictly positive. -/
theorem directL2RightPowerExponent_boundary_pos_of_lt_half
    (beta lambda gamma : ℝ)
    (hbeta : beta < 1)
    (hgamma : gamma < lambda / 2) :
    0 < directL2RightPowerExponent beta lambda (4 * beta - 2) gamma 1 := by
  have hidentity :
      directL2RightPowerExponent beta lambda (4 * beta - 2) gamma 1 =
        2 * (1 - beta) * (lambda - 2 * gamma) := by
    simp [directL2RightPowerExponent, carlsonTwoHeightDensityExponent]
    ring
  rw [hidentity]
  exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hbeta)) (by nlinarith)

/-- Combined two-sided direct-L2 parameter package with explicit witnesses and
strict uniform margins. -/
theorem exists_directL2_twoSidedParameters
    (beta lambda theta : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hlambda : 0 < lambda)
    (hfeasible : theta < 4 * beta - 2) :
    ∃ gammaLeft gammaRight etaLeft etaRight : ℝ,
      gammaLeft = directL2LeftHeight ∧
      gammaRight = directL2RightHeightWitness beta lambda theta ∧
      etaLeft = directL2LeftPowerMargin beta theta ∧
      etaRight = directL2RightPowerMargin beta lambda theta ∧
      0 < gammaLeft ∧
      0 < gammaRight ∧
      gammaRight < lambda / 2 ∧
      0 < etaLeft ∧
      0 < etaRight ∧
      (∀ sigma : ℝ, 1 / 2 ≤ sigma → sigma ≤ beta →
        directL2LeftPowerExponent beta theta gammaLeft sigma ≤ -etaLeft) ∧
      (∀ sigma : ℝ, beta ≤ sigma → sigma ≤ 1 →
        directL2RightPowerExponent beta lambda theta gammaRight sigma ≤ -etaRight) := by
  refine ⟨directL2LeftHeight,
    directL2RightHeightWitness beta lambda theta,
    directL2LeftPowerMargin beta theta,
    directL2RightPowerMargin beta lambda theta,
    rfl, rfl, rfl, rfl, ?_,
    directL2RightHeightWitness_pos beta lambda theta hbetaOne hlambda hfeasible,
    directL2RightHeightWitness_lt_half beta lambda theta hbetaOne hlambda hfeasible,
    directL2LeftPowerMargin_pos beta theta hfeasible,
    directL2RightPowerMargin_pos beta lambda theta hlambda hfeasible, ?_, ?_⟩
  · norm_num [directL2LeftHeight]
  · intro sigma hsigmaHalf hsigmaBeta
    exact directL2LeftPowerExponent_fixed_le_neg_margin beta theta sigma
      hbetaOne hfeasible hsigmaHalf hsigmaBeta
  · intro sigma hbetaSigma hsigmaOne
    exact directL2RightPowerExponent_witness_le_neg_margin
      beta lambda theta sigma hbetaHalf hbetaOne hlambda hfeasible
      hbetaSigma hsigmaOne

/-- Right-strip exponent when the amplitude is bounded at the strip's upper
endpoint but Carlson capacity is measured at its lower endpoint. -/
def directL2RightStripPowerExponent
    (beta lambda theta gamma width sigma : ℝ) : ℝ :=
  2 * lambda * (sigma + width - beta) +
    gamma * (carlsonTwoHeightDensityExponent sigma - 2 + theta)

/-- Left-strip analogue of `directL2RightStripPowerExponent`. -/
def directL2LeftStripPowerExponent
    (beta theta gamma width sigma : ℝ) : ℝ :=
  2 * (sigma + width - beta) +
    gamma * (carlsonTwoHeightDensityExponent sigma - 2 + theta)

/-- Coarse global-zero-count exponent after reciprocal-square weighting. -/
def directL2CoarsePowerExponent
    (beta theta gamma sigma : ℝ) : ℝ :=
  2 * (sigma - beta) + gamma * (theta - 1)

/-- Fixed real-strip width for the first actual-zeta specialization. -/
def directL2HundredthWidth : ℝ :=
  1 / 100

/-- Common safe power margin for the fixed-grid specialization. -/
def directL2UniformPowerMargin : ℝ :=
  1 / 20

/-- Natural right endpoint scale in the polylogarithmic Occupancy case. -/
def directL2PolylogBaseHeight (beta lambda : ℝ) : ℝ :=
  lambda * (1 - beta)

/-- Concrete right direct-L2 cutoff for polylogarithmic Occupancy. -/
def directL2PolylogRightHeight (beta lambda : ℝ) : ℝ :=
  (directL2PolylogBaseHeight beta lambda + lambda / 2) / 2

/-- Concrete outer contour exponent compatible with the direct-L2 cutoff. -/
def directL2PolylogOuterHeight (beta lambda : ℝ) : ℝ :=
  (1 + directL2PolylogBaseHeight beta lambda) / 2

/-- Concrete inverse smoothing-scale exponent for the centered cubic kernel. -/
def directL2PolylogSmoothingExponent (beta lambda : ℝ) : ℝ :=
  (1 - directL2PolylogBaseHeight beta lambda) / 8

/-- A strip exponent is its pointwise exponent plus exactly the upper-endpoint
width loss. -/
theorem directL2RightStripPowerExponent_eq
    (beta lambda theta gamma width sigma : ℝ) :
    directL2RightStripPowerExponent beta lambda theta gamma width sigma =
      directL2RightPowerExponent beta lambda theta gamma sigma +
        2 * lambda * width := by
  simp [directL2RightStripPowerExponent, directL2RightPowerExponent]
  ring

/-- Left-strip upper-endpoint loss. -/
theorem directL2LeftStripPowerExponent_eq
    (beta theta gamma width sigma : ℝ) :
    directL2LeftStripPowerExponent beta theta gamma width sigma =
      directL2LeftPowerExponent beta theta gamma sigma + 2 * width := by
  simp [directL2LeftStripPowerExponent, directL2LeftPowerExponent]
  ring

/-- At `theta = 0`, the abstract critical height is the natural base height
`lambda * (1 - beta)`. -/
theorem directL2CriticalRightHeight_zero
    (beta lambda : ℝ) :
    directL2CriticalRightHeight beta lambda 0 =
      directL2PolylogBaseHeight beta lambda := by
  simp [directL2CriticalRightHeight, directL2PolylogBaseHeight]
  ring

/-- The concrete polylogarithmic right cutoff is the generic midpoint witness. -/
theorem directL2PolylogRightHeight_eq_witness
    (beta lambda : ℝ) :
    directL2PolylogRightHeight beta lambda =
      directL2RightHeightWitness beta lambda 0 := by
  simp [directL2PolylogRightHeight, directL2RightHeightWitness,
    directL2CriticalRightHeight_zero]

/-- The concrete polylogarithmic parameters are strictly ordered. -/
theorem directL2Polylog_parameter_order
    (beta lambda : ℝ)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hlambdaPos : 0 < lambda)
    (hlambdaTwo : lambda < 2) :
    0 < directL2PolylogBaseHeight beta lambda ∧
      directL2PolylogBaseHeight beta lambda <
        directL2PolylogRightHeight beta lambda ∧
      directL2PolylogRightHeight beta lambda < lambda / 2 ∧
      directL2PolylogRightHeight beta lambda <
        directL2PolylogOuterHeight beta lambda ∧
      directL2PolylogOuterHeight beta lambda < 1 ∧
      0 < directL2PolylogSmoothingExponent beta lambda ∧
      directL2PolylogSmoothingExponent beta lambda <
        directL2PolylogOuterHeight beta lambda := by
  have hbasePos : 0 < directL2PolylogBaseHeight beta lambda := by
    exact mul_pos hlambdaPos (sub_pos.mpr hbetaOne)
  have hbaseHalf :
      directL2PolylogBaseHeight beta lambda < lambda / 2 := by
    dsimp [directL2PolylogBaseHeight]
    have hfactor : 1 - beta < 1 / 2 := by nlinarith
    exact (mul_lt_mul_left hlambdaPos).2 hfactor
  have hlambdaHalfOne : lambda / 2 < 1 := by nlinarith
  have hbaseOne : directL2PolylogBaseHeight beta lambda < 1 :=
    lt_trans hbaseHalf hlambdaHalfOne
  dsimp [directL2PolylogRightHeight, directL2PolylogOuterHeight,
    directL2PolylogSmoothingExponent]
  constructor
  · exact hbasePos
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Exact gap between the outer contour and direct-L2 right cutoff. -/
theorem directL2Polylog_outer_sub_right
    (beta lambda : ℝ) :
    directL2PolylogOuterHeight beta lambda -
        directL2PolylogRightHeight beta lambda =
      (2 - lambda) / 4 := by
  simp [directL2PolylogOuterHeight, directL2PolylogRightHeight,
    directL2PolylogBaseHeight]
  ring

/-- Exact right endpoint margin in the polylogarithmic case. -/
theorem directL2Polylog_right_endpoint
    (beta lambda : ℝ) :
    directL2RightPowerExponent beta lambda 0
        (directL2PolylogRightHeight beta lambda) 1 =
      -lambda * (beta - 1 / 2) := by
  simp [directL2RightPowerExponent, carlsonTwoHeightDensityExponent,
    directL2PolylogRightHeight, directL2PolylogBaseHeight]
  ring

/-- The unshifted right margin is uniformly greater than `1/6`. -/
theorem one_sixth_lt_directL2Polylog_rightMargin
    (beta lambda : ℝ)
    (hbeta : 2 / 3 < beta)
    (hlambda : 1 ≤ lambda) :
    1 / 6 < lambda * (beta - 1 / 2) := by
  have hfactor : 1 / 6 < beta - 1 / 2 := by nlinarith
  have hfactorNonneg : 0 ≤ beta - 1 / 2 := by nlinarith
  calc
    1 / 6 < 1 * (beta - 1 / 2) := by simpa using hfactor
    _ ≤ lambda * (beta - 1 / 2) :=
      mul_le_mul_of_nonneg_right hlambda hfactorNonneg

/-- The unshifted left margin is uniformly greater than `5/36`. -/
theorem five_thirtySixths_lt_directL2Polylog_leftMargin
    (beta : ℝ)
    (hbeta : 2 / 3 < beta) :
    5 / 36 < directL2LeftPowerMargin beta 0 := by
  have hfirst : 0 < 3 * beta - 2 := by nlinarith
  have hsecond : 0 < 6 * beta - 2 := by nlinarith
  have hproduct : 0 < (3 * beta - 2) * (6 * beta - 2) :=
    mul_pos hfirst hsecond
  have hidentity :
      directL2LeftPowerMargin beta 0 - 5 / 36 =
        ((3 * beta - 2) * (6 * beta - 2)) / 36 := by
    simp [directL2LeftPowerMargin, directL2FeasibilityGap]
    ring
  rw [hidentity]
  positivity

/-- Every fixed hundredth right strip has the common power margin `1/20`. -/
theorem directL2Polylog_rightHundredthStrip_le
    (beta lambda sigma : ℝ)
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hlambdaOne : 1 ≤ lambda)
    (hlambdaTwo : lambda < 2)
    (hbetaSigma : beta ≤ sigma)
    (hsigmaOne : sigma ≤ 1) :
    directL2RightStripPowerExponent beta lambda 0
        (directL2PolylogRightHeight beta lambda)
        directL2HundredthWidth sigma ≤
      -directL2UniformPowerMargin := by
  have hbetaHalf : 1 / 2 < beta := by nlinarith
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambdaOne
  have hfeasible : (0 : ℝ) < 4 * beta - 2 := by nlinarith
  have hbase := directL2RightPowerExponent_witness_le_neg_margin
    beta lambda 0 sigma hbetaHalf hbetaOne hlambdaPos hfeasible
    hbetaSigma hsigmaOne
  have hwitness := directL2PolylogRightHeight_eq_witness beta lambda
  have hmargin :
      directL2RightPowerMargin beta lambda 0 =
        lambda * (beta - 1 / 2) := by
    simp [directL2RightPowerMargin, directL2FeasibilityGap]
    ring
  have hlower := one_sixth_lt_directL2Polylog_rightMargin
    beta lambda hbeta hlambdaOne
  have hwidth :
      2 * lambda * directL2HundredthWidth < 1 / 25 := by
    dsimp [directL2HundredthWidth]
    nlinarith
  rw [← hwitness] at hbase
  rw [directL2RightStripPowerExponent_eq, hmargin]
  dsimp [directL2UniformPowerMargin]
  nlinarith

/-- Every fixed hundredth left strip has the common power margin `1/20`. -/
theorem directL2Polylog_leftHundredthStrip_le
    (beta sigma : ℝ)
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 ≤ sigma)
    (hsigmaBeta : sigma ≤ beta) :
    directL2LeftStripPowerExponent beta 0 directL2LeftHeight
        directL2HundredthWidth sigma ≤
      -directL2UniformPowerMargin := by
  have hfeasible : (0 : ℝ) < 4 * beta - 2 := by nlinarith
  have hbase := directL2LeftPowerExponent_fixed_le_neg_margin
    beta 0 sigma hbetaOne hfeasible hsigmaHalf hsigmaBeta
  have hlower := five_thirtySixths_lt_directL2Polylog_leftMargin beta hbeta
  rw [directL2LeftStripPowerExponent_eq]
  dsimp [directL2HundredthWidth, directL2UniformPowerMargin]
  nlinarith

/-- The coarse layer at real part `13/25` has a much larger negative margin. -/
theorem directL2Polylog_coarseThirteenTwentyFifths_lt
    (beta : ℝ)
    (hbeta : 2 / 3 < beta) :
    directL2CoarsePowerExponent beta 0 directL2LeftHeight (13 / 25) <
      -(2 / 5) := by
  dsimp [directL2CoarsePowerExponent, directL2LeftHeight]
  nlinarith

/-- Exact centered-cubic contour exponent for the concrete parameter choice. -/
theorem directL2Polylog_centeredContourExponent
    (beta lambda : ℝ) :
    lambda * (1 - beta) +
        2 * directL2PolylogSmoothingExponent beta lambda -
        2 * directL2PolylogOuterHeight beta lambda =
      -(3 + directL2PolylogBaseHeight beta lambda) / 4 := by
  simp [directL2PolylogSmoothingExponent, directL2PolylogOuterHeight,
    directL2PolylogBaseHeight]
  ring

/-- The centered-cubic contour exponent is strictly negative. -/
theorem directL2Polylog_centeredContourExponent_neg
    (beta lambda : ℝ)
    (hbeta : beta < 1)
    (hlambda : 0 < lambda) :
    lambda * (1 - beta) +
        2 * directL2PolylogSmoothingExponent beta lambda -
        2 * directL2PolylogOuterHeight beta lambda < 0 := by
  rw [directL2Polylog_centeredContourExponent]
  have hbase : 0 < directL2PolylogBaseHeight beta lambda :=
    mul_pos hlambda (sub_pos.mpr hbeta)
  nlinarith

end PrimeNumberTheorem
