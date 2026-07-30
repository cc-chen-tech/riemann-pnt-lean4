import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightOptimalPrescribedCapOuterExponent

/-!
# Strict improvement from an interior density threshold

When the prescribed real-part cap lies strictly to the right of `1 / 2`,
choosing the density threshold strictly between these two endpoints improves
both active outer-height constraints over the cap-aligned baseline.
-/

namespace PrimeNumberTheorem

/-- The explicit density threshold halfway between `1 / 2` and the prescribed
real-part cap. -/
noncomputable def jointTwoHeightMidpointDensityThreshold
    (theta : ℝ) : ℝ :=
  ((1 / 2 : ℝ) + theta) / 2

theorem jointTwoHeightMidpointDensityThreshold_spec
    {theta : ℝ} (hthetaHalf : 1 / 2 < theta) :
    1 / 2 < jointTwoHeightMidpointDensityThreshold theta ∧
      jointTwoHeightMidpointDensityThreshold theta < theta := by
  unfold jointTwoHeightMidpointDensityThreshold
  constructor <;> linarith

/-- At the midpoint density threshold, the optimized prescribed-cap ceiling
strictly exceeds the cap-aligned exponent `2 * (beta - theta)`.  The gain is
simultaneous: the low layer improves because `sigma < theta`, while the
Carlson constraint improves because its balanced slope is strictly below
`1 / 2` away from the endpoint. -/
theorem
    jointTwoHeightPrescribedCapOuterExponentCeiling_midpoint_gt_capAligned
    {beta theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1) :
    2 * (beta - theta) <
      jointTwoHeightPrescribedCapOuterExponentCeiling
        beta (jointTwoHeightMidpointDensityThreshold theta) theta := by
  let sigma := jointTwoHeightMidpointDensityThreshold theta
  rcases jointTwoHeightMidpointDensityThreshold_spec hthetaHalf with
    ⟨hsigmaHalf, hsigmaTheta⟩
  have hsigmaOne : sigma < 1 := by
    exact hsigmaTheta.trans (hthetaBeta.trans hbetaOne)
  have hslopePos :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigmaHalf hsigmaOne
  have hslopeHalf :
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma < 1 / 2 :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half
      hsigmaHalf hsigmaOne
  have hdiffPos : 0 < beta - theta := sub_pos.mpr hthetaBeta
  have hbaselineOne : 2 * (beta - theta) < 1 := by
    linarith
  have hlow :
      2 * (beta - theta) < 2 * (beta - sigma) := by
    linarith
  have hhigh :
      2 * (beta - theta) <
        (beta - max sigma theta) /
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma := by
    rw [max_eq_right hsigmaTheta.le]
    rw [lt_div_iff₀ hslopePos]
    have hgain :
        0 <
          (beta - theta) *
            (1 / 2 -
              targetAmplitudeCarlsonTwoHeightBalancedSlope sigma) :=
      mul_pos hdiffPos (sub_pos.mpr hslopeHalf)
    nlinarith
  change
    2 * (beta - theta) <
      jointTwoHeightPrescribedCapOuterExponentCeiling
        beta sigma theta
  unfold jointTwoHeightPrescribedCapOuterExponentCeiling
  exact lt_min hbaselineOne (lt_min hlow hhigh)

/-- Under the canonical cap condition, the midpoint threshold produces an
outer exponent strictly larger than the cap-aligned baseline and still above
the contour floor.  The returned endpoint and feasibility predicate are the
complete numerical input expected by the strict-margin constructor. -/
theorem exists_jointTwoHeightStrictlyImprovedMidpointSigmaParameters
    {beta theta : ℝ}
    (hbetaOne : beta < 1)
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hthetaCanonical : theta < (3 * beta - 1) / 2) :
    ∃ sigma tau alpha : ℝ,
      sigma = jointTwoHeightMidpointDensityThreshold theta ∧
      1 / 2 < sigma ∧
      sigma < theta ∧
      sigma < tau ∧
      theta < tau ∧
      tau < beta ∧
      2 * (beta - theta) < alpha ∧
      alpha <
        jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      IsJointTwoHeightOuterExponentFeasible
        beta sigma tau alpha := by
  let sigma := jointTwoHeightMidpointDensityThreshold theta
  rcases jointTwoHeightMidpointDensityThreshold_spec hthetaHalf with
    ⟨hsigmaHalf, hsigmaTheta⟩
  have hsigmaOne : sigma < 1 := by
    exact hsigmaTheta.trans (hthetaBeta.trans hbetaOne)
  have hceiling :
      2 * (beta - theta) <
        jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta := by
    simpa [sigma] using
      jointTwoHeightPrescribedCapOuterExponentCeiling_midpoint_gt_capAligned
        hthetaHalf hthetaBeta hbetaOne
  let alpha :=
    (2 * (beta - theta) +
      jointTwoHeightPrescribedCapOuterExponentCeiling
        beta sigma theta) / 2
  have hbaselineAlpha : 2 * (beta - theta) < alpha := by
    dsimp [alpha]
    linarith
  have halphaCeiling :
      alpha <
        jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta := by
    dsimp [alpha]
    linarith
  have hcontourBaseline : 1 - beta < 2 * (beta - theta) := by
    linarith
  have hcontour : 1 - beta < alpha :=
    hcontourBaseline.trans hbaselineAlpha
  have halphaPos : 0 < alpha := by
    have hbetaPos : 0 < beta := by
      linarith
    have : 0 < 1 - beta := sub_pos.mpr hbetaOne
    linarith
  rcases
      jointTwoHeightPrescribedCapOuterExponentFeasible_of_lt_ceiling
        hbetaOne hsigmaHalf hsigmaOne hcontour halphaCeiling with
    ⟨tau, hsigmaTau, hthetaTau, htauBeta, halphaFeasible⟩
  exact
    ⟨sigma, tau, alpha, rfl, hsigmaHalf, hsigmaTheta,
      hsigmaTau, hthetaTau, htauBeta, hbaselineAlpha,
      halphaCeiling, hcontour, halphaPos, halphaFeasible⟩

end PrimeNumberTheorem
