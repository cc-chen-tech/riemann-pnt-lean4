import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightGlobalOptimalTruncationParameters

/-!
# Improved global real-part cap threshold

Optimizing the density threshold enlarges the range of prescribed real-part
caps for which a contour-compatible common outer height exists.  The exact
new cap threshold is characterized through the strictly decreasing balance
map.
-/

namespace PrimeNumberTheorem

/-- Balance value whose level set defines the optimal density threshold. -/
noncomputable def jointTwoHeightSigmaBalanceValue
    (beta sigma : ℝ) : ℝ :=
  2 *
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
    (beta - sigma)

/-- The balance value strictly decreases while the density threshold moves
from `1 / 2` toward `beta < 1`. -/
theorem jointTwoHeightSigmaBalanceValue_strictAnti
    {beta sigma₁ sigma₂ : ℝ}
    (hsigma₁Half : 1 / 2 < sigma₁)
    (hsigma₁Sigma₂ : sigma₁ < sigma₂)
    (hsigma₂Beta : sigma₂ < beta)
    (hbetaOne : beta < 1) :
    jointTwoHeightSigmaBalanceValue beta sigma₂ <
      jointTwoHeightSigmaBalanceValue beta sigma₁ := by
  have hsigma₂One : sigma₂ < 1 :=
    hsigma₂Beta.trans hbetaOne
  have hslope :
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ <
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_strictAntiOn_half_one
      hsigma₁Half hsigma₁Sigma₂ hsigma₂One
  have hbetaSigma₂ : 0 < beta - sigma₂ :=
    sub_pos.mpr hsigma₂Beta
  have hbetaSigma :
      beta - sigma₂ < beta - sigma₁ := by
    linarith
  have hslope₁Pos :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigma₁Half
      (hsigma₁Sigma₂.trans hsigma₂One)
  have hproduct :
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ *
          (beta - sigma₂) <
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ *
          (beta - sigma₁) :=
    (mul_lt_mul_of_pos_right hslope hbetaSigma₂).trans
      (mul_lt_mul_of_pos_left hbetaSigma hslope₁Pos)
  unfold jointTwoHeightSigmaBalanceValue
  linarith

/-- Largest prescribed real-part cap allowed by the globally optimized
two-height contour inequalities. -/
noncomputable def jointTwoHeightImprovedGlobalCapThreshold
    (beta : ℝ) : ℝ :=
  beta -
    jointTwoHeightSigmaBalanceValue beta
      (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta)

/-- The globally optimized cap threshold strictly improves the old canonical
threshold while remaining strictly below `beta`. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_spec
    {beta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta <
        jointTwoHeightImprovedGlobalCapThreshold beta ∧
      jointTwoHeightImprovedGlobalCapThreshold beta < beta := by
  let c := targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta
  rcases
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
        hbeta hbetaOne with
    ⟨hcHalf, hcBeta, hcOne⟩
  have hslopePos :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope c :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hcHalf hcOne
  have hslopeHalf :
      targetAmplitudeCarlsonTwoHeightBalancedSlope c < 1 / 2 :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half
      hcHalf hcOne
  have hgap : 0 < beta - c := sub_pos.mpr hcBeta
  have hbalancePos :
      0 < jointTwoHeightSigmaBalanceValue beta c := by
    unfold jointTwoHeightSigmaBalanceValue
    positivity
  have himprovement :
      jointTwoHeightSigmaBalanceValue beta c < beta - c := by
    have hgain :
        0 <
          (beta - c) *
            (1 / 2 -
              targetAmplitudeCarlsonTwoHeightBalancedSlope c) :=
      mul_pos hgap (sub_pos.mpr hslopeHalf)
    unfold jointTwoHeightSigmaBalanceValue
    nlinarith
  change
    c < jointTwoHeightImprovedGlobalCapThreshold beta ∧
      jointTwoHeightImprovedGlobalCapThreshold beta < beta
  unfold jointTwoHeightImprovedGlobalCapThreshold
  exact ⟨by linarith, by linarith⟩

/-- The global contour gap is positive exactly below the improved cap
threshold.  This is the exact arithmetic gain obtained by optimizing
`sigma`, not merely a sufficient condition. -/
theorem
    contourFloor_lt_jointTwoHeightGlobalOuterExponentCeiling_iff
    {beta theta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta) :
    1 - beta < jointTwoHeightGlobalOuterExponentCeiling beta theta ↔
      theta < jointTwoHeightImprovedGlobalCapThreshold beta := by
  let sigmaOpt := jointTwoHeightOptimalDensityThreshold beta theta
  let c := targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta
  have hoptimizer :
      IsJointTwoHeightSigmaOptimizer beta theta sigmaOpt := by
    simpa [sigmaOpt] using
      jointTwoHeightOptimalDensityThreshold_spec
        hthetaHalf hthetaBeta hbetaOne
  rcases hoptimizer with
    ⟨hsigmaOptHalf, hsigmaOptTheta, hbalanceOptRaw⟩
  have hbalanceOpt :
      jointTwoHeightSigmaBalanceValue beta sigmaOpt =
        beta - theta := by
    simpa [jointTwoHeightSigmaBalanceValue] using hbalanceOptRaw
  rcases
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
        hbeta hbetaOne with
    ⟨hcHalf, hcBeta, _hcOne⟩
  have hoptLtC :
      sigmaOpt < c ↔
        theta < jointTwoHeightImprovedGlobalCapThreshold beta := by
    constructor
    · intro hsigmaOptC
      have hdecrease :
          jointTwoHeightSigmaBalanceValue beta c <
            jointTwoHeightSigmaBalanceValue beta sigmaOpt :=
        jointTwoHeightSigmaBalanceValue_strictAnti
          hsigmaOptHalf hsigmaOptC hcBeta hbetaOne
      rw [hbalanceOpt] at hdecrease
      unfold jointTwoHeightImprovedGlobalCapThreshold
      change
        theta <
          beta - jointTwoHeightSigmaBalanceValue beta c
      linarith
    · intro htheta
      unfold jointTwoHeightImprovedGlobalCapThreshold at htheta
      change
        theta <
          beta - jointTwoHeightSigmaBalanceValue beta c at htheta
      by_contra hnot
      have hcOpt : c ≤ sigmaOpt := le_of_not_gt hnot
      rcases eq_or_lt_of_le hcOpt with heq | hcOptLt
      · rw [heq, hbalanceOpt] at htheta
        linarith
      · have hdecrease :
            jointTwoHeightSigmaBalanceValue beta sigmaOpt <
              jointTwoHeightSigmaBalanceValue beta c :=
          jointTwoHeightSigmaBalanceValue_strictAnti
            hcHalf hcOptLt
            (hsigmaOptTheta.trans hthetaBeta) hbetaOne
        rw [hbalanceOpt] at hdecrease
        linarith
  constructor
  · intro hfloor
    rw [jointTwoHeightGlobalOuterExponentCeiling_eq
      hthetaHalf hthetaBeta hbetaOne] at hfloor
    rcases lt_min_iff.mp hfloor with ⟨_hunit, hlow⟩
    apply hoptLtC.mp
    dsimp [c]
    unfold targetAmplitudeCarlsonTwoHeightCanonicalThreshold
    linarith
  · intro htheta
    have hsigmaOptC : sigmaOpt < c :=
      hoptLtC.mpr htheta
    rw [jointTwoHeightGlobalOuterExponentCeiling_eq
      hthetaHalf hthetaBeta hbetaOne]
    apply lt_min
    · have hbetaPos : 0 < beta := by
        exact (by norm_num : (0 : ℝ) < 2 / 3).trans hbeta
      linarith
    · dsimp [c] at hsigmaOptC
      unfold targetAmplitudeCarlsonTwoHeightCanonicalThreshold at hsigmaOptC
      linarith

/-- Below the improved threshold there is a positive strict loss realizing a
globally near-optimal, contour-compatible truncation exponent. -/
theorem exists_pos_lt_jointTwoHeightGlobalContourGap_of_lt_improvedThreshold
    {beta theta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (htheta :
      theta < jointTwoHeightImprovedGlobalCapThreshold beta) :
    ∃ eta : ℝ,
      0 < eta ∧
      eta <
        jointTwoHeightGlobalOuterExponentCeiling beta theta -
          (1 - beta) := by
  have hgap :
      0 <
        jointTwoHeightGlobalOuterExponentCeiling beta theta -
          (1 - beta) := by
    have :=
      (contourFloor_lt_jointTwoHeightGlobalOuterExponentCeiling_iff
        hbeta hbetaOne hthetaHalf hthetaBeta).mpr htheta
    linarith
  refine
    ⟨(jointTwoHeightGlobalOuterExponentCeiling beta theta -
        (1 - beta)) / 2, ?_, ?_⟩ <;>
    linarith

end PrimeNumberTheorem
