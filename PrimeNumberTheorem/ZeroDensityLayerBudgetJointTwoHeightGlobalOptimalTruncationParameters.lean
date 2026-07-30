import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightUniqueSigmaOptimizer
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightNearOptimalTruncationParameters

/-!
# Globally optimal truncation parameters

The unique balancing density threshold is packaged as a canonical parameter.
Its prescribed-cap ceiling is then the global ceiling over every admissible
density threshold, and every exponent strictly below it is converted into the
full strict-margin tuple used by the actual transfer.
-/

namespace PrimeNumberTheorem

/-- Canonical density threshold selected from the unique optimizer when
`1 / 2 < theta < beta < 1`, with a harmless fallback outside that regime. -/
noncomputable def jointTwoHeightOptimalDensityThreshold
    (beta theta : ℝ) : ℝ :=
  if h : 1 / 2 < theta ∧ theta < beta ∧ beta < 1 then
    Classical.choose
      (existsUnique_jointTwoHeightSigmaOptimizer
        h.1 h.2.1 h.2.2).exists
  else
    1 / 2

theorem jointTwoHeightOptimalDensityThreshold_spec
    {beta theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1) :
    IsJointTwoHeightSigmaOptimizer beta theta
      (jointTwoHeightOptimalDensityThreshold beta theta) := by
  unfold jointTwoHeightOptimalDensityThreshold
  rw [dif_pos ⟨hthetaHalf, hthetaBeta, hbetaOne⟩]
  exact
    Classical.choose_spec
      (existsUnique_jointTwoHeightSigmaOptimizer
        hthetaHalf hthetaBeta hbetaOne).exists

/-- Every balancing threshold equals the canonical optimizer. -/
theorem eq_jointTwoHeightOptimalDensityThreshold_of_optimizer
    {beta theta sigma : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1)
    (hoptimizer : IsJointTwoHeightSigmaOptimizer beta theta sigma) :
    sigma = jointTwoHeightOptimalDensityThreshold beta theta :=
  IsJointTwoHeightSigmaOptimizer.unique
    hthetaBeta hbetaOne hoptimizer
    (jointTwoHeightOptimalDensityThreshold_spec
      hthetaHalf hthetaBeta hbetaOne)

/-- Global outer-height ceiling after optimizing both the strip endpoint and
the density threshold. -/
noncomputable def jointTwoHeightGlobalOuterExponentCeiling
    (beta theta : ℝ) : ℝ :=
  jointTwoHeightPrescribedCapOuterExponentCeiling
    beta (jointTwoHeightOptimalDensityThreshold beta theta) theta

/-- The global ceiling has the low-layer value at the balancing threshold,
subject only to the closed unit cap. -/
theorem jointTwoHeightGlobalOuterExponentCeiling_eq
    {beta theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1) :
    jointTwoHeightGlobalOuterExponentCeiling beta theta =
      min 1
        (2 *
          (beta -
            jointTwoHeightOptimalDensityThreshold beta theta)) := by
  unfold jointTwoHeightGlobalOuterExponentCeiling
  exact
    jointTwoHeightPrescribedCapOuterExponentCeiling_eq_of_sigmaOptimizer
      hthetaBeta hbetaOne
      (jointTwoHeightOptimalDensityThreshold_spec
        hthetaHalf hthetaBeta hbetaOne)

/-- No admissible fixed density threshold has a larger prescribed-cap ceiling
than the canonical global ceiling. -/
theorem
    jointTwoHeightPrescribedCapOuterExponentCeiling_le_global
    {beta theta sigma : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 < sigma)
    (hsigmaBeta : sigma < beta) :
    jointTwoHeightPrescribedCapOuterExponentCeiling beta sigma theta ≤
      jointTwoHeightGlobalOuterExponentCeiling beta theta := by
  unfold jointTwoHeightGlobalOuterExponentCeiling
  exact
    jointTwoHeightPrescribedCapOuterExponentCeiling_le_at_sigmaOptimizer
      hthetaBeta hbetaOne
      (jointTwoHeightOptimalDensityThreshold_spec
        hthetaHalf hthetaBeta hbetaOne)
      hsigmaHalf hsigmaBeta

/-- Every positive loss smaller than the global contour gap gives the complete
transfer-ready parameter tuple at the exact globally near-optimal exponent
`globalCeiling - eta`. -/
theorem exists_jointTwoHeightGloballyNearOptimalTruncationParameters
    {beta theta eta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1)
    (hetaPos : 0 < eta)
    (hetaGap :
      eta <
        jointTwoHeightGlobalOuterExponentCeiling beta theta -
          (1 - beta)) :
    ∃ sigma tau alpha gammaLow gammaHigh epsilonLow epsilonHigh : ℝ,
      sigma = jointTwoHeightOptimalDensityThreshold beta theta ∧
      IsJointTwoHeightSigmaOptimizer beta theta sigma ∧
      alpha =
        jointTwoHeightGlobalOuterExponentCeiling beta theta - eta ∧
      sigma < tau ∧
      theta < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      gammaLow = alpha / 2 ∧
      0 < gammaLow ∧
      gammaLow ≤ alpha ∧
      gammaHigh = carlsonTwoHeightBalancedCut sigma alpha ∧
      0 < gammaHigh ∧
      gammaHigh < alpha ∧
      0 < epsilonLow ∧
      0 < epsilonHigh ∧
      gammaLow + sigma - beta + epsilonLow < 0 ∧
      alpha + sigma - beta - gammaLow + epsilonLow < 0 ∧
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0 ∧
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0 := by
  let sigma := jointTwoHeightOptimalDensityThreshold beta theta
  have hoptimizer :
      IsJointTwoHeightSigmaOptimizer beta theta sigma := by
    simpa [sigma] using
      jointTwoHeightOptimalDensityThreshold_spec
        hthetaHalf hthetaBeta hbetaOne
  rcases hoptimizer with
    ⟨hsigmaHalf, hsigmaTheta, hbalance⟩
  have hsigmaOne : sigma < 1 :=
    hsigmaTheta.trans (hthetaBeta.trans hbetaOne)
  have hetaGapFixed :
      eta <
        jointTwoHeightPrescribedCapOuterExponentCeiling
              beta sigma theta -
            (1 - beta) := by
    simpa [jointTwoHeightGlobalOuterExponentCeiling, sigma] using hetaGap
  rcases
      exists_jointTwoHeightNearOptimalTruncationParameters
        hbetaOne hsigmaHalf hsigmaOne hetaPos hetaGapFixed with
    ⟨tau, alpha, gammaLow, gammaHigh, epsilonLow, epsilonHigh,
      halphaEq, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne,
      hgammaLowEq, hgammaLow, hgammaLowAlpha,
      hgammaHighEq, hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  have halphaGlobal :
      alpha =
        jointTwoHeightGlobalOuterExponentCeiling beta theta - eta := by
    simpa [jointTwoHeightGlobalOuterExponentCeiling, sigma] using halphaEq
  exact
    ⟨sigma, tau, alpha, gammaLow, gammaHigh, epsilonLow, epsilonHigh,
      rfl, ⟨hsigmaHalf, hsigmaTheta, hbalance⟩,
      halphaGlobal, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne,
      hgammaLowEq, hgammaLow, hgammaLowAlpha,
      hgammaHighEq, hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩

end PrimeNumberTheorem
