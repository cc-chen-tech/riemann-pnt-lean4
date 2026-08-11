import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightOptimalPrescribedCapOuterExponent

/-!
# Near-optimal truncation parameters

Every exponent below the optimized prescribed-cap ceiling is converted into
the exact cuts and strict margins used by the actual two-height transfer.
-/

namespace PrimeNumberTheorem

/-- A positive feasible fixed outer exponent supplies the balanced low and
Carlson cuts and positive strict margins at that same exponent. -/
theorem exists_jointTwoHeightStrictMargins_of_outerExponentFeasible
    {beta sigma tau alpha : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halphaPos : 0 < alpha)
    (halpha :
      IsJointTwoHeightOuterExponentFeasible
        beta sigma tau alpha) :
    ∃ gammaLow gammaHigh epsilonLow epsilonHigh : ℝ,
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
  rcases halpha with
    ⟨_halphaOne, hlowBalanced, hcarlsonBalanced⟩
  let gammaLow := alpha / 2
  let epsilonLow :=
    -(alpha / 2 + sigma - beta) / 2
  have hgammaLowPos : 0 < gammaLow := by
    dsimp [gammaLow]
    linarith
  have hgammaLowAlpha : gammaLow ≤ alpha := by
    dsimp [gammaLow]
    linarith
  have hepsilonLow : 0 < epsilonLow := by
    dsimp [epsilonLow]
    linarith
  have hlowMargin :
      gammaLow + sigma - beta + epsilonLow < 0 := by
    dsimp [gammaLow, epsilonLow]
    linarith
  have hhighGlobalMargin :
      alpha + sigma - beta - gammaLow + epsilonLow < 0 := by
    have hbalanced :
        alpha + sigma - beta - gammaLow =
          gammaLow + sigma - beta := by
      dsimp [gammaLow]
      ring
    rw [hbalanced]
    exact hlowMargin
  let gammaHigh :=
    carlsonTwoHeightBalancedCut sigma alpha
  let epsilonHigh :=
    -targetAmplitudeCarlsonTwoHeightBalancedExponent
        beta sigma tau alpha / 2
  have hgammaHighPos : 0 < gammaHigh := by
    simpa [gammaHigh] using
      carlsonTwoHeightBalancedCut_pos
        hsigmaHalf hsigmaOne halphaPos
  have hgammaHighAlpha : gammaHigh < alpha := by
    simpa [gammaHigh] using
      carlsonTwoHeightBalancedCut_lt_alpha
        hsigmaHalf hsigmaOne halphaPos
  have hepsilonHigh : 0 < epsilonHigh := by
    dsimp [epsilonHigh]
    linarith
  have hden :
      carlsonTwoHeightDensityExponent sigma + 1 ≠ 0 := by
    have hq :=
      carlsonTwoHeightDensityExponent_pos hsigmaHalf hsigmaOne
    linarith
  have hcarlsonLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0 := by
    rw [show gammaHigh =
        carlsonTwoHeightBalancedCut sigma alpha by rfl]
    rw [targetAmplitudeCarlsonTwoHeightLowExponent_balanced hden]
    dsimp [epsilonHigh]
    linarith
  have hcarlsonHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0 := by
    rw [show gammaHigh =
        carlsonTwoHeightBalancedCut sigma alpha by rfl]
    rw [targetAmplitudeCarlsonTwoHeightHighExponent_balanced hden]
    dsimp [epsilonHigh]
    linarith
  exact
    ⟨gammaLow, gammaHigh, epsilonLow, epsilonHigh,
      rfl, hgammaLowPos, hgammaLowAlpha,
      rfl, hgammaHighPos, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowMargin, hhighGlobalMargin,
      hcarlsonLow, hcarlsonHigh⟩

/-- Every positive distance `eta` smaller than the contour-compatible ceiling
gap gives a complete transfer-ready parameter tuple at the exact near-optimal
outer exponent `ceiling - eta`. -/
theorem exists_jointTwoHeightNearOptimalTruncationParameters
    {beta sigma theta eta : ℝ}
    (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hetaPos : 0 < eta)
    (hetaGap :
      eta <
        jointTwoHeightPrescribedCapOuterExponentCeiling
            beta sigma theta -
          (1 - beta)) :
    ∃ tau alpha gammaLow gammaHigh epsilonLow epsilonHigh : ℝ,
      alpha =
        jointTwoHeightPrescribedCapOuterExponentCeiling
            beta sigma theta -
          eta ∧
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
  let alpha :=
    jointTwoHeightPrescribedCapOuterExponentCeiling
        beta sigma theta -
      eta
  have hcontour : 1 - beta < alpha := by
    dsimp [alpha]
    linarith
  have halphaCeiling :
      alpha <
        jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta := by
    dsimp [alpha]
    linarith
  have halphaPos : 0 < alpha := by
    have hfloorPos : 0 < 1 - beta :=
      sub_pos.mpr hbetaOne
    linarith
  rcases
      jointTwoHeightPrescribedCapOuterExponentFeasible_of_lt_ceiling
        hbetaOne hsigmaHalf hsigmaOne hcontour halphaCeiling with
    ⟨tau, hsigmaTau, hthetaTau, htauBeta, halpha⟩
  rcases halpha with
    ⟨halphaOne, hlowBalanced, hcarlsonBalanced⟩
  have halphaFeasible :
      IsJointTwoHeightOuterExponentFeasible
        beta sigma tau alpha :=
    ⟨halphaOne, hlowBalanced, hcarlsonBalanced⟩
  rcases
      exists_jointTwoHeightStrictMargins_of_outerExponentFeasible
        hsigmaHalf hsigmaOne halphaPos halphaFeasible with
    ⟨gammaLow, gammaHigh, epsilonLow, epsilonHigh,
      hgammaLowEq, hgammaLow, hgammaLowAlpha,
      hgammaHighEq, hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  exact
    ⟨tau, alpha, gammaLow, gammaHigh, epsilonLow, epsilonHigh,
      rfl, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne,
      hgammaLowEq, hgammaLow, hgammaLowAlpha,
      hgammaHighEq, hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩

end PrimeNumberTheorem
