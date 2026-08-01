import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent

/-!
# Joint two-height target-amplitude parameter feasibility

The low global layer and the Carlson strip previously supplied separate
strict-margin existence theorems.  This file constructs one common outer
height exponent and both balanced cuts.  Thus every `2 / 3 < beta < 1`
supplies a single numerical input tuple for the two transfer mechanisms.
-/

namespace PrimeNumberTheorem

/-- For every target real part strictly between `2 / 3` and `1`, one can
simultaneously choose:

* a low-layer endpoint `sigma`;
* a Carlson strip endpoint `tau`;
* one contour-compatible outer height exponent `alpha <= 1`;
* the balanced low and Carlson cuts;
* positive strict margins for all four target-normalized exponents.

This is the joint numerical feasibility statement needed to remove separate
margin hypotheses from the downstream two-height transfer chain. -/
theorem exists_jointTwoHeightTargetAmplitudeParameters
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh epsilonLow epsilonHigh : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      tau < beta ∧
      sigma < 1 ∧
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
  let threshold : ℝ := (3 * beta - 1) / 2
  have hhalfThreshold : 1 / 2 < threshold := by
    dsimp [threshold]
    linarith
  have hthresholdBeta : threshold < beta := by
    dsimp [threshold]
    linarith
  let sigma : ℝ := (1 / 2 + threshold) / 2
  have hsigmaHalf : 1 / 2 < sigma := by
    dsimp [sigma]
    linarith
  have hsigmaThreshold : sigma < threshold := by
    dsimp [sigma]
    linarith
  have hsigmaBeta : sigma < beta :=
    hsigmaThreshold.trans hthresholdBeta
  have hsigmaOne : sigma < 1 :=
    hsigmaBeta.trans hbetaOne
  let slope : ℝ :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma
  have hslopePos : 0 < slope := by
    simpa [slope] using
      targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
        hsigmaHalf hsigmaOne
  have hslopeHalf : slope < 1 / 2 := by
    simpa [slope] using
      targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half
        hsigmaHalf hsigmaOne
  have hfloorPos : 0 < 1 - beta :=
    sub_pos.mpr hbetaOne
  have hslopeFloor :
      slope * (1 - beta) < (1 / 2) * (1 - beta) :=
    mul_lt_mul_of_pos_right hslopeHalf hfloorPos
  have hsigmaFeasible :
      slope * (1 - beta) + sigma - beta < 0 := by
    have hthresholdIdentity :
        threshold = beta - (1 - beta) / 2 := by
      dsimp [threshold]
      ring
    linarith
  let tauUpper : ℝ := beta - slope * (1 - beta)
  have hsigmaTauUpper : sigma < tauUpper := by
    dsimp [tauUpper]
    linarith
  have hslopeFloorPos : 0 < slope * (1 - beta) :=
    mul_pos hslopePos hfloorPos
  have htauUpperBeta : tauUpper < beta := by
    dsimp [tauUpper]
    linarith
  let tau : ℝ := (sigma + tauUpper) / 2
  have hsigmaTau : sigma < tau := by
    dsimp [tau]
    linarith
  have htauTauUpper : tau < tauUpper := by
    dsimp [tau]
    linarith
  have htauBeta : tau < beta :=
    htauTauUpper.trans htauUpperBeta
  have hhighFloor :
      slope * (1 - beta) < beta - tau := by
    dsimp [tauUpper] at htauTauUpper
    linarith
  let lowUpper : ℝ := 2 * (beta - sigma)
  have hfloorLowUpper : 1 - beta < lowUpper := by
    dsimp [lowUpper]
    have hsigmaThreshold' :
        sigma < (3 * beta - 1) / 2 := by
      simpa [threshold] using hsigmaThreshold
    linarith
  let highUpper : ℝ := (beta - tau) / slope
  have hfloorHighUpper : 1 - beta < highUpper := by
    dsimp [highUpper]
    rw [lt_div_iff₀ hslopePos]
    simpa [mul_comm] using hhighFloor
  have hbetaPos : 0 < beta := by
    linarith
  have hfloorOne : 1 - beta < 1 := by
    linarith
  let cap : ℝ := min 1 (min lowUpper highUpper)
  have hfloorCap : 1 - beta < cap := by
    dsimp [cap]
    exact lt_min hfloorOne (lt_min hfloorLowUpper hfloorHighUpper)
  have hcapOne : cap ≤ 1 := by
    dsimp [cap]
    exact min_le_left _ _
  have hcapLowUpper : cap ≤ lowUpper := by
    dsimp [cap]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcapHighUpper : cap ≤ highUpper := by
    dsimp [cap]
    exact (min_le_right _ _).trans (min_le_right _ _)
  let alpha : ℝ := ((1 - beta) + cap) / 2
  have hcontour : 1 - beta < alpha := by
    dsimp [alpha]
    linarith
  have halphaCap : alpha < cap := by
    dsimp [alpha]
    linarith
  have halphaPos : 0 < alpha :=
    hfloorPos.trans hcontour
  have halphaOne : alpha ≤ 1 :=
    (halphaCap.le.trans hcapOne)
  have halphaLowUpper : alpha < lowUpper :=
    halphaCap.trans_le hcapLowUpper
  have halphaHighUpper : alpha < highUpper :=
    halphaCap.trans_le hcapHighUpper
  let gammaLow : ℝ := alpha / 2
  have hgammaLowPos : 0 < gammaLow := by
    dsimp [gammaLow]
    linarith
  have hgammaLowAlpha : gammaLow ≤ alpha := by
    dsimp [gammaLow]
    linarith
  have hlowCommon : gammaLow + sigma - beta < 0 := by
    dsimp [gammaLow, lowUpper] at *
    linarith
  let epsilonLow : ℝ :=
    -(gammaLow + sigma - beta) / 2
  have hepsilonLow : 0 < epsilonLow := by
    dsimp [epsilonLow]
    linarith
  have hlowMargin :
      gammaLow + sigma - beta + epsilonLow < 0 := by
    dsimp [epsilonLow]
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
  have hhighProduct : slope * alpha < beta - tau := by
    dsimp [highUpper] at halphaHighUpper
    simpa [mul_comm] using
      (lt_div_iff₀ hslopePos).mp halphaHighUpper
  have hbalancedHigh :
      targetAmplitudeCarlsonTwoHeightBalancedExponent
          beta sigma tau alpha < 0 := by
    unfold targetAmplitudeCarlsonTwoHeightBalancedExponent
    change tau - beta + slope * alpha < 0
    linarith
  let gammaHigh : ℝ :=
    carlsonTwoHeightBalancedCut sigma alpha
  have hgammaHighPos : 0 < gammaHigh := by
    simpa [gammaHigh] using
      carlsonTwoHeightBalancedCut_pos
        hsigmaHalf hsigmaOne halphaPos
  have hgammaHighAlpha : gammaHigh < alpha := by
    simpa [gammaHigh] using
      carlsonTwoHeightBalancedCut_lt_alpha
        hsigmaHalf hsigmaOne halphaPos
  let epsilonHigh : ℝ :=
    -targetAmplitudeCarlsonTwoHeightBalancedExponent
        beta sigma tau alpha / 2
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
    ⟨sigma, tau, alpha, gammaLow, gammaHigh, epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, htauBeta, hsigmaOne,
      hcontour, halphaPos, halphaOne, rfl,
      hgammaLowPos, hgammaLowAlpha, rfl,
      hgammaHighPos, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowMargin, hhighGlobalMargin, hcarlsonLow, hcarlsonHigh⟩

end PrimeNumberTheorem
