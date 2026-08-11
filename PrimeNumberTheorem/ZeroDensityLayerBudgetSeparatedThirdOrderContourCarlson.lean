import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicSmoothedHighToLowTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderDynamicContourDecay

open Complex Set Filter Topology

namespace PrimeNumberTheorem

/-- Separate the high analytic contour from the lower Carlson balancing height. -/
theorem exists_separatedThirdOrderContourHeight_with_actualCubicSmoothedHighToLowTransfer
    {beta c : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (hc : 1 < c) (hcTwo : c ≤ 2) :
    ∃ sigma tau layerAlpha gammaLow gammaHigh epsilonLow epsilonHigh : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      tau < beta ∧
      sigma < 1 ∧
      1 - beta < layerAlpha ∧
      0 < layerAlpha ∧
      layerAlpha ≤ 1 ∧
      gammaLow = layerAlpha / 2 ∧
      0 < gammaLow ∧
      gammaLow ≤ layerAlpha ∧
      gammaHigh = carlsonTwoHeightBalancedCut sigma layerAlpha ∧
      0 < gammaHigh ∧
      gammaHigh < layerAlpha ∧
      0 < epsilonLow ∧
      0 < epsilonHigh ∧
      gammaLow + sigma - beta + epsilonLow < 0 ∧
      layerAlpha + sigma - beta - gammaLow + epsilonLow < 0 ∧
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0 ∧
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau layerAlpha gammaHigh + epsilonHigh < 0 ∧
      cubicCarlsonL2BlockExponent beta sigma tau gammaLow < 0 ∧
      cubicCarlsonL2BlockExponent beta sigma tau gammaHigh < 0 ∧
      cubicCarlsonL2BlockExponent beta sigma tau layerAlpha < 0 ∧
      2 / 3 < (3 / 4 : ℝ) ∧
      (3 / 4 : ℝ) < 1 ∧
      gammaLow ≤ (3 / 4 : ℝ) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ x : ℝ in atTop,
          ∃ T ∈ Icc (x ^ (3 / 4 : ℝ)) (x ^ (3 / 4 : ℝ) + 1),
            ExplicitFormulaAux.goodHeight T ∧
            ‖ExplicitFormulaResidues.thirdOrderContourRemainder
                x (-1) c (T / (2 * Real.pi))‖ < ε) ∧
      ∀ certificate : CarlsonEventualMajorant sigma, ∀ S : Finset ℂ,
        (∀ᶠ m : ℕ in atTop,
          actualCubicNormalizedSmoothedStripEnergyUpTo
              beta sigma tau (3 / 4 : ℝ) S m =
            actualCubicNormalizedSmoothedStripEnergyUpTo
                beta sigma tau gammaLow S m +
              actualCubicNormalizedSmoothedStripEnergyBetween
                beta sigma tau gammaLow (3 / 4 : ℝ) S m) ∧
        Tendsto
          (actualCubicNormalizedSmoothedStripEnergyBetween
            beta sigma tau gammaLow (3 / 4 : ℝ) S)
          atTop (nhds 0) := by
  obtain ⟨sigma, tau, layerAlpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigma, hsigmaTau, htauBeta, hsigmaOne,
      hcontourLayer, hlayerAlpha, hlayerAlphaOne,
      hgammaLowEq, hgammaLow, hgammaLowLayer,
      hgammaHighEq, hgammaHigh, hgammaHighLayer,
      hepsilonLow, hepsilonHigh,
      hlow, hhigh, hcarlsonLow, hcarlsonHigh,
      hcubicLow, hcubicHigh, hcubicLayer⟩ :=
    exists_jointTwoHeightTargetAmplitudeParameters_with_cubicL2
      hbeta hbetaOne
  obtain ⟨C, hC, hcontour⟩ :=
    ExplicitFormulaResidues.exists_uniform_eventually_goodHeight_norm_thirdOrderContourRemainder_lt
      (alpha := (3 / 4 : ℝ)) (c := c) (by norm_num) (by norm_num) hc hcTwo
  have hgammaLowContour : gammaLow ≤ (3 / 4 : ℝ) := by
    rw [hgammaLowEq]
    linarith
  refine ⟨sigma, tau, layerAlpha, gammaLow, gammaHigh,
    epsilonLow, epsilonHigh,
    hsigma, hsigmaTau, htauBeta, hsigmaOne,
    hcontourLayer, hlayerAlpha, hlayerAlphaOne,
    hgammaLowEq, hgammaLow, hgammaLowLayer,
    hgammaHighEq, hgammaHigh, hgammaHighLayer,
    hepsilonLow, hepsilonHigh,
    hlow, hhigh, hcarlsonLow, hcarlsonHigh,
    hcubicLow, hcubicHigh, hcubicLayer,
    by norm_num, by norm_num, hgammaLowContour, hcontour, ?_⟩
  intro certificate S
  exact certificate.actualCubicSmoothedHighToLowTransfer_of_tail
    hgammaLowContour S
    (certificate.tendsto_actualCubicCarlsonNormalizedDiagonalTail_zero
      hgammaLow hcubicLow S)

end PrimeNumberTheorem
