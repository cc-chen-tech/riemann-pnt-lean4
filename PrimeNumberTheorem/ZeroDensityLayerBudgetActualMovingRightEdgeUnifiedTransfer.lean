import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingClusterComplementMajorant
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticGoodHeightNaturalUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightPrescribedCapFeasibility

/-!
# Actual unified transfer from a moving right-edge cluster

The moving right-edge complement is now discharged by Carlson without a
zero-free cap. A far target-amplitude witness for the moving visible cluster
therefore transfers to the actual PNT error.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Fixed-parameter natural-point lower transfer from the moving right-edge
visible cluster to the actual PNT error. -/
theorem automaticGoodHeight_twoHeight_movingRightEdgeNaturalPointLowerTransfer
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hbeta : 0 < beta)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          movingRightEdgeVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            tau (m : ℝ))
        (fun m : ℕ =>
          targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarTargetAmplitudeWitness
      relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  let H := selectedUniformGoodHeight alpha selection
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg :
      ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  have hcomplement :=
    selectedMovingRightEdgeOutsideClusterComplement_targetAmplitudeNegligible
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHnonneg hHle
  have hremainder :=
    selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hcontourMargin selection
  apply HasFarNaturalPointTargetAmplitudeWitness.toReal
  apply
    hasFarNaturalPointTargetAmplitudeWitness_of_three_remainders
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
        hbeta).naturalPoint
      hremainder.negligible
      hcomplement.naturalPoint
      (by simpa [H] using hmain)
  intro m
  exact
    relativeChebyshevPsi0Error_eq_movingRightEdgeCluster_add_actualResiduals
      H tau (m : ℝ)

/-- Fixed-parameter unified output: actual PNT convergence together with the
moving-cluster lower transfer. -/
theorem unified_automaticGoodHeight_twoHeight_movingRightEdgeNaturalTargetTransfer
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hbeta : 0 < beta)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh :
      alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHigh : 0 < gammaHigh)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hepsilonHigh : 0 < epsilonHigh)
    (hstripLow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0)
    (hstripHigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          movingRightEdgeVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            tau (m : ℝ))
        (fun m : ℕ =>
          targetZeroPowerAmplitude beta (m : ℝ))) :
    (∃ rate : ℝ,
        0 < rate ∧
        rate ≤ 1 ∧
        Tendsto
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          atTop (nhds 0)) ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => targetZeroPowerAmplitude beta x / 2) := by
  exact
    ⟨exists_fixedRate_relativeChebyshevPsi0Error_tendsto,
      automaticGoodHeight_twoHeight_movingRightEdgeNaturalPointLowerTransfer
        hbeta halphaOne hcontourMargin selection
        hsigma hsigmaOne halpha hgammaLow hepsilonLow
        hlowLow hlowHigh hgammaHigh hgammaHighAlpha
        hepsilonHigh hstripLow hstripHigh hmain⟩

/-- From `2 / 3 < beta < 1`, automatically select all two-height and contour
parameters. No zero-free or outside-cluster cap is required: every visible
zero with real part at least `tau` enters the moving main. -/
theorem exists_automaticGoodHeight_movingRightEdgeNaturalTargetTransfer
    {beta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      1 / 2 < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        HasFarNaturalPointTargetAmplitudeWitness
            (fun m : ℕ =>
              movingRightEdgeVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection)
                tau (m : ℝ))
            (fun m : ℕ =>
              targetZeroPowerAmplitude beta (m : ℝ)) →
        (∃ rate : ℝ,
            0 < rate ∧
            rate ≤ 1 ∧
            Tendsto
              (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (nhds 0)) ∧
          HasFarTargetAmplitudeWitness
            relativeChebyshevPsi0Error
            (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hanchor :
      (1 / 2 : ℝ) < (3 * beta - 1) / 2 := by
    linarith
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        hbeta hbetaOne hanchor with
    ⟨sigma, tau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hanchorTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  have hbetaPos : 0 < beta := by
    linarith
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hanchorTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hmain
  exact
    unified_automaticGoodHeight_twoHeight_movingRightEdgeNaturalTargetTransfer
      hbetaPos halphaOne hcontour selection
      hsigmaHalf hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha.le
      hepsilonHigh hstripLow hstripHigh hmain

end PrimeNumberTheorem
