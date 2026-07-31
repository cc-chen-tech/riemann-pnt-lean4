import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryExtensionAbsoluteMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedTargetLineSelector
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer

/-!
# Boundary-captured moving-seed signed PNT transfer

The residual moving extension is controlled by absolute mass, so no
cancellation assumption is imposed outside the captured target-line cluster.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter

noncomputable section

/-- For `2 / 3 < beta < 1` and `0 < q < c`, automatically select the Carlson
geometry and a finite target-line capture cluster.  Signed coefficient-`c`
visible-main witnesses for that captured cluster transfer to signed actual PNT
witnesses with coefficient `q / 2`. -/
theorem
    exists_automaticGoodHeight_boundaryCapturedMovingSeedSignedNaturalTargetTransfer
    {S₀ : Finset ℂ} {beta c q : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hq : 0 < q)
    (hqC : q < c)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ sigma transferTau alpha : ℝ, ∃ S : Finset ℂ,
      1 / 2 < sigma ∧
      sigma < transferTau ∧
      1 / 2 < transferTau ∧
      transferTau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      (∀ rho ∈ S₀, rho ∈ S) ∧
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      IsTargetRealPartNontrivialZeroSeed beta S ∧
      OutsideClusterRealPartCap S beta ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        HasFarNaturalPointPositiveTargetAmplitudeWitness
            (fun m : ℕ =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection) S (m : ℝ))
            (fun m : ℕ =>
              c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
            (fun m : ℕ =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection) S (m : ℝ))
            (fun m : ℕ =>
              c * targetZeroPowerAmplitude beta (m : ℝ)) →
        (∃ rate : ℝ,
            0 < rate ∧
            rate ≤ 1 ∧
            Tendsto
              (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (nhds 0)) ∧
          HasFarSignedTargetAmplitudeWitnesses
            relativeChebyshevPsi0Error
            (fun x =>
              (q / 2) * targetZeroPowerAmplitude beta x) := by
  have hanchor :
      (1 / 2 : ℝ) < (3 * beta - 1) / 2 := by
    linarith
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        (theta := (1 / 2 : ℝ)) hbeta hbetaOne hanchor with
    ⟨sigma, transferTau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hhalfTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  rcases
      exists_targetLine_actualCarlsonFiniteSeedGapTransferCluster
        hS₀ hseed hsigmaHalf hsigmaOne hqC hcap with
    ⟨S, hS₀S, hS, htarget, hcapS, hreHigh, hreReal, hgap⟩
  refine
    ⟨sigma, transferTau, alpha, S,
      hsigmaHalf, hsigmaTau, hhalfTau, htauBeta,
      hcontour, halpha, halphaOne,
      hS₀S, hS, htarget, hcapS, hreHigh, hreReal, hgap, ?_⟩
  intro selection hseedPos hseedNeg
  let H := selectedUniformGoodHeight alpha selection
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  let delta := (c - q) -
    2 * actualCarlsonOutsideClusterBoundaryMass
      (sigma := sigma) beta S
  have hdelta : 0 < delta := by
    simpa [delta] using hgap
  have hfull :=
    eventually_selectedFullOutsideClusterPNTAbsoluteMass_div_target_lt_two_mul_boundaryMass_add
      (fun rho => (hS rho).symm)
      hsigmaHalf hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hHnonneg hHle hreHigh hreReal hdelta
  have hextension :=
    eventually_selectedMovingRightEdgeExtension_div_target_lt_two_mul_boundaryMass_add
      (sigma := sigma) (transferTau := transferTau)
      (delta := delta) hfull
  have hextensionGap :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain H
            (movingRightEdgeExceptionalCluster H transferTau (m : ℝ) \ S)
            (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) < c - q := by
    simpa [delta] using hextension
  have hamplitude :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain H
            (movingRightEdgeExceptionalCluster H transferTau (m : ℝ) \ S)
            (m : ℝ)| <
          (c - q) * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [hextensionGap, hamplitude] with m hm hamp
    exact (div_lt_iff₀ hamp).mp hm
  have hbetaPos : 0 < beta := by linarith
  have hnet : 0 < c - (c - q) := by linarith
  have hresult :=
    unified_automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalTargetTransfer
      (S₀ := S) (c := c) (loss := c - q)
      hbetaPos halphaOne hcontour selection
      hsigmaHalf hsigmaOne htauBeta halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le
      hepsilonHigh hstripLow hstripHigh
      hnet htarget
      (by simpa [H] using hseedPos)
      (by simpa [H] using hseedNeg)
      (by simpa [H] using hnew)
  refine ⟨hresult.1, ?_⟩
  convert hresult.2 using 1 <;> funext x <;> ring

end

end PrimeNumberTheorem

