import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightUnifiedTargetTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFullRelativeDecay

/-!
# Automatic good-height natural-point unified transfer

The selected uniform good height supplies only a natural-point remainder
certificate.  This module combines it with the selected two-height zero-tail
theorem without strengthening the sampling domain.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- The uniform selected good height is eventually nonnegative and bounded
above by its polynomial envelope. -/
theorem eventually_selectedUniformGoodHeight_nonneg_le_polynomial
    {alpha : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      0 ≤ selectedUniformGoodHeight alpha selection x ∧
      selectedUniformGoodHeight alpha selection x ≤
        carlsonPolynomialHeight alpha x := by
  have hpow :=
    (tendsto_rpow_atTop halpha).eventually
      (eventually_ge_atTop (9 : ℝ))
  filter_upwards [hpow] with x hx
  have hbase : 8 ≤ x ^ alpha - 1 := by linarith
  have hmem := selection.height_mem (x ^ alpha - 1) hbase
  constructor
  · unfold selectedUniformGoodHeight
    linarith [hmem.1]
  · unfold selectedUniformGoodHeight carlsonPolynomialHeight
    linarith [hmem.2]

/-- Automatic natural-point lower transfer using the two-height selected
zero tail and the uniform good-height remainder certificate. -/
theorem automaticGoodHeight_twoHeight_naturalPointLowerTransfer
    {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hbeta : 0 < beta)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
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
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset
          (selectedUniformGoodHeight alpha selection x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ))
        (fun m : ℕ =>
          targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg :
      ∀ᶠ x : ℝ in atTop,
        0 ≤ selectedUniformGoodHeight alpha selection x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        selectedUniformGoodHeight alpha selection x ≤
          carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  have hcomplement :=
    selectedSignedOutsideClusterComplement_targetAmplitudeNegligible
      hS hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh
      hHnonneg hHle hcap hreal
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
      hmain
  intro m
  exact
    relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
      (selectedUniformGoodHeight alpha selection) S (m : ℝ)

/-- Automatic-good-height unified output: fixed-rate natural-point PNT
convergence together with the natural-witness oscillation transfer. -/
theorem unified_automaticGoodHeight_twoHeight_naturalTargetTransfer
    {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hbeta : 0 < beta)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
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
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset
          (selectedUniformGoodHeight alpha selection x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ))
        (fun m : ℕ =>
          targetZeroPowerAmplitude beta (m : ℝ))) :
    (∃ rate : ℝ,
        0 < rate ∧ rate ≤ 1 ∧
        Tendsto
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          atTop (nhds 0)) ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x => targetZeroPowerAmplitude beta x / 2) := by
  exact
    ⟨exists_fixedRate_relativeChebyshevPsi0Error_tendsto,
      automaticGoodHeight_twoHeight_naturalPointLowerTransfer
        hbeta halphaOne hcontourMargin selection hS
        hsigma hsigmaOne halpha hgammaLow hepsilonLow
        hlowLow hlowHigh hgammaHigh hgammaHighAlpha
        hepsilonHigh hstripLow hstripHigh hcap hreal hmain⟩

end PrimeNumberTheorem
