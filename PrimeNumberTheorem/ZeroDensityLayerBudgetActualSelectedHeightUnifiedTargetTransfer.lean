import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightTwoHeightFullTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterComplementUnifiedTransfer

/-!
# Selected-height unified explicit-formula target transfer

This module combines the selected-height two-height full zero tail with an
actual selected-height explicit-formula remainder certificate.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Selected full-tail decay controls the signed complement in the exact
explicit formula. -/
theorem selectedSignedOutsideClusterComplement_targetAmplitudeNegligible
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
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
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicOutsideClusterPNTComplement H S) := by
  have hfull :=
    selectedFullOutsideClusterTail_targetAmplitudeNegligible
      hS hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHnonneg hHle hcap hreal
  have hamplitude :
      ∀ᶠ x : ℝ in atTop, 0 < targetZeroPowerAmplitude beta x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [targetZeroPowerAmplitude] using
      (Real.rpow_pos_of_pos hx (beta - 1))
  apply TargetAmplitudeNegligible.of_eventually_abs_le
    hamplitude hfull
  filter_upwards with x
  exact abs_dynamicOutsideClusterPNTComplement_le_tailNorm H S x

/-- Complete selected-height explicit-formula residual negligibility. -/
theorem selectedExplicitFormulaResidual_targetAmplitudeNegligible
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hbeta : 0 < beta)
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
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (remainderCertificate :
      ActualSelectedHeightExplicitFormulaRemainderCertificate alpha H)
    (hcontourMargin : 1 - beta < alpha) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        actualPNTClosedRealAxisRelativeTerm x +
          actualPNTExplicitFormulaRelativeRemainder H x +
          dynamicOutsideClusterPNTComplement H S x) := by
  have hamplitude :
      ∀ᶠ x : ℝ in atTop, 0 < targetZeroPowerAmplitude beta x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [targetZeroPowerAmplitude] using
      (Real.rpow_pos_of_pos hx (beta - 1))
  have hclosed :=
    actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta
  have hremainder :=
    remainderCertificate.targetAmplitudeNegligible hcontourMargin
  have hcomplement :=
    selectedSignedOutsideClusterComplement_targetAmplitudeNegligible
      hS hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHnonneg hHle hcap hreal
  exact (hclosed.add hamplitude hremainder).add hamplitude hcomplement

/-- Selected-height concrete unified transfer for the actual zeta explicit
formula. -/
theorem unified_actualSelectedHeightExplicitFormula_targetAmplitudeTransfer
    {H : ℝ → ℝ} {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hbeta : 0 < beta)
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
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (remainderCertificate :
      ActualSelectedHeightExplicitFormulaRemainderCertificate alpha H)
    (hcontourMargin : 1 - beta < alpha)
    (hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain H S)
        (targetZeroPowerAmplitude beta)) :
    (∃ rate : ℝ,
        0 < rate ∧ rate ≤ 1 ∧
        Tendsto
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          atTop (nhds 0)) ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hamplitude :
      ∀ᶠ x : ℝ in atTop, 0 < targetZeroPowerAmplitude beta x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [targetZeroPowerAmplitude] using
      (Real.rpow_pos_of_pos hx (beta - 1))
  have hclosed :=
    actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta
  have hremainder :=
    remainderCertificate.targetAmplitudeNegligible hcontourMargin
  have hcomplement :=
    selectedSignedOutsideClusterComplement_targetAmplitudeNegligible
      hS hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hHnonneg hHle hcap hreal
  exact
    unified_parametricPNTUpper_targetAmplitudeLower
      sigma hsigma hsigmaOne hamplitude
      hclosed hremainder hcomplement hmain
      (relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
        H S)

end PrimeNumberTheorem
