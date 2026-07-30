import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetAmplitudeFullTailConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPolynomialRemainderCriterion
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterComplementUnifiedTransfer

/-!
# Actual explicit-formula unified target-amplitude transfer

This module inserts the concrete two-height full zero-tail estimate into the
actual explicit-formula decomposition and the abstract unified PNT
upper/lower transfer.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Eventual positivity of the target-zero power amplitude. -/
theorem eventually_targetZeroPowerAmplitude_pos (beta : ℝ) :
    ∀ᶠ x : ℝ in atTop, 0 < targetZeroPowerAmplitude beta x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa [targetZeroPowerAmplitude] using
    (Real.rpow_pos_of_pos hx (beta - 1))

/-- Stack39 full-tail decay transfers to the signed outside-cluster
complement occurring in the exact explicit formula. -/
theorem actualSignedOutsideClusterComplement_targetAmplitudeNegligible
    {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow :
      gammaLow + sigma - beta + epsilonLow < 0)
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
          (carlsonPolynomialHeight alpha x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicOutsideClusterPNTComplement
        (carlsonPolynomialHeight alpha) S) := by
  have hfull :=
    actualFullOutsideClusterTail_targetAmplitudeNegligible
      hS hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hcap hreal
  apply TargetAmplitudeNegligible.of_eventually_abs_le
    (eventually_targetZeroPowerAmplitude_pos beta) hfull
  filter_upwards with x
  exact
    abs_dynamicOutsideClusterPNTComplement_le_tailNorm
      (carlsonPolynomialHeight alpha) S x

/-- All non-main terms in the actual explicit formula are negligible on the
target-zero scale. -/
theorem actualExplicitFormulaResidual_targetAmplitudeNegligible
    {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hbeta : 0 < beta)
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow :
      gammaLow + sigma - beta + epsilonLow < 0)
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
          (carlsonPolynomialHeight alpha x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (remainderCertificate :
      ActualPolynomialExplicitFormulaRemainderCertificate alpha)
    (hcontourMargin : 1 - beta < alpha) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        actualPNTClosedRealAxisRelativeTerm x +
          actualPNTExplicitFormulaRelativeRemainder
              (carlsonPolynomialHeight alpha) x +
          dynamicOutsideClusterPNTComplement
              (carlsonPolynomialHeight alpha) S x) := by
  have hamplitude := eventually_targetZeroPowerAmplitude_pos beta
  have hclosed :=
    actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta
  have hremainder :=
    remainderCertificate.targetAmplitudeNegligible hcontourMargin
  have hcomplement :=
    actualSignedOutsideClusterComplement_targetAmplitudeNegligible
      hS hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hcap hreal
  exact (hclosed.add hamplitude hremainder).add hamplitude hcomplement

/-- Concrete unified transfer for the actual zeta explicit formula.

The conclusion contains both a fixed-rate natural-point PNT upper result and
a target-amplitude lower witness for the same relative PNT error. -/
theorem unified_actualExplicitFormula_targetAmplitudeTransfer
    {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
    (hbeta : 0 < beta)
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow :
      gammaLow + sigma - beta + epsilonLow < 0)
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
          (carlsonPolynomialHeight alpha x) S →
        sigma < rho.re → rho.re ≤ tau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (remainderCertificate :
      ActualPolynomialExplicitFormulaRemainderCertificate alpha)
    (hcontourMargin : 1 - beta < alpha)
    (hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain
          (carlsonPolynomialHeight alpha) S)
        (targetZeroPowerAmplitude beta)) :
    (∃ rate : ℝ,
        0 < rate ∧ rate ≤ 1 ∧
        Tendsto
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          atTop (nhds 0)) ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hclosed :=
    actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta
  have hremainder :=
    remainderCertificate.targetAmplitudeNegligible hcontourMargin
  have hcomplement :=
    actualSignedOutsideClusterComplement_targetAmplitudeNegligible
      hS hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hcap hreal
  exact
    unified_parametricPNTUpper_targetAmplitudeLower
      sigma hsigma hsigmaOne
      (eventually_targetZeroPowerAmplitude_pos beta)
      hclosed hremainder hcomplement hmain
      (relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
        (carlsonPolynomialHeight alpha) S)

end PrimeNumberTheorem
