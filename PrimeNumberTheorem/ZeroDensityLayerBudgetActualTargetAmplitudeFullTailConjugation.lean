import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetAmplitudePositiveTailComposition
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailExcludingClusterConjugation

/-!
# Actual target-amplitude full outside-cluster zero tail

This module combines the concrete positive-tail theorem with the existing
conjugation transfer and real-ordinate residual estimate.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Complete finite outside-cluster zero tail divided by the target-zero
power amplitude. -/
noncomputable def actualFullOutsideClusterTailTargetAmplitudeNorm
    (beta alpha : ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  dynamicFullOutsideClusterPNTZeroTailNorm
      (carlsonPolynomialHeight alpha) S x /
    targetZeroPowerAmplitude beta x

/-- The stack38 positive-tail limit in the abstract negligibility form used
by the conjugation transfer. -/
theorem actualPositiveOutsideClusterTail_targetAmplitudeNegligible
    {S : Finset ℂ}
    {beta sigma tau alpha gammaLow epsilonLow
      gammaHigh epsilonHigh : ℝ}
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
        sigma < rho.re → rho.re ≤ tau) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  have h :=
    tendsto_actualPositiveOutsideClusterTailTargetAmplitudeNorm
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hcap
  unfold TargetAmplitudeNegligible
  simpa [actualPositiveOutsideClusterTailTargetAmplitudeNorm,
    dynamicPositiveOutsideClusterPNTTailNorm] using h

/-- Under conjugation invariance and the strict real-ordinate residual
condition, the complete actual outside-cluster zero tail is negligible on
the target-zero scale. -/
theorem actualFullOutsideClusterTail_targetAmplitudeNegligible
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
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  have hamplitude :
      ∀ᶠ x : ℝ in atTop, 0 < targetZeroPowerAmplitude beta x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [targetZeroPowerAmplitude] using
      (Real.rpow_pos_of_pos hx (beta - 1))
  have hpositive :=
    actualPositiveOutsideClusterTail_targetAmplitudeNegligible
      hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hcap
  have hrealNegligible :=
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_carlsonPolynomial_negligible
      (alpha := alpha) hreal
  exact
    dynamicFullOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      hS hamplitude hpositive hrealNegligible

/-- Direct limit form of the complete actual outside-cluster zero-tail
theorem. -/
theorem tendsto_actualFullOutsideClusterTailTargetAmplitudeNorm
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
    Tendsto
      (actualFullOutsideClusterTailTargetAmplitudeNorm
        beta alpha S)
      atTop (nhds 0) := by
  have h :=
    actualFullOutsideClusterTail_targetAmplitudeNegligible
      hS hsigma hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHigh hgammaHighAlpha
      hepsilonHigh hstripLow hstripHigh hcap hreal
  unfold TargetAmplitudeNegligible at h
  simpa [actualFullOutsideClusterTailTargetAmplitudeNorm,
    dynamicFullOutsideClusterPNTZeroTailNorm] using h

end PrimeNumberTheorem
