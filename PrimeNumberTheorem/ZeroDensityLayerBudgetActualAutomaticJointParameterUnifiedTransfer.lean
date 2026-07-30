import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticGoodHeightNaturalUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility

/-!
# Automatic joint-parameter unified transfer

The preceding arithmetic theorem constructs one common parameter tuple for
the low global layer and the Carlson strip.  This file hides its balanced cuts
and strict margins behind the actual automatic-good-height unified transfer.

The public result exposes only `sigma`, `tau`, and `alpha`, because those are
the parameters occurring in the remaining honest analytic inputs.
-/

namespace PrimeNumberTheorem

open Filter

/-- If `2 / 3 < beta < 1`, there exist numerical parameters for which the
automatic-good-height unified transfer requires no externally supplied
strict-margin inequalities.

The remaining hypotheses are analytic rather than numerical: the selected
strip cap, the real-ordinate complementary bound, and the visible-cluster
natural-point witness. -/
theorem exists_automaticGoodHeight_jointParameterNaturalTargetTransfer
    {S : Finset ℂ} {beta : ℝ}
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        IsConjugationInvariantCluster S →
        (∀ (x : ℝ),
          ∀ rho ∈
            positiveNontrivialZerosOutsideClusterFinset
              (selectedUniformGoodHeight alpha selection x) S,
            sigma < rho.re → rho.re ≤ tau) →
        (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
          rho.re < beta) →
        HasFarNaturalPointTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection) S (m : ℝ))
            (fun m => targetZeroPowerAmplitude beta (m : ℝ)) →
        (∃ rate : ℝ,
            0 < rate ∧
            rate ≤ 1 ∧
            Tendsto
              (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (nhds 0)) ∧
          HasFarTargetAmplitudeWitness
            relativeChebyshevPsi0Error
            (fun x => targetZeroPowerAmplitude beta x / 2) := by
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters hbeta hbetaOne with
    ⟨sigma, tau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  have hbetaPos : 0 < beta := by
    linarith
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hS hcap hreal hmain
  exact
    unified_automaticGoodHeight_twoHeight_naturalTargetTransfer
      (S := S) (beta := beta)
      (sigma := sigma) (tau := tau) (alpha := alpha)
      (gammaLow := gammaLow) (epsilonLow := epsilonLow)
      (gammaHigh := gammaHigh) (epsilonHigh := epsilonHigh)
      hbetaPos halphaOne hcontour selection hS
      hsigmaHalf hsigmaOne halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le hepsilonHigh
      hstripLow hstripHigh hcap hreal hmain

end PrimeNumberTheorem

