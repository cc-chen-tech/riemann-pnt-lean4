import PrimeNumberTheorem.ZeroDensityLayerBudgetActualImprovedCapAutomaticTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightCubicStrictTargetExponent

/-!
# Cubic-strict theta-only actual unified transfer

The theta-only actual Pintz-Carlson-explicit-formula transfer is run at the
cubic-strict target exponent. This preserves cubic proximity to the prescribed
global cap while retaining all strict truncation margins.
-/

namespace PrimeNumberTheorem

open Filter

/-- Given only a global cap `1 / 2 < theta < 1`, select the cubic-strict target
exponent and all globally optimized truncation parameters, then run the actual
Pintz-Carlson-explicit-formula transfer.

The remaining lower-direction input is the visible-cluster natural-point
witness at the automatically selected cubic-strict exponent. -/
theorem
    exists_thetaOnlyCubicStrictAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
    {S : Finset ℂ} {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1)
    (hS : IsConjugationInvariantCluster S)
    (hzeroBound :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ theta) :
    ∃ betaBoundary beta eta sigma tau alpha : ℝ,
      betaBoundary = jointTwoHeightOptimalTargetExponent theta ∧
      beta = jointTwoHeightCubicStrictTargetExponent theta ∧
      2 / 3 < betaBoundary ∧
      betaBoundary < beta ∧
      beta < jointTwoHeightCanonicalStrictTargetExponent theta ∧
      beta < 1 ∧
      theta < betaBoundary ∧
      jointTwoHeightImprovedGlobalCapThreshold betaBoundary = theta ∧
      theta < jointTwoHeightImprovedGlobalCapThreshold beta ∧
      0 < eta ∧
      eta <
        jointTwoHeightGlobalOuterExponentCeiling beta theta -
          (1 - beta) ∧
      sigma = jointTwoHeightOptimalDensityThreshold beta theta ∧
      IsJointTwoHeightSigmaOptimizer beta theta sigma ∧
      alpha =
        jointTwoHeightGlobalOuterExponentCeiling beta theta - eta ∧
      sigma < tau ∧
      theta < tau ∧
      tau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection),
        HasFarNaturalPointTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection)
                (actualCarlsonAdjoinRealOrdinateZeros S) (m : ℝ))
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
  let betaBoundary := jointTwoHeightOptimalTargetExponent theta
  let beta := jointTwoHeightCubicStrictTargetExponent theta
  rcases
      jointTwoHeightCubicStrictTargetExponent_spec
        hthetaHalf hthetaOne with
    ⟨hboundaryLower, hboundaryBeta, hbetaMidpoint, hbetaOne,
      hbetaLower, hthetaBoundary, hthetaBeta,
      hboundaryEq, hthetaImproved⟩
  rcases
      exists_improvedCapAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
        (S := S)
        hbetaLower hbetaOne hthetaHalf hthetaBeta
        hthetaImproved hS hzeroBound with
    ⟨eta, sigma, tau, alpha,
      hetaPos, hetaGap,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩
  exact
    ⟨betaBoundary, beta, eta, sigma, tau, alpha,
      rfl, rfl,
      hboundaryLower, hboundaryBeta, hbetaMidpoint, hbetaOne,
      hthetaBoundary, hboundaryEq, hthetaImproved,
      hetaPos, hetaGap,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩

end PrimeNumberTheorem
