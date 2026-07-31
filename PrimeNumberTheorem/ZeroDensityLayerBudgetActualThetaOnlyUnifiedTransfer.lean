import PrimeNumberTheorem.ZeroDensityLayerBudgetActualImprovedCapAutomaticTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightCanonicalStrictTargetExponent

/-!
# Theta-only actual unified transfer

A prescribed global positive-zero real-part cap is now the only numerical
input.  The target exponent, density threshold, strip endpoint, outer height,
and all strict losses are selected automatically and returned for audit.
-/

namespace PrimeNumberTheorem

open Filter

/-- Given only a global cap `1 / 2 < theta < 1`, the system selects a
canonical strict target exponent and all globally optimized truncation
parameters, then runs the actual Pintz-Carlson-explicit-formula transfer.

The remaining lower-direction input is the visible-cluster natural-point
witness at the automatically selected target exponent. -/
theorem
    exists_thetaOnlyAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
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
      beta = jointTwoHeightCanonicalStrictTargetExponent theta ∧
      2 / 3 < betaBoundary ∧
      betaBoundary < beta ∧
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
  let beta := jointTwoHeightCanonicalStrictTargetExponent theta
  rcases
      jointTwoHeightCanonicalStrictTargetExponent_spec
        hthetaHalf hthetaOne with
    ⟨hboundaryLower, hboundaryBeta, hbetaOne, hbetaLower,
      hthetaBoundary, hthetaBeta, hboundaryEq, hthetaImproved⟩
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
      hboundaryLower, hboundaryBeta, hbetaOne,
      hthetaBoundary, hboundaryEq, hthetaImproved,
      hetaPos, hetaGap,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩

end PrimeNumberTheorem
