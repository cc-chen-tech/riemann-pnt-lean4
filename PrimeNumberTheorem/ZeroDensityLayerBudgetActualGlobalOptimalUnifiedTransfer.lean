import PrimeNumberTheorem.ZeroDensityLayerBudgetActualNearOptimalUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightGlobalOptimalTruncationParameters

/-!
# Globally optimal actual unified transfer

The actual selected-good-height Pintz-Carlson-explicit-formula transfer is run
at an outer-height exponent arbitrarily close to the global ceiling obtained
after optimizing both the strip endpoint and the density threshold.
-/

namespace PrimeNumberTheorem

open Filter

/-- Under a global positive-zero real-part cap, every positive loss below the
global contour gap gives an actual unified PNT transfer at
`alpha = globalCeiling - eta`.

The density threshold is the unique global optimizer. The only remaining
lower-direction input is the natural-point witness for the enlarged visible
cluster. -/
theorem
    exists_globallyNearOptimalAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
    {S : Finset ℂ} {beta theta eta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hetaPos : 0 < eta)
    (hetaGap :
      eta <
        jointTwoHeightGlobalOuterExponentCeiling beta theta -
          (1 - beta))
    (hS : IsConjugationInvariantCluster S)
    (hzeroBound :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ theta) :
    ∃ sigma tau alpha : ℝ,
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
  let sigma := jointTwoHeightOptimalDensityThreshold beta theta
  have hoptimizer :
      IsJointTwoHeightSigmaOptimizer beta theta sigma := by
    simpa [sigma] using
      jointTwoHeightOptimalDensityThreshold_spec
        hthetaHalf hthetaBeta hbetaOne
  rcases hoptimizer with
    ⟨hsigmaHalf, hsigmaTheta, hbalance⟩
  have hsigmaOne : sigma < 1 :=
    hsigmaTheta.trans (hthetaBeta.trans hbetaOne)
  have hetaGapFixed :
      eta <
        jointTwoHeightPrescribedCapOuterExponentCeiling
              beta sigma theta -
            (1 - beta) := by
    simpa [jointTwoHeightGlobalOuterExponentCeiling, sigma] using hetaGap
  rcases
      exists_nearOptimalAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
        (S := S) hbeta hbetaOne
        hsigmaHalf hsigmaOne
        hetaPos hetaGapFixed hS hzeroBound with
    ⟨tau, alpha, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩
  have halphaGlobal :
      alpha =
        jointTwoHeightGlobalOuterExponentCeiling beta theta - eta := by
    simpa [jointTwoHeightGlobalOuterExponentCeiling, sigma] using halphaEq
  exact
    ⟨sigma, tau, alpha, rfl,
      ⟨hsigmaHalf, hsigmaTheta, hbalance⟩,
      halphaGlobal, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩

end PrimeNumberTheorem
