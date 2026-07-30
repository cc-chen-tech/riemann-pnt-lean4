import PrimeNumberTheorem.ZeroDensityLayerBudgetActualGlobalOptimalUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightImprovedGlobalCapThreshold

/-!
# Automatic actual transfer below the improved cap threshold

The exact improved cap criterion automatically supplies a positive global
contour gap.  Choosing a strict loss inside that gap yields the actual
globally optimized Pintz-Carlson-explicit-formula transfer.
-/

namespace PrimeNumberTheorem

open Filter

/-- A global positive-zero real-part cap below the improved threshold
automatically produces an actual PNT transfer at a globally optimized,
contour-compatible truncation height.

The sole remaining lower-direction input is the natural-point witness for the
enlarged visible cluster. -/
theorem
    exists_improvedCapAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
    {S : Finset ℂ} {beta theta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (htheta :
      theta < jointTwoHeightImprovedGlobalCapThreshold beta)
    (hS : IsConjugationInvariantCluster S)
    (hzeroBound :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ theta) :
    ∃ eta sigma tau alpha : ℝ,
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
  rcases
      exists_pos_lt_jointTwoHeightGlobalContourGap_of_lt_improvedThreshold
        hbeta hbetaOne hthetaHalf hthetaBeta htheta with
    ⟨eta, hetaPos, hetaGap⟩
  rcases
      exists_globallyNearOptimalAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
        (S := S)
        hbeta hbetaOne hthetaHalf hthetaBeta
        hetaPos hetaGap hS hzeroBound with
    ⟨sigma, tau, alpha,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩
  exact
    ⟨eta, sigma, tau, alpha,
      hetaPos, hetaGap,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩

end PrimeNumberTheorem
