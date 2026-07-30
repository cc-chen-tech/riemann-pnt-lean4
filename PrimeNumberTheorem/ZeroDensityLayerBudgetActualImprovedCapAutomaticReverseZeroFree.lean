import PrimeNumberTheorem.ZeroDensityLayerBudgetActualImprovedCapAutomaticTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticQuantitativeReverseFiniteHeightZeroFree

/-!
# Automatic reverse zero freedom below the improved cap

The improved real-part cap criterion automatically constructs the globally
optimized actual transfer.  An eventual coefficient below one half then
forces finite-height right-edge zero freedom, conditional only on the visible
cluster witness.
-/

namespace PrimeNumberTheorem

open Filter

/-- Below the improved global cap threshold, an eventual actual relative-error
coefficient `q < 1 / 2` automatically yields finite-height right-edge zero
freedom from the visible-cluster unit witness. -/
theorem
    exists_improvedCapAutomaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree
    {beta theta H q : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (htheta :
      theta < jointTwoHeightImprovedGlobalCapThreshold beta)
    (hqHalf : q < 1 / 2)
    (hzeroBound :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ theta)
    (hupper :
      ∀ᶠ x : ℝ in atTop,
        |relativeChebyshevPsi0Error x| ≤
          q * targetZeroPowerAmplitude beta x) :
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
        ((actualCarlsonAdjoinRealOrdinateZeros
            (rightEdgeNontrivialZerosFinset beta H)).Nonempty →
          HasFarNaturalPointTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection)
                (actualCarlsonAdjoinRealOrdinateZeros
                  (rightEdgeNontrivialZerosFinset beta H))
                (m : ℝ))
            (fun m => targetZeroPowerAmplitude beta (m : ℝ))) →
        FiniteHeightRightEdgeZeroFree beta H := by
  rcases
      exists_improvedCapAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
        (S := rightEdgeNontrivialZerosFinset beta H)
        hbeta hbetaOne hthetaHalf hthetaBeta htheta
        (rightEdgeNontrivialZerosFinset_conjugationInvariant beta H)
        hzeroBound with
    ⟨eta, sigma, tau, alpha,
      hetaPos, hetaGap,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩
  refine
    ⟨eta, sigma, tau, alpha,
      hetaPos, hetaGap,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, ?_⟩
  intro selection hmain
  have hadjoinedEmpty :
      actualCarlsonAdjoinRealOrdinateZeros
          (rightEdgeNontrivialZerosFinset beta H) = ∅ := by
    by_contra hnotEmpty
    have hnonempty :
        (actualCarlsonAdjoinRealOrdinateZeros
          (rightEdgeNontrivialZerosFinset beta H)).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hnotEmpty
    have hfar :=
      (htransfer selection (hmain hnonempty)).2
    have hnotFar :=
      not_hasFarTargetAmplitude_mul_of_eventually_abs_le_mul
        hupper
        (targetZeroPowerAmplitude_eventually_pos beta)
        hqHalf
    apply hnotFar
    simpa [div_eq_mul_inv, mul_comm] using hfar
  apply
    (rightEdgeNontrivialZerosFinset_eq_empty_iff_zeroFree
      beta H).mp
  ext rho
  constructor
  · intro hrho
    have hadjoined :
        rho ∈ actualCarlsonAdjoinRealOrdinateZeros
          (rightEdgeNontrivialZerosFinset beta H) := by
      unfold actualCarlsonAdjoinRealOrdinateZeros
      exact Finset.mem_union_left _ hrho
    rw [hadjoinedEmpty] at hadjoined
    simp at hadjoined
  · simp

end PrimeNumberTheorem
