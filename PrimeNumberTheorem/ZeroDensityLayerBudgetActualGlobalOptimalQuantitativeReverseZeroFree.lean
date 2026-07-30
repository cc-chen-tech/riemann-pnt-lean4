import PrimeNumberTheorem.ZeroDensityLayerBudgetActualGlobalOptimalUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticQuantitativeReverseFiniteHeightZeroFree

/-!
# Globally optimal quantitative reverse zero-free transfer

An eventual actual relative-error coefficient below one half is incompatible
with the half-target-amplitude witness produced by the globally optimized
actual transfer.  Hence a conditional visible-cluster witness excludes every
finite-height right-edge zero.
-/

namespace PrimeNumberTheorem

open Filter

/-- At the globally optimized truncation height, an eventual actual relative
PNT-error coefficient `q < 1 / 2` forces finite-height right-edge zero freedom.

The remaining sharp input is the unit target-amplitude witness for every
nonempty real-ordinate enlargement of the right-edge cluster. -/
theorem
    exists_globallyNearOptimalAutomaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree
    {beta theta eta H q : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hetaPos : 0 < eta)
    (hetaGap :
      eta <
        jointTwoHeightGlobalOuterExponentCeiling beta theta -
          (1 - beta))
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
      exists_globallyNearOptimalAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
        (S := rightEdgeNontrivialZerosFinset beta H)
        hbeta hbetaOne hthetaHalf hthetaBeta
        hetaPos hetaGap
        (rightEdgeNontrivialZerosFinset_conjugationInvariant beta H)
        hzeroBound with
    ⟨sigma, tau, alpha,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩
  refine
    ⟨sigma, tau, alpha,
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
