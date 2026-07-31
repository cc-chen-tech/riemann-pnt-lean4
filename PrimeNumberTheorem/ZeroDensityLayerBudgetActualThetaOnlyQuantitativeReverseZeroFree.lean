import PrimeNumberTheorem.ZeroDensityLayerBudgetActualThetaOnlyUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticQuantitativeReverseFiniteHeightZeroFree

/-!
# Theta-only quantitative reverse zero-free transfer

The theta-only automatic parameter chain is used in reverse.  An eventual
actual-error coefficient below one half, measured at the canonical target
exponent, forces finite-height right-edge zero freedom.
-/

namespace PrimeNumberTheorem

open Filter

/-- From a global cap `theta`, the system automatically selects the target and
truncation parameters. An eventual coefficient `q < 1 / 2` at that target
scale then excludes finite-height right-edge zeros, conditional only on the
visible-cluster witness. -/
theorem
    exists_thetaOnlyAutomaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree
    {theta H q : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1)
    (hqHalf : q < 1 / 2)
    (hzeroBound :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ theta)
    (hupper :
      ∀ᶠ x : ℝ in atTop,
        |relativeChebyshevPsi0Error x| ≤
          q *
            targetZeroPowerAmplitude
              (jointTwoHeightCanonicalStrictTargetExponent theta) x) :
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
  let beta := jointTwoHeightCanonicalStrictTargetExponent theta
  rcases
      exists_thetaOnlyAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
        (S := rightEdgeNontrivialZerosFinset beta H)
        hthetaHalf hthetaOne
        (rightEdgeNontrivialZerosFinset_conjugationInvariant beta H)
        hzeroBound with
    ⟨betaBoundary, beta', eta, sigma, tau, alpha,
      hboundaryEq, hbetaEq,
      hboundaryLower, hboundaryBeta, hbetaOne,
      hthetaBoundary, hthresholdBoundary, hthetaImproved,
      hetaPos, hetaGap,
      hsigmaEq, hoptimizer, halphaEq,
      hsigmaTau, hthetaTau, htauBeta,
      hcontour, halphaPos, halphaOne, htransfer⟩
  have hbetaPrime : beta' = beta := by
    simpa [beta] using hbetaEq
  subst beta'
  refine
    ⟨betaBoundary, beta, eta, sigma, tau, alpha,
      hboundaryEq, rfl,
      hboundaryLower, hboundaryBeta, hbetaOne,
      hthetaBoundary, hthresholdBoundary, hthetaImproved,
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
        (by simpa [beta] using hupper)
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
