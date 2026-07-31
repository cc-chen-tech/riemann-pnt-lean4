import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPositiveOutsideClusterCapUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticQuantitativeReverseFiniteHeightZeroFree

/-!
# Nonvacuous quantitative reverse transfer from an outside-cluster cap

The finite right-edge zero cluster is exempt from the positive real-part cap.
An eventual actual-error coefficient below one half then excludes that cluster
through the actual Pintz-Carlson-explicit-formula transfer.
-/

namespace PrimeNumberTheorem

open Filter

/-- A positive real-part cap only outside the finite right-edge cluster,
together with an eventual coefficient `q < 1 / 2`, forces finite-height
right-edge zero freedom.

Unlike the global-cap version, the cap hypothesis permits the target cluster
itself to contain zeros with `beta ≤ rho.re`. -/
theorem
    exists_automaticGoodHeight_positiveOutsideRightEdgeCap_eventualUpper_finiteHeightZeroFree
    {beta theta H q : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (htheta : theta < (3 * beta - 1) / 2)
    (hqHalf : q < 1 / 2)
    (hcap :
      PositiveOutsideClusterRealPartCap
        (rightEdgeNontrivialZerosFinset beta H) theta)
    (hupper :
      ∀ᶠ x : ℝ in atTop,
        |relativeChebyshevPsi0Error x| ≤
          q * targetZeroPowerAmplitude beta x) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧
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
      exists_automaticGoodHeight_positiveOutsideClusterRealPartCapNaturalTargetTransfer
        (S := rightEdgeNontrivialZerosFinset beta H)
        hbeta hbetaOne htheta
        (rightEdgeNontrivialZerosFinset_conjugationInvariant beta H)
        hcap with
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, htransfer⟩
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
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
