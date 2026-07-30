import PrimeNumberTheorem.ZeroDensityLayerBudgetActualAutomaticReverseClusterExclusion
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSignedReverseZeroFree

/-!
# Automatic reverse transfer to finite-height zero-free regions

The automatic reverse cluster-exclusion theorem is specialized to the
concrete finite right-edge zeta-zero cluster.  Its emptiness has an existing
equivalent formulation as a finite-height zero-free region.
-/

namespace PrimeNumberTheorem

/-- Target-scale negligibility of the actual relative PNT error yields a
finite-height right-edge zero-free statement through the automatic
Pintz-Carlson-explicit-formula reverse chain.

The remaining sharp input is a natural-point witness for every nonempty
real-ordinate enlargement of the right-edge cluster. -/
theorem
    exists_automaticGoodHeight_globalRealPartBound_finiteHeightZeroFree
    {beta theta H : ℝ}
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (htheta : theta < (3 * beta - 1) / 2)
    (hzeroBound :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
        0 < rho.im →
        rho.re ≤ theta)
    (herror :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        relativeChebyshevPsi0Error) :
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
      exists_automaticGoodHeight_globalRealPartBound_reverseClusterExclusion
        hbeta hbetaOne htheta
        (rightEdgeNontrivialZerosFinset_conjugationInvariant beta H)
        hzeroBound herror with
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, hreverse⟩
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hmain
  have hadjoinedEmpty :=
    hreverse selection hmain
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
    simpa using hadjoined
  · simp

end PrimeNumberTheorem
