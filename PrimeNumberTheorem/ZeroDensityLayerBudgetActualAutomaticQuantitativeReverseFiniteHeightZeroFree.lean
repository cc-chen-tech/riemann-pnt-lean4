import PrimeNumberTheorem.ZeroDensityLayerBudgetActualGlobalRealPartBoundUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSignedReverseZeroFree

/-!
# Quantitative automatic reverse finite-height zero-free transfer

The automatic forward transfer preserves one half of a unit target-amplitude
cluster witness.  Consequently every eventual actual-error coefficient
strictly below `1 / 2` excludes a nonempty right-edge cluster.
-/

namespace PrimeNumberTheorem

open Filter

/-- An eventual real upper bound with coefficient `q` excludes every far
witness with a strictly larger coefficient `d`, provided the amplitude is
eventually positive. -/
theorem not_hasFarTargetAmplitude_mul_of_eventually_abs_le_mul
    {amplitude remainder : ℝ → ℝ}
    {q d : ℝ}
    (hupper :
      ∀ᶠ x : ℝ in atTop,
        |remainder x| ≤ q * amplitude x)
    (hamplitude : ∀ᶠ x : ℝ in atTop, 0 < amplitude x)
    (hqd : q < d) :
    ¬ HasFarTargetAmplitudeWitness
        remainder (fun x => d * amplitude x) := by
  intro hfar
  have hbound :
      ∀ᶠ x : ℝ in atTop,
        |remainder x| ≤ q * amplitude x ∧
          0 < amplitude x :=
    hupper.and hamplitude
  obtain ⟨X, hX⟩ := eventually_atTop.mp hbound
  obtain ⟨x, hx, hlower⟩ := hfar X
  have hxBound := hX x hx
  have hstrict :
      q * amplitude x < d * amplitude x :=
    mul_lt_mul_of_pos_right hqd hxBound.2
  exact
    (not_lt_of_ge hlower)
      (hxBound.1.trans_lt hstrict)

/-- An eventual actual relative PNT-error coefficient `q < 1 / 2` yields
finite-height right-edge zero freedom through the fully automatic numerical
and complementary-tail transfer stack.

The remaining sharp input is the unit target-amplitude witness for every
nonempty real-ordinate enlargement of the right-edge cluster. -/
theorem
    exists_automaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree
    {beta theta H q : ℝ}
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (htheta : theta < (3 * beta - 1) / 2)
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
      exists_automaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
        (S := rightEdgeNontrivialZerosFinset beta H)
        hbeta hbetaOne htheta
        (rightEdgeNontrivialZerosFinset_conjugationInvariant beta H)
        hzeroBound with
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
