import PrimeNumberTheorem.ZeroDensityLayerBudgetActualGlobalRealPartBoundUnifiedTransfer

/-!
# Automatic reverse cluster exclusion

The global-real-part-bound forward transfer supplies an actual PNT-error far
witness from every visible-cluster witness.  Target-scale negligibility of the
same PNT error excludes that conclusion, yielding a reverse cluster-exclusion
theorem with all numerical and complementary-tail inputs automated.
-/

namespace PrimeNumberTheorem

open Filter

/-- A function negligible relative to an eventually positive real amplitude
cannot have a positive-proportion far witness at that amplitude. -/
theorem TargetAmplitudeNegligible.not_hasFar_mul
    {amplitude remainder : ℝ → ℝ}
    (hnegligible : TargetAmplitudeNegligible amplitude remainder)
    (hamplitude : ∀ᶠ x : ℝ in atTop, 0 < amplitude x)
    {c : ℝ} (hc : 0 < c) :
    ¬ HasFarTargetAmplitudeWitness
        remainder (fun x => c * amplitude x) := by
  intro hfar
  have hsmall :=
    eventually_abs_lt_mul_of_targetAmplitudeNegligible
      hamplitude hnegligible hc
  obtain ⟨X, hX⟩ := eventually_atTop.mp hsmall
  obtain ⟨x, hx, hlower⟩ := hfar X
  exact (not_lt_of_ge hlower) (hX x hx)

/-- Under a global real-part bound, target-scale negligibility of the actual
relative PNT error forces the enlarged visible cluster to be empty whenever a
nonempty cluster would supply the natural-point target-amplitude witness.

All numerical margins, the selected height, the Carlson strip cap, and the
real-ordinate residual are discharged by the preceding automatic transfer
stack. -/
theorem
    exists_automaticGoodHeight_globalRealPartBound_reverseClusterExclusion
    {S : Finset ℂ} {beta theta : ℝ}
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (htheta : theta < (3 * beta - 1) / 2)
    (hS : IsConjugationInvariantCluster S)
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
        ((actualCarlsonAdjoinRealOrdinateZeros S).Nonempty →
          HasFarNaturalPointTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection)
                (actualCarlsonAdjoinRealOrdinateZeros S) (m : ℝ))
            (fun m => targetZeroPowerAmplitude beta (m : ℝ))) →
        actualCarlsonAdjoinRealOrdinateZeros S = ∅ := by
  rcases
      exists_automaticGoodHeight_globalRealPartBoundNaturalTargetTransfer
        hbeta hbetaOne htheta hS hzeroBound with
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, htransfer⟩
  refine
    ⟨sigma, tau, alpha,
      hsigmaHalf, hsigmaTau, hthetaTau, htauBeta,
      hcontour, halpha, halphaOne, ?_⟩
  intro selection hmain
  by_contra hnotEmpty
  have hnonempty :
      (actualCarlsonAdjoinRealOrdinateZeros S).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hnotEmpty
  have hfar :=
    (htransfer selection (hmain hnonempty)).2
  have hnotFar :=
    herror.not_hasFar_mul
      (targetZeroPowerAmplitude_eventually_pos beta)
      (c := (1 / 2 : ℝ)) (by norm_num)
  apply hnotFar
  simpa [div_eq_mul_inv, mul_comm] using hfar

end PrimeNumberTheorem

