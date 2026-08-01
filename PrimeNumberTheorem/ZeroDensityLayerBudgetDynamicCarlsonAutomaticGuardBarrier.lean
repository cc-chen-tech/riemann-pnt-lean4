import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonAutomaticGuardPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicTailInconsistency

/-!
# Noninhabitation barrier for the automatic all-Carlson PNT input

The automatic-guard PNT transfer still asks a finite family of Carlson strips,
all with lower endpoint strictly greater than `1 / 2`, to contain every
positive-height zero below a cofinal sequence of truncation heights.

This input is unconditionally impossible.  It would force every
positive-ordinate nontrivial zero strictly to the right of the critical line.
Applying that conclusion to one zero and its critical-line reflection gives a
contradiction.

This is an audit theorem.  It does not construct the deliberately deferred
critical-half decomposition, and therefore it does not turn the conditional
automatic-guard transfer into an unconditional PNT proof.
-/

open Filter

noncomputable section

namespace PrimeNumberTheorem

/-- Every zero in a positive bucket whose lower thresholds exceed `1 / 2`
lies strictly to the right of the critical line. -/
theorem PositiveZeroBucketInput.half_lt_re_of_sigma_half
    {T : ℝ} {n : ℕ}
    (input : PositiveZeroBucketInput T n)
    (hsigma : ∀ i, 1 / 2 < input.sigma i)
    {rho : ℂ}
    (hrho : rho ∈ positiveNontrivialZerosFinset T) :
    1 / 2 < rho.re :=
  (hsigma (input.bucket rho)).trans
    (input.sigma_lt_re rho hrho)

/-- A cofinal automatic-target bucket family with all fixed strip thresholds
above `1 / 2` would force every positive-height nontrivial zero strictly to
the right of the critical line. -/
theorem
    dynamicCarlsonAutomaticGuardInput_positiveZeros_strictlyRightOfHalf
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            (dynamicCarlsonAutomaticTargetBeta sigma tau)
            sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i) :
    PositiveNontrivialZerosStrictlyRightOfHalf := by
  intro rho hzero him
  have hheight :
      Tendsto
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          (dynamicCarlsonAutomaticTargetBeta sigma tau)
          sigma tau selection)
        atTop atTop :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_tendsto_atTop
      sigma tau
      (dynamicCarlsonAutomaticTargetBeta_lt_one
        sigma tau hthresholdOne)
      hsigma hsigmaOne htau
      (carlsonStripEndpointTargetThreshold_lt_automaticTargetBeta
        sigma tau hthresholdOne)
      selection
  have heventuallyHeight :
      ∀ᶠ y : ℝ in atTop,
        rho.im ≤
          actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            (dynamicCarlsonAutomaticTargetBeta sigma tau)
            sigma tau selection y :=
    (tendsto_atTop.1 hheight) rho.im
  rcases heventuallyHeight.exists with ⟨y, himHeight⟩
  have hrho :
      rho ∈
        positiveNontrivialZerosFinset
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            (dynamicCarlsonAutomaticTargetBeta sigma tau)
            sigma tau selection y) :=
    mem_positiveNontrivialZerosFinset.mpr
      ⟨hzero, him, himHeight⟩
  apply (input y).half_lt_re_of_sigma_half
  · intro i
    rw [hfixedSigma i y]
    exact hsigma i
  · exact hrho

/-- The complete positive-zero bucket family required by the automatic
all-Carlson PNT transfer is unconditionally uninhabited. -/
theorem
    not_exists_dynamicCarlsonAutomaticGuardPositiveZeroBucketInput
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ¬ ∃ input :
        (x : ℝ) →
          PositiveZeroBucketInput
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              (dynamicCarlsonAutomaticTargetBeta sigma tau)
              sigma tau selection x)
            (n + 1),
        ∀ i x, (input x).sigma i = sigma i := by
  rintro ⟨input, hfixedSigma⟩
  have hright :
      PositiveNontrivialZerosStrictlyRightOfHalf :=
    dynamicCarlsonAutomaticGuardInput_positiveZeros_strictlyRightOfHalf
      sigma tau hsigma hsigmaOne htau hthresholdOne
      selection input hfixedSigma
  obtain ⟨rho, hzero, him⟩ :=
    exists_positiveOrdinate_nontrivialZero
  have hrhoRight : 1 / 2 < rho.re :=
    hright rho hzero him
  let reflected :=
    RiemannVonMangoldt.criticalLineReflection rho
  have hreflectedZero :
      RiemannHypothesis.IsNontrivialZero reflected :=
    RiemannVonMangoldt.isNontrivialZero_criticalLineReflection hzero
  have hreflectedIm : 0 < reflected.im := by
    simpa [reflected] using him
  have hreflectedRight : 1 / 2 < reflected.re :=
    hright reflected hreflectedZero hreflectedIm
  have hreflectedRe : reflected.re = 1 - rho.re := by
    simp [reflected, RiemannVonMangoldt.criticalLineReflection]
  rw [hreflectedRe] at hreflectedRight
  linarith

end PrimeNumberTheorem
