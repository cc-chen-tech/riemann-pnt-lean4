import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStripBottleneck

/-!
# An explicit balanced selected-height exponent

For one endpoint-aware Carlson strip, the polynomial exponent must satisfy

`alpha < (beta - tau) / (4 * sigma * (1 - sigma))`.

For a nonempty finite strip family, the common upper ceiling is the minimum of
these quantities.  This module replaces the opaque feasible exponent selected
by `Classical.choose` with the explicit midpoint between the contour lower
transition `1 - beta` and the effective upper ceiling, capped by `1`.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- The largest polynomial height exponent allowed by one Carlson strip. -/
noncomputable def actualSelectedHeightStripAlphaCeiling
    (beta sigma tau : ℝ) : ℝ :=
  (beta - tau) / (4 * sigma * (1 - sigma))

/-- The contour transition lies below one strip's alpha ceiling exactly when
the target real part clears that strip's endpoint threshold. -/
theorem contourTransition_lt_stripAlphaCeiling_iff
    {beta sigma tau : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    1 - beta < actualSelectedHeightStripAlphaCeiling beta sigma tau ↔
      carlsonStripEndpointTargetThreshold sigma tau < beta := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    simpa [q, mul_assoc] using
      carlsonClassicalDensitySlope_pos hsigma hsigmaOne
  have hden : 0 < 1 + q := by linarith
  constructor
  · intro hceiling
    have hwindow : (1 - beta) * q < beta - tau := by
      apply (lt_div_iff₀ hq).1
      simpa [actualSelectedHeightStripAlphaCeiling, q] using hceiling
    dsimp [carlsonStripEndpointTargetThreshold]
    rw [div_lt_iff₀ hden]
    dsimp [q] at hwindow ⊢
    nlinarith
  · intro hthreshold
    have hwindow : (1 - beta) * q < beta - tau := by
      dsimp [carlsonStripEndpointTargetThreshold] at hthreshold
      rw [div_lt_iff₀ hden] at hthreshold
      dsimp [q] at hthreshold ⊢
      nlinarith
    apply (lt_div_iff₀ hq).2
    simpa [actualSelectedHeightStripAlphaCeiling, q] using hwindow

/-- A strip's target-normalized Carlson exponent is negative exactly below its
alpha ceiling. -/
theorem stripEndpointExponent_neg_iff_lt_alphaCeiling
    {beta sigma tau alpha : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0 ↔
      alpha < actualSelectedHeightStripAlphaCeiling beta sigma tau := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    simpa [q, mul_assoc] using
      carlsonClassicalDensitySlope_pos hsigma hsigmaOne
  constructor
  · intro hdecay
    have hwindow : alpha * q < beta - tau := by
      simp only [targetAmplitudeStripEndpointExponent,
        carlsonClassicalPolynomialDensityExponent,
        carlsonPolynomialHeightDensityExponent] at hdecay
      dsimp [q] at hdecay ⊢
      nlinarith
    have hquotient : alpha < (beta - tau) / q :=
      (lt_div_iff₀ hq).2 hwindow
    simpa [actualSelectedHeightStripAlphaCeiling, q] using hquotient
  · intro hceiling
    have hquotient : alpha < (beta - tau) / q := by
      simpa [actualSelectedHeightStripAlphaCeiling, q] using hceiling
    have hwindow : alpha * q < beta - tau :=
      (lt_div_iff₀ hq).1 hquotient
    simp only [targetAmplitudeStripEndpointExponent,
      carlsonClassicalPolynomialDensityExponent,
      carlsonPolynomialHeightDensityExponent]
    dsimp [q] at hwindow ⊢
    nlinarith

/-- The common alpha ceiling of a nonempty finite strip family. -/
noncomputable def actualSelectedHeightFiniteStripAlphaCeiling
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  let ceilings :=
    Finset.univ.image fun i =>
      actualSelectedHeightStripAlphaCeiling beta (sigma i) (tau i)
  ceilings.min' (Finset.univ_nonempty.image _)

/-- The contour transition clears the common alpha ceiling exactly when every
strip endpoint threshold clears the target. -/
theorem contourTransition_lt_finiteStripAlphaCeiling_iff
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    1 - beta <
        actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau ↔
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta := by
  let ceilings :=
    Finset.univ.image fun i =>
      actualSelectedHeightStripAlphaCeiling beta (sigma i) (tau i)
  change 1 - beta < ceilings.min' (Finset.univ_nonempty.image _) ↔ _
  rw [Finset.lt_min'_iff]
  constructor
  · intro h i
    apply
      (contourTransition_lt_stripAlphaCeiling_iff
        (hsigma i) (hsigmaOne i)).1
    exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro h value hvalue
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvalue
    exact
      (contourTransition_lt_stripAlphaCeiling_iff
        (hsigma i) (hsigmaOne i)).2 (h i)

/-- Being below the common alpha ceiling is equivalent to simultaneous
negative Carlson exponents for all strips. -/
theorem lt_finiteStripAlphaCeiling_iff_all_exponents_neg
    {beta alpha : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    alpha < actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau ↔
      ∀ i,
        targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) <
            0 := by
  let ceilings :=
    Finset.univ.image fun i =>
      actualSelectedHeightStripAlphaCeiling beta (sigma i) (tau i)
  change alpha < ceilings.min' (Finset.univ_nonempty.image _) ↔ _
  rw [Finset.lt_min'_iff]
  constructor
  · intro h i
    apply
      (stripEndpointExponent_neg_iff_lt_alphaCeiling
        (hsigma i) (hsigmaOne i)).2
    exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro h value hvalue
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvalue
    exact
      (stripEndpointExponent_neg_iff_lt_alphaCeiling
        (hsigma i) (hsigmaOne i)).1 (h i)

/-- Explicit robust exponent: the midpoint between the contour transition and
the effective finite-strip upper ceiling, capped by `1`. -/
noncomputable def actualSelectedHeightFiniteStripBalancedExponent
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  ((1 - beta) +
      min 1 (actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau)) / 2

/-- The explicit balanced exponent satisfies every condition required by the
actual selected-height remainder and every finite Carlson strip.  It also has
equal distance to the contour transition and the effective upper ceiling. -/
theorem actualSelectedHeightFiniteStripBalancedExponent_spec
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) :
    0 <
        actualSelectedHeightFiniteStripBalancedExponent beta sigma tau ∧
      actualSelectedHeightFiniteStripBalancedExponent beta sigma tau < 1 ∧
      1 - beta <
        actualSelectedHeightFiniteStripBalancedExponent beta sigma tau ∧
      actualSelectedHeightFiniteStripBalancedExponent beta sigma tau <
        actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau ∧
      (∀ i,
        targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent
            (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau)
            (sigma i)) < 0) ∧
      actualSelectedHeightFiniteStripBalancedExponent beta sigma tau -
          (1 - beta) =
        min 1
            (actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau) -
          actualSelectedHeightFiniteStripBalancedExponent beta sigma tau := by
  have hfinite :
      1 - beta <
        actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau :=
    (contourTransition_lt_finiteStripAlphaCeiling_iff
      sigma tau hsigma hsigmaOne).2 hthreshold
  have hlowerOne : 1 - beta < 1 := by linarith
  have hlowerUpper :
      1 - beta <
        min 1
          (actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau) :=
    lt_min hlowerOne hfinite
  let alpha :=
    actualSelectedHeightFiniteStripBalancedExponent beta sigma tau
  have hLowerAlpha : 1 - beta < alpha := by
    dsimp [alpha, actualSelectedHeightFiniteStripBalancedExponent]
    linarith
  have hAlphaUpper :
      alpha <
        min 1
          (actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau) := by
    dsimp [alpha, actualSelectedHeightFiniteStripBalancedExponent]
    linarith
  have hAlphaOne : alpha < 1 :=
    hAlphaUpper.trans_le (min_le_left _ _)
  have hAlphaFinite :
      alpha <
        actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau :=
    hAlphaUpper.trans_le (min_le_right _ _)
  have hAlphaPos : 0 < alpha := by
    have hLowerPos : 0 < 1 - beta := by linarith
    exact hLowerPos.trans hLowerAlpha
  refine ⟨hAlphaPos, hAlphaOne, hLowerAlpha, hAlphaFinite,
    (lt_finiteStripAlphaCeiling_iff_all_exponents_neg
      sigma tau hsigma hsigmaOne).1 hAlphaFinite, ?_⟩
  dsimp [alpha, actualSelectedHeightFiniteStripBalancedExponent]
  ring

end PrimeNumberTheorem
