import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeExponentCriterion
import PrimeNumberTheorem.CarlsonAsymptotic

/-!
# The target-amplitude region allowed by Carlson's classical exponent

The theorem `carlson_zeroDensity_isBigO` supplies the concrete height exponent
`4 * sigma * (1 - sigma)`.  At a polynomial truncation height `T = x^alpha`,
the resulting count exponent is `4 * alpha * sigma * (1 - sigma)`.

This file substitutes that exponent into the target-amplitude feasibility
criterion and solves the resulting inequality exactly.  The logarithmic fourth
power in Carlson's theorem is not discarded: the strict exponent margin proved
here is the input needed to absorb it in a subsequent analytic step.
-/

namespace PrimeNumberTheorem

/-- The density exponent contributed by Carlson's classical estimate after the
polynomial substitution `T = x^alpha`. -/
def carlsonClassicalPolynomialDensityExponent
    (alpha sigma : ℝ) : ℝ :=
  carlsonPolynomialHeightDensityExponent alpha (4 * sigma) sigma

/-- Boundary target real part above which one polynomial height can satisfy
both the target-amplitude contour condition and Carlson strip decay. -/
noncomputable def carlsonClassicalTargetThreshold (sigma : ℝ) : ℝ :=
  let q := 4 * sigma * (1 - sigma)
  (sigma + q) / (1 + q)

/-- Carlson's height slope is positive in the classical density range. -/
theorem carlsonClassicalDensitySlope_pos
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    0 < (4 * sigma) * (1 - sigma) := by
  have hsigmaPos : 0 < sigma := by linarith
  exact mul_pos (mul_pos (by norm_num) hsigmaPos)
    (sub_pos.mpr hsigmaOne)

/-- The target threshold is strictly to the right of the strip itself. -/
theorem sigma_lt_carlsonClassicalTargetThreshold
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    sigma < carlsonClassicalTargetThreshold sigma := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    dsimp [q]
    have hsigmaPos : 0 < sigma := by linarith
    exact mul_pos (mul_pos (by norm_num) hsigmaPos)
      (sub_pos.mpr hsigmaOne)
  have hden : 0 < 1 + q := by linarith
  dsimp [carlsonClassicalTargetThreshold]
  rw [lt_div_iff₀ hden]
  nlinarith [mul_pos hq (sub_pos.mpr hsigmaOne)]

/-- The target threshold remains strictly below `1`. -/
theorem carlsonClassicalTargetThreshold_lt_one
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    carlsonClassicalTargetThreshold sigma < 1 := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    dsimp [q]
    have hsigmaPos : 0 < sigma := by linarith
    exact mul_pos (mul_pos (by norm_num) hsigmaPos)
      (sub_pos.mpr hsigmaOne)
  have hden : 0 < 1 + q := by linarith
  dsimp [carlsonClassicalTargetThreshold]
  rw [div_lt_iff₀ hden]
  linarith

/-- Exact classification of the target real parts for which Carlson's classical
power exponent leaves a polynomial-height window. -/
theorem exists_carlsonPolynomialHeight_targetAmplitude_decay_iff
    {beta sigma : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) :
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        targetAmplitudePintzCarlsonExponent beta sigma
          (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0) ↔
      carlsonClassicalTargetThreshold sigma < beta := by
  have hslope :
      0 < (4 * sigma) * (1 - sigma) :=
    carlsonClassicalDensitySlope_pos hsigma hsigmaOne
  rw [show
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        targetAmplitudePintzCarlsonExponent beta sigma
          (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0) ↔
      (1 - beta) * ((4 * sigma) * (1 - sigma)) < beta - sigma by
        simpa [carlsonClassicalPolynomialDensityExponent] using
          (exists_polynomialHeight_targetAmplitude_decay_iff
            (beta := beta) (sigma := sigma) (A := 4 * sigma) hslope)]
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    simpa [q, mul_assoc] using hslope
  have hden : 0 < 1 + q := by linarith
  dsimp [carlsonClassicalTargetThreshold]
  constructor
  · intro h
    rw [div_lt_iff₀ hden]
    dsimp [q] at h ⊢
    nlinarith
  · intro h
    rw [div_lt_iff₀ hden] at h
    dsimp [q] at h ⊢
    nlinarith

/-- Inside the admissible target region there is a strictly negative exponent
with a positive margin.  This margin is what can absorb Carlson's `log^4`
factor. -/
theorem exists_carlsonPolynomialHeight_targetAmplitude_strictMargin
    {beta sigma : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hbeta :
      carlsonClassicalTargetThreshold sigma < beta) :
    ∃ alpha epsilon : ℝ,
      0 < epsilon ∧
      1 - beta < alpha ∧
      targetAmplitudePintzCarlsonExponent beta sigma
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0 := by
  obtain ⟨alpha, hcontour, hexponent⟩ :=
    (exists_carlsonPolynomialHeight_targetAmplitude_decay_iff
      hsigma hsigmaOne).2 hbeta
  let epsilon :=
    -targetAmplitudePintzCarlsonExponent beta sigma
      (carlsonClassicalPolynomialDensityExponent alpha sigma) / 2
  refine ⟨alpha, epsilon, ?_, hcontour, ?_⟩
  · dsimp [epsilon]
    linarith
  · dsimp [epsilon]
    linarith

/-- Carlson's actual multiplicity-weighted zero-density theorem together with
the exact target region in which its power exponent permits a compatible
polynomial lower height. -/
theorem carlson_zeroDensity_with_targetAmplitude_height
    {beta sigma : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hbeta :
      carlsonClassicalTargetThreshold sigma < beta) :
    ((fun T => (ZeroDensity.zeroDensityCount sigma T : ℝ))
        =O[Filter.atTop]
      (fun T =>
        T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4)) ∧
      ∃ alpha : ℝ,
        1 - beta < alpha ∧
        targetAmplitudePintzCarlsonExponent beta sigma
          (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0 := by
  exact ⟨CarlsonZeroDensity.carlson_zeroDensity_isBigO hsigma hsigmaOne,
    (exists_carlsonPolynomialHeight_targetAmplitude_decay_iff
      hsigma hsigmaOne).2 hbeta⟩

end PrimeNumberTheorem
