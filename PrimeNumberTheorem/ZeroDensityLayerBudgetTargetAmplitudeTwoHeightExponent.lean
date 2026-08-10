import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonTwoHeightSplit

/-!
# Target-amplitude two-height Carlson exponents

The ordinary two-height Carlson split gains the denominator at the
intermediate height, but its existing exponent is normalized against the PNT
scale `x`.  This file records the corresponding arithmetic after normalization
by a target-zero amplitude `x ^ (beta - 1)`.

Writing `q = 4 * sigma * (1 - sigma)`, the low and high exponents are

`q * gamma + tau - beta`

and

`q * alpha + tau - beta - gamma`.

The same balanced cut `gamma = q * alpha / (q + 1)` makes both equal to

`tau - beta + q^2 * alpha / (q + 1)`.
-/

namespace PrimeNumberTheorem

/-- Target-normalized exponent of the low-ordinate Carlson layer. -/
def targetAmplitudeCarlsonTwoHeightLowExponent
    (beta sigma tau gamma : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma * gamma + tau - beta

/-- Target-normalized exponent of the high-ordinate annulus, including the
denominator saving at the intermediate height. -/
def targetAmplitudeCarlsonTwoHeightHighExponent
    (beta sigma tau alpha gamma : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma * alpha + tau - beta - gamma

/-- Slope of the common balanced exponent as a function of the outer height
exponent. -/
noncomputable def targetAmplitudeCarlsonTwoHeightBalancedSlope
    (sigma : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma ^ 2 /
    (carlsonTwoHeightDensityExponent sigma + 1)

/-- Common target-normalized exponent at the balanced intermediate height. -/
noncomputable def targetAmplitudeCarlsonTwoHeightBalancedExponent
    (beta sigma tau alpha : ℝ) : ℝ :=
  tau - beta +
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma * alpha

theorem targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  unfold targetAmplitudeCarlsonTwoHeightBalancedSlope
  exact div_pos (pow_pos hq 2) (by linarith)

theorem targetAmplitudeCarlsonTwoHeightLowExponent_balanced
    {beta sigma tau alpha : ℝ}
    (hden : carlsonTwoHeightDensityExponent sigma + 1 ≠ 0) :
    targetAmplitudeCarlsonTwoHeightLowExponent beta sigma tau
        (carlsonTwoHeightBalancedCut sigma alpha) =
      targetAmplitudeCarlsonTwoHeightBalancedExponent
        beta sigma tau alpha := by
  unfold targetAmplitudeCarlsonTwoHeightLowExponent
    carlsonTwoHeightBalancedCut
    targetAmplitudeCarlsonTwoHeightBalancedExponent
    targetAmplitudeCarlsonTwoHeightBalancedSlope
  field_simp [hden]
  ring

theorem targetAmplitudeCarlsonTwoHeightHighExponent_balanced
    {beta sigma tau alpha : ℝ}
    (hden : carlsonTwoHeightDensityExponent sigma + 1 ≠ 0) :
    targetAmplitudeCarlsonTwoHeightHighExponent beta sigma tau alpha
        (carlsonTwoHeightBalancedCut sigma alpha) =
      targetAmplitudeCarlsonTwoHeightBalancedExponent
        beta sigma tau alpha := by
  unfold targetAmplitudeCarlsonTwoHeightHighExponent
    carlsonTwoHeightBalancedCut
    targetAmplitudeCarlsonTwoHeightBalancedExponent
    targetAmplitudeCarlsonTwoHeightBalancedSlope
  field_simp [hden]
  ring

/-- The denominator-saving balanced exponent is strictly below the exponent
obtained by counting the full strip at the outer height. -/
theorem targetAmplitudeCarlsonTwoHeightBalancedExponent_lt_singleHeight
    {beta sigma tau alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    targetAmplitudeCarlsonTwoHeightBalancedExponent
        beta sigma tau alpha <
      carlsonTwoHeightDensityExponent sigma * alpha + tau - beta := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  have hden : 0 < carlsonTwoHeightDensityExponent sigma + 1 := by
    linarith
  have hslope :
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma <
        carlsonTwoHeightDensityExponent sigma := by
    unfold targetAmplitudeCarlsonTwoHeightBalancedSlope
    rw [div_lt_iff₀ hden]
    nlinarith
  have hmul :
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma * alpha <
        carlsonTwoHeightDensityExponent sigma * alpha :=
    mul_lt_mul_of_pos_right hslope halpha
  unfold targetAmplitudeCarlsonTwoHeightBalancedExponent
  linarith

/-- Exact feasibility criterion for choosing an outer polynomial height above
the contour floor while retaining target-normalized two-height decay. -/
theorem exists_targetAmplitudeCarlsonTwoHeightBalancedDecay_iff
    {beta sigma tau : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        targetAmplitudeCarlsonTwoHeightBalancedExponent
          beta sigma tau alpha < 0) ↔
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) + tau - beta < 0 := by
  let slope := targetAmplitudeCarlsonTwoHeightBalancedSlope sigma
  have hslope : 0 < slope := by
    simpa [slope] using
      targetAmplitudeCarlsonTwoHeightBalancedSlope_pos hhalf hone
  constructor
  · rintro ⟨alpha, hcontour, hdecay⟩
    have hmul :
        slope * (1 - beta) < slope * alpha :=
      mul_lt_mul_of_pos_left hcontour hslope
    change tau - beta + slope * alpha < 0 at hdecay
    nlinarith
  · intro hfeasible
    have hlowerUpper :
        1 - beta < (beta - tau) / slope := by
      rw [lt_div_iff₀ hslope]
      nlinarith
    let alpha :=
      ((1 - beta) + (beta - tau) / slope) / 2
    have hcontour : 1 - beta < alpha := by
      dsimp [alpha]
      linarith
    have halphaUpper : alpha < (beta - tau) / slope := by
      dsimp [alpha]
      linarith
    have hproduct : slope * alpha < beta - tau := by
      have := (lt_div_iff₀ hslope).mp halphaUpper
      nlinarith
    refine ⟨alpha, hcontour, ?_⟩
    change tau - beta + slope * alpha < 0
    linarith

/-- A feasible balanced exponent supplies an explicit intermediate cut and a
single positive strict margin for both pieces of the split. -/
theorem exists_targetAmplitudeCarlsonTwoHeightStrictMargins
    {beta sigma tau : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hbetaOne : beta < 1)
    (hfeasible :
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) + tau - beta < 0) :
    ∃ alpha gamma epsilon : ℝ,
      1 - beta < alpha ∧
      0 < gamma ∧ gamma < alpha ∧
      0 < epsilon ∧
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gamma + epsilon < 0 ∧
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gamma + epsilon < 0 := by
  rcases
      (exists_targetAmplitudeCarlsonTwoHeightBalancedDecay_iff
        hhalf hone).mpr hfeasible with
    ⟨alpha, hcontour, hbalanced⟩
  have halpha : 0 < alpha := by
    linarith
  let gamma := carlsonTwoHeightBalancedCut sigma alpha
  let epsilon :=
    -targetAmplitudeCarlsonTwoHeightBalancedExponent
        beta sigma tau alpha / 2
  have hgammaPos : 0 < gamma := by
    simpa [gamma] using
      carlsonTwoHeightBalancedCut_pos hhalf hone halpha
  have hgammaAlpha : gamma < alpha := by
    simpa [gamma] using
      carlsonTwoHeightBalancedCut_lt_alpha hhalf hone halpha
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hden :
      carlsonTwoHeightDensityExponent sigma + 1 ≠ 0 := by
    have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
    linarith
  refine
    ⟨alpha, gamma, epsilon, hcontour, hgammaPos, hgammaAlpha,
      hepsilon, ?_, ?_⟩
  · rw [show gamma = carlsonTwoHeightBalancedCut sigma alpha by
      rfl]
    rw [targetAmplitudeCarlsonTwoHeightLowExponent_balanced hden]
    dsimp [epsilon]
    linarith
  · rw [show gamma = carlsonTwoHeightBalancedCut sigma alpha by
      rfl]
    rw [targetAmplitudeCarlsonTwoHeightHighExponent_balanced hden]
    dsimp [epsilon]
    linarith

/-- Carlson's classical density exponent is strictly below one away from the
critical-line endpoint. -/
theorem carlsonTwoHeightDensityExponent_lt_one
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    carlsonTwoHeightDensityExponent sigma < 1 := by
  have hne : 2 * sigma - 1 ≠ 0 := by
    linarith
  have hsquare : 0 < (2 * sigma - 1) ^ 2 :=
    sq_pos_of_ne_zero hne
  unfold carlsonTwoHeightDensityExponent
  nlinarith

/-- Consequently the balanced density slope is strictly below `1/2`. -/
theorem targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma < 1 / 2 := by
  let q := carlsonTwoHeightDensityExponent sigma
  have hq : 0 < q := by
    simpa [q] using carlsonTwoHeightDensityExponent_pos hhalf hone
  have hqOne : q < 1 := by
    simpa [q] using carlsonTwoHeightDensityExponent_lt_one hhalf
  have hden : 0 < q + 1 := by
    linarith
  have hmul : q * (q - 1) < 0 :=
    mul_neg_of_pos_of_neg hq (sub_neg.mpr hqOne)
  unfold targetAmplitudeCarlsonTwoHeightBalancedSlope
  change q ^ 2 / (q + 1) < 1 / 2
  rw [div_lt_iff₀ hden]
  nlinarith [hmul]

/-- Canonical real-part threshold for the target-amplitude two-height split. -/
noncomputable def targetAmplitudeCarlsonTwoHeightCanonicalThreshold
    (beta : ℝ) : ℝ :=
  (3 * beta - 1) / 2

theorem targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    1 / 2 <
        targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta ∧
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta < beta ∧
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta < 1 := by
  unfold targetAmplitudeCarlsonTwoHeightCanonicalThreshold
  constructor
  · linarith
  constructor <;> linarith

/-- At the canonical threshold, the exact target-amplitude two-height
feasibility expression is negative for every `2/3 < beta < 1`. -/
theorem targetAmplitudeCarlsonTwoHeightCanonical_feasible
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    targetAmplitudeCarlsonTwoHeightBalancedSlope
          (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) *
        (1 - beta) +
        targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta - beta < 0 := by
  rcases
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
        hbeta hbetaOne with
    ⟨hhalf, hsigmaBeta, hsigmaOne⟩
  have hslope :
      targetAmplitudeCarlsonTwoHeightBalancedSlope
          (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) <
        1 / 2 :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half
      hhalf hsigmaOne
  have hfloor : 0 < 1 - beta := sub_pos.mpr hbetaOne
  have hmul :
      targetAmplitudeCarlsonTwoHeightBalancedSlope
          (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) *
          (1 - beta) <
        (1 / 2) * (1 - beta) :=
    mul_lt_mul_of_pos_right hslope hfloor
  have hthreshold :
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta - beta =
        -(1 - beta) / 2 := by
    unfold targetAmplitudeCarlsonTwoHeightCanonicalThreshold
    ring
  linarith

/-- Explicit two-height parameters exist at the canonical threshold whenever
`2/3 < beta < 1`.  This is the arithmetic improvement over the canonical
single-height `3/4` threshold. -/
theorem exists_targetAmplitudeCarlsonTwoHeightCanonicalStrictMargins
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ alpha gamma epsilon : ℝ,
      1 - beta < alpha ∧
      0 < gamma ∧ gamma < alpha ∧
      0 < epsilon ∧
      targetAmplitudeCarlsonTwoHeightLowExponent beta
          (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta)
          (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta)
          gamma + epsilon < 0 ∧
      targetAmplitudeCarlsonTwoHeightHighExponent beta
          (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta)
          (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta)
          alpha gamma + epsilon < 0 := by
  rcases
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
        hbeta hbetaOne with
    ⟨hhalf, hsigmaBeta, hsigmaOne⟩
  exact
    exists_targetAmplitudeCarlsonTwoHeightStrictMargins
      hhalf hsigmaOne hbetaOne
      (targetAmplitudeCarlsonTwoHeightCanonical_feasible
        hbeta hbetaOne)

end PrimeNumberTheorem
