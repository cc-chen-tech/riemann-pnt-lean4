import Mathlib

/-!
# Two-height numerical core

This file owns only the real-arithmetic definitions and balancing identities
used by the target-normalized two-height parameter construction.  It does not
define zero sets, zero counts, tails, contour errors, or smoothing transfers.
-/

namespace PrimeNumberTheorem

/-- Carlson's classical polynomial density exponent at real threshold
`sigma`. -/
def carlsonTwoHeightDensityExponent (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

/-- The intermediate-height exponent which balances the two Carlson
contributions. -/
noncomputable def carlsonTwoHeightBalancedCut
    (sigma alpha : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma * alpha /
    (carlsonTwoHeightDensityExponent sigma + 1)

/-- Target-normalized exponent of the low-ordinate Carlson layer. -/
def targetAmplitudeCarlsonTwoHeightLowExponent
    (beta sigma tau gamma : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma * gamma + tau - beta

/-- Target-normalized exponent of the high-ordinate Carlson annulus. -/
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

theorem carlsonTwoHeightDensityExponent_pos
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    0 < carlsonTwoHeightDensityExponent sigma := by
  unfold carlsonTwoHeightDensityExponent
  exact mul_pos
    (mul_pos (by norm_num) (lt_trans (by norm_num) hhalf))
    (sub_pos.mpr hone)

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

theorem carlsonTwoHeightBalancedCut_pos
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    0 < carlsonTwoHeightBalancedCut sigma alpha := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  exact div_pos (mul_pos hq halpha) (by linarith)

theorem carlsonTwoHeightBalancedCut_lt_alpha
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    carlsonTwoHeightBalancedCut sigma alpha < alpha := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  rw [carlsonTwoHeightBalancedCut]
  exact (div_lt_iff₀ (by linarith)).2 (by nlinarith)

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

/-- The balanced density slope is strictly below `1 / 2`. -/
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

end PrimeNumberTheorem
