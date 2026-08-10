import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualBalancedTwoHeightTransfer

/-!
# Moving balanced Carlson margins near the line `re = 1`

For a moving gap `delta`, put `sigma = tau = 1 - delta`.  The Carlson density
exponent is `O(delta)`, hence the balanced two-height penalty is
`O(alpha * delta^2)`.  The endpoint gain is `delta`.  This file makes the
linear-versus-quadratic comparison explicit.
-/

namespace PrimeNumberTheorem

open Filter

noncomputable section

theorem carlsonTwoHeightDensityExponent_one_sub
    (delta : ℝ) :
    carlsonTwoHeightDensityExponent (1 - delta) =
      4 * (1 - delta) * delta := by
  simp [carlsonTwoHeightDensityExponent]

/-- Near one, the Carlson density exponent lies between zero and `4 * delta`.
-/
theorem carlsonTwoHeightDensityExponent_one_sub_bounds
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1) :
    0 ≤ carlsonTwoHeightDensityExponent (1 - delta) ∧
      carlsonTwoHeightDensityExponent (1 - delta) ≤ 4 * delta := by
  rw [carlsonTwoHeightDensityExponent_one_sub]
  constructor <;> nlinarith

/-- The balanced penalty is quadratically small in the moving distance from
one. -/
theorem carlsonTwoHeightBalancedPenalty_one_sub_le
    {delta alpha : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1)
    (halpha : 0 ≤ alpha) :
    carlsonTwoHeightDensityExponent (1 - delta) ^ 2 * alpha /
        (carlsonTwoHeightDensityExponent (1 - delta) + 1) ≤
      16 * alpha * delta ^ 2 := by
  let q := carlsonTwoHeightDensityExponent (1 - delta)
  have hqBounds :=
    carlsonTwoHeightDensityExponent_one_sub_bounds hdelta hdeltaOne
  have hq : 0 ≤ q := hqBounds.1
  have hqLe : q ≤ 4 * delta := hqBounds.2
  have hfourDelta : 0 ≤ 4 * delta := by positivity
  have hqSq : q ^ 2 ≤ (4 * delta) ^ 2 :=
    (sq_le_sq₀ hq hfourDelta).2 hqLe
  have hnum : 0 ≤ q ^ 2 * alpha :=
    mul_nonneg (sq_nonneg q) halpha
  have hdenom : 1 ≤ q + 1 := by linarith
  calc
    q ^ 2 * alpha / (q + 1) ≤ q ^ 2 * alpha :=
      div_le_self hnum hdenom
    _ ≤ (4 * delta) ^ 2 * alpha :=
      mul_le_mul_of_nonneg_right hqSq halpha
    _ = 16 * alpha * delta ^ 2 := by ring

/-- If `32 * alpha * delta <= 1`, the moving endpoint gain leaves at least
half of its linear margin after the balanced Carlson penalty. -/
theorem carlsonTwoHeightBalancedExponent_one_sub_le_neg_half
    {delta alpha : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (halpha : 0 ≤ alpha)
    (hsmall : 32 * alpha * delta ≤ 1) :
    carlsonTwoHeightBalancedExponent
        (1 - delta) (1 - delta) alpha ≤
      -delta / 2 := by
  have hpenalty :=
    carlsonTwoHeightBalancedPenalty_one_sub_le
      hdelta.le hdeltaOne halpha
  have hdeltaHalf : 0 ≤ delta / 2 := by positivity
  have hscaled :=
    mul_le_mul_of_nonneg_right hsmall hdeltaHalf
  rw [carlsonTwoHeightBalancedExponent]
  nlinarith

/-- Under the strict smallness condition, the moving endpoint remains
strictly below the balanced admissible ceiling. -/
theorem one_sub_lt_carlsonTwoHeightBalancedTauCeiling
    {delta alpha : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (halpha : 0 ≤ alpha)
    (hsmall : 32 * alpha * delta < 1) :
    1 - delta <
      carlsonTwoHeightBalancedTauCeiling (1 - delta) alpha := by
  have hbound :=
    carlsonTwoHeightBalancedExponent_one_sub_le_neg_half
      hdelta hdeltaOne halpha hsmall.le
  have hnegative :
      carlsonTwoHeightBalancedExponent
          (1 - delta) (1 - delta) alpha < 0 := by
    nlinarith
  have hiff :=
    (carlsonTwoHeightBalancedExponent_add_lt_zero_iff
      (sigma := 1 - delta) (tau := 1 - delta)
      (alpha := alpha) (epsilon := 0))
  exact (by simpa using hiff.mp (by simpa using hnegative))

/-- Filter form of the moving linear margin, ready for a dynamic zero-free
gap function. -/
theorem eventually_carlsonTwoHeightBalancedExponent_one_sub_le_neg_half
    {ι : Type*} {l : Filter ι} {delta : ι → ℝ} {alpha : ℝ}
    (halpha : 0 ≤ alpha)
    (hdelta :
      ∀ᶠ x in l,
        0 < delta x ∧ delta x ≤ 1 ∧
          32 * alpha * delta x ≤ 1) :
    ∀ᶠ x in l,
      carlsonTwoHeightBalancedExponent
          (1 - delta x) (1 - delta x) alpha ≤
        -delta x / 2 := by
  filter_upwards [hdelta] with x hx
  exact
    carlsonTwoHeightBalancedExponent_one_sub_le_neg_half
      hx.1 hx.2.1 halpha hx.2.2

/-- For the nondegenerate moving strip
`(1 - 2 * delta, 1 - delta]`, the Carlson density exponent is at most
`8 * delta`. -/
theorem carlsonTwoHeightDensityExponent_one_sub_two_mul_bounds
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2) :
    0 ≤ carlsonTwoHeightDensityExponent (1 - 2 * delta) ∧
      carlsonTwoHeightDensityExponent (1 - 2 * delta) ≤ 8 * delta := by
  rw [carlsonTwoHeightDensityExponent_one_sub]
  constructor <;> nlinarith

/-- The balanced penalty for the nondegenerate moving strip is bounded by
`64 * alpha * delta^2`. -/
theorem carlsonTwoHeightBalancedPenalty_one_sub_two_mul_le
    {delta alpha : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (halpha : 0 ≤ alpha) :
    carlsonTwoHeightDensityExponent (1 - 2 * delta) ^ 2 * alpha /
        (carlsonTwoHeightDensityExponent (1 - 2 * delta) + 1) ≤
      64 * alpha * delta ^ 2 := by
  let q := carlsonTwoHeightDensityExponent (1 - 2 * delta)
  have hqBounds :=
    carlsonTwoHeightDensityExponent_one_sub_two_mul_bounds
      hdelta hdeltaHalf
  have hq : 0 ≤ q := hqBounds.1
  have hqLe : q ≤ 8 * delta := hqBounds.2
  have heightDelta : 0 ≤ 8 * delta := by positivity
  have hqSq : q ^ 2 ≤ (8 * delta) ^ 2 :=
    (sq_le_sq₀ hq heightDelta).2 hqLe
  have hnum : 0 ≤ q ^ 2 * alpha :=
    mul_nonneg (sq_nonneg q) halpha
  have hdenom : 1 ≤ q + 1 := by linarith
  calc
    q ^ 2 * alpha / (q + 1) ≤ q ^ 2 * alpha :=
      div_le_self hnum hdenom
    _ ≤ (8 * delta) ^ 2 * alpha :=
      mul_le_mul_of_nonneg_right hqSq halpha
    _ = 64 * alpha * delta ^ 2 := by ring

/-- On the genuine strip `(1 - 2 * delta, 1 - delta]`, the endpoint gain
retains half its linear size once `128 * alpha * delta <= 1`. -/
theorem carlsonTwoHeightBalancedExponent_movingStrip_le_neg_half
    {delta alpha : ℝ}
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (halpha : 0 ≤ alpha)
    (hsmall : 128 * alpha * delta ≤ 1) :
    carlsonTwoHeightBalancedExponent
        (1 - 2 * delta) (1 - delta) alpha ≤
      -delta / 2 := by
  have hpenalty :=
    carlsonTwoHeightBalancedPenalty_one_sub_two_mul_le
      hdelta.le hdeltaHalf halpha
  have hdeltaHalfNonneg : 0 ≤ delta / 2 := by positivity
  have hscaled :=
    mul_le_mul_of_nonneg_right hsmall hdeltaHalfNonneg
  rw [carlsonTwoHeightBalancedExponent]
  nlinarith

/-- The moving upper endpoint is strictly below the balanced ceiling of the
lower endpoint. -/
theorem one_sub_lt_carlsonTwoHeightBalancedTauCeiling_movingStrip
    {delta alpha : ℝ}
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (halpha : 0 ≤ alpha)
    (hsmall : 128 * alpha * delta < 1) :
    1 - delta <
      carlsonTwoHeightBalancedTauCeiling
        (1 - 2 * delta) alpha := by
  have hbound :=
    carlsonTwoHeightBalancedExponent_movingStrip_le_neg_half
      hdelta hdeltaHalf halpha hsmall.le
  have hnegative :
      carlsonTwoHeightBalancedExponent
          (1 - 2 * delta) (1 - delta) alpha < 0 := by
    nlinarith
  have hiff :=
    (carlsonTwoHeightBalancedExponent_add_lt_zero_iff
      (sigma := 1 - 2 * delta) (tau := 1 - delta)
      (alpha := alpha) (epsilon := 0))
  exact (by simpa using hiff.mp (by simpa using hnegative))

/-- Filter form of the usable nondegenerate moving-strip margin. -/
theorem eventually_carlsonTwoHeightBalancedExponent_movingStrip_le_neg_half
    {ι : Type*} {l : Filter ι} {delta : ι → ℝ} {alpha : ℝ}
    (halpha : 0 ≤ alpha)
    (hdelta :
      ∀ᶠ x in l,
        0 < delta x ∧ delta x ≤ 1 / 2 ∧
          128 * alpha * delta x ≤ 1) :
    ∀ᶠ x in l,
      carlsonTwoHeightBalancedExponent
          (1 - 2 * delta x) (1 - delta x) alpha ≤
        -delta x / 2 := by
  filter_upwards [hdelta] with x hx
  exact
    carlsonTwoHeightBalancedExponent_movingStrip_le_neg_half
      hx.1 hx.2.1 halpha hx.2.2

end

end PrimeNumberTheorem
