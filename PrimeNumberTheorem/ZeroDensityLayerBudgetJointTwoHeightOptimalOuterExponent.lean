import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightPrescribedCapFeasibility

/-!
# Optimal common outer-height exponent

The low global layer, the balanced Carlson strip, and the polynomial-height
cap impose three upper constraints on the common outer exponent.  Their
minimum is proved here to be the exact supremal exponent.
-/

namespace PrimeNumberTheorem

/-- Numerical feasibility of one common outer-height exponent for the balanced
low global layer and target-amplitude Carlson strip. -/
def IsJointTwoHeightOuterExponentFeasible
    (beta sigma tau alpha : ℝ) : Prop :=
  alpha ≤ 1 ∧
    alpha / 2 + sigma - beta < 0 ∧
    targetAmplitudeCarlsonTwoHeightBalancedExponent
      beta sigma tau alpha < 0

/-- The supremal common outer-height exponent imposed by the unit cap, the
balanced low global layer, and the balanced Carlson strip. -/
noncomputable def jointTwoHeightOuterExponentCeiling
    (beta sigma tau : ℝ) : ℝ :=
  min 1
    (min
      (2 * (beta - sigma))
      ((beta - tau) /
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma))

/-- Every exponent strictly below the joint ceiling satisfies all three
outer-height constraints. -/
theorem jointTwoHeightOuterExponentFeasible_of_lt_ceiling
    {beta sigma tau alpha : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha :
      alpha < jointTwoHeightOuterExponentCeiling beta sigma tau) :
    IsJointTwoHeightOuterExponentFeasible
      beta sigma tau alpha := by
  have hslope :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigmaHalf hsigmaOne
  unfold jointTwoHeightOuterExponentCeiling at halpha
  rcases lt_min_iff.mp halpha with ⟨halphaOne, hinner⟩
  rcases lt_min_iff.mp hinner with ⟨halphaLow, halphaHigh⟩
  refine ⟨halphaOne.le, ?_, ?_⟩
  · linarith
  · have hproduct :
        alpha *
            targetAmplitudeCarlsonTwoHeightBalancedSlope sigma <
          beta - tau :=
      (lt_div_iff₀ hslope).mp halphaHigh
    unfold targetAmplitudeCarlsonTwoHeightBalancedExponent
    nlinarith

/-- Every feasible exponent is bounded above by the joint ceiling.  Equality
is allowed only because the polynomial cap `alpha <= 1` is closed. -/
theorem le_jointTwoHeightOuterExponentCeiling_of_feasible
    {beta sigma tau alpha : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha :
      IsJointTwoHeightOuterExponentFeasible beta sigma tau alpha) :
    alpha ≤ jointTwoHeightOuterExponentCeiling beta sigma tau := by
  have hslope :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigmaHalf hsigmaOne
  rcases halpha with ⟨halphaOne, halphaLow, halphaHigh⟩
  have hlow : alpha ≤ 2 * (beta - sigma) := by
    have : alpha < 2 * (beta - sigma) := by
      linarith
    exact this.le
  have hproduct :
      alpha *
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma <
        beta - tau := by
    unfold targetAmplitudeCarlsonTwoHeightBalancedExponent at halphaHigh
    nlinarith
  have hhigh :
      alpha ≤
        (beta - tau) /
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    ((lt_div_iff₀ hslope).mpr hproduct).le
  unfold jointTwoHeightOuterExponentCeiling
  exact le_min halphaOne (le_min hlow hhigh)

/-- A contour-compatible feasible outer exponent exists exactly when the
contour floor lies strictly below the joint ceiling. -/
theorem exists_contourCompatible_jointTwoHeightOuterExponent_iff
    {beta sigma tau : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        IsJointTwoHeightOuterExponentFeasible
          beta sigma tau alpha) ↔
      1 - beta <
        jointTwoHeightOuterExponentCeiling beta sigma tau := by
  constructor
  · rintro ⟨alpha, hcontour, halpha⟩
    exact
      hcontour.trans_le
        (le_jointTwoHeightOuterExponentCeiling_of_feasible
          hsigmaHalf hsigmaOne halpha)
  · intro hfloor
    let alpha :=
      ((1 - beta) +
        jointTwoHeightOuterExponentCeiling beta sigma tau) / 2
    have hcontour : 1 - beta < alpha := by
      dsimp [alpha]
      linarith
    have halphaCeiling :
        alpha <
          jointTwoHeightOuterExponentCeiling beta sigma tau := by
      dsimp [alpha]
      linarith
    exact
      ⟨alpha, hcontour,
        jointTwoHeightOuterExponentFeasible_of_lt_ceiling
          hsigmaHalf hsigmaOne halphaCeiling⟩

/-- The contour floor lies below the optimal common ceiling exactly under the
three arithmetic conditions for the unit cap, low layer, and Carlson strip. -/
theorem contourFloor_lt_jointTwoHeightOuterExponentCeiling_iff
    {beta sigma tau : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    1 - beta <
        jointTwoHeightOuterExponentCeiling beta sigma tau ↔
      0 < beta ∧
      sigma < (3 * beta - 1) / 2 ∧
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) + tau - beta < 0 := by
  have hslope :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigmaHalf hsigmaOne
  constructor
  · intro hfloor
    unfold jointTwoHeightOuterExponentCeiling at hfloor
    rcases lt_min_iff.mp hfloor with ⟨hone, hinner⟩
    rcases lt_min_iff.mp hinner with ⟨hlow, hhigh⟩
    refine ⟨by linarith, by linarith, ?_⟩
    have hproduct :=
      (lt_div_iff₀ hslope).mp hhigh
    nlinarith
  · rintro ⟨hbeta, hsigma, hhigh⟩
    unfold jointTwoHeightOuterExponentCeiling
    apply lt_min
    · linarith
    apply lt_min
    · linarith
    · rw [lt_div_iff₀ hslope]
      nlinarith

/-- Exact arithmetic criterion for the existence of a contour-compatible
common outer-height exponent. -/
theorem exists_contourCompatible_jointTwoHeightOuterExponent_iff_arithmetic
    {beta sigma tau : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        IsJointTwoHeightOuterExponentFeasible
          beta sigma tau alpha) ↔
      0 < beta ∧
      sigma < (3 * beta - 1) / 2 ∧
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) + tau - beta < 0 :=
  (exists_contourCompatible_jointTwoHeightOuterExponent_iff
      hsigmaHalf hsigmaOne).trans
    (contourFloor_lt_jointTwoHeightOuterExponentCeiling_iff
      hsigmaHalf hsigmaOne)

end PrimeNumberTheorem
