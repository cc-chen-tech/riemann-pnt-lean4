import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightOptimalOuterExponent

/-!
# Optimal prescribed-cap outer-height exponent

The strip endpoint is optimized subject to lying above both the low-layer
threshold `sigma` and a prescribed global real-part ceiling `theta`.
-/

namespace PrimeNumberTheorem

/-- A common outer exponent is prescribed-cap feasible if some strip endpoint
above both `sigma` and `theta`, and below `beta`, makes the fixed-endpoint
constraints feasible. -/
def IsJointTwoHeightPrescribedCapOuterExponentFeasible
    (beta sigma theta alpha : ℝ) : Prop :=
  ∃ tau : ℝ,
    sigma < tau ∧
    theta < tau ∧
    tau < beta ∧
    IsJointTwoHeightOuterExponentFeasible beta sigma tau alpha

/-- The supremal common outer exponent after optimizing the strip endpoint
above `max sigma theta`. -/
noncomputable def jointTwoHeightPrescribedCapOuterExponentCeiling
    (beta sigma theta : ℝ) : ℝ :=
  min 1
    (min
      (2 * (beta - sigma))
      ((beta - max sigma theta) /
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma))

/-- Every contour-compatible exponent strictly below the optimized ceiling
admits an explicit strip endpoint above the prescribed cap. -/
theorem jointTwoHeightPrescribedCapOuterExponentFeasible_of_lt_ceiling
    {beta sigma theta alpha : ℝ}
    (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hcontour : 1 - beta < alpha)
    (halpha :
      alpha <
        jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta) :
    IsJointTwoHeightPrescribedCapOuterExponentFeasible
      beta sigma theta alpha := by
  have hslope :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigmaHalf hsigmaOne
  unfold jointTwoHeightPrescribedCapOuterExponentCeiling at halpha
  rcases lt_min_iff.mp halpha with ⟨halphaOne, hinner⟩
  rcases lt_min_iff.mp hinner with ⟨halphaLow, halphaHigh⟩
  have hproduct :
      alpha *
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma <
        beta - max sigma theta :=
    (lt_div_iff₀ hslope).mp halphaHigh
  let tauUpper :=
    beta -
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma * alpha
  have hmaxUpper : max sigma theta < tauUpper := by
    dsimp [tauUpper]
    nlinarith
  let tau := (max sigma theta + tauUpper) / 2
  have hmaxTau : max sigma theta < tau := by
    dsimp [tau]
    linarith
  have htauUpper : tau < tauUpper := by
    dsimp [tau]
    linarith
  have hsigmaTau : sigma < tau :=
    (le_max_left sigma theta).trans_lt hmaxTau
  have hthetaTau : theta < tau :=
    (le_max_right sigma theta).trans_lt hmaxTau
  have halphaPos : 0 < alpha := by
    have : 0 < 1 - beta := sub_pos.mpr hbetaOne
    linarith
  have hpositiveProduct :
      0 <
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma * alpha :=
    mul_pos hslope halphaPos
  have htauUpperBeta : tauUpper < beta := by
    dsimp [tauUpper]
    linarith
  have htauBeta : tau < beta :=
    htauUpper.trans htauUpperBeta
  refine
    ⟨tau, hsigmaTau, hthetaTau, htauBeta,
      halphaOne.le, ?_, ?_⟩
  · linarith
  · unfold targetAmplitudeCarlsonTwoHeightBalancedExponent
    dsimp [tauUpper] at htauUpper
    nlinarith

/-- Every prescribed-cap feasible exponent is bounded by the optimized
ceiling, independently of which endpoint witnesses feasibility. -/
theorem le_jointTwoHeightPrescribedCapOuterExponentCeiling_of_feasible
    {beta sigma theta alpha : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha :
      IsJointTwoHeightPrescribedCapOuterExponentFeasible
        beta sigma theta alpha) :
    alpha ≤
      jointTwoHeightPrescribedCapOuterExponentCeiling
        beta sigma theta := by
  have hslope :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigmaHalf hsigmaOne
  rcases halpha with
    ⟨tau, hsigmaTau, hthetaTau, _htauBeta,
      halphaOne, halphaLow, halphaHigh⟩
  have hmaxTau : max sigma theta < tau :=
    max_lt hsigmaTau hthetaTau
  have hlow : alpha ≤ 2 * (beta - sigma) := by
    have : alpha < 2 * (beta - sigma) := by
      linarith
    exact this.le
  have hproduct :
      alpha *
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma <
        beta - max sigma theta := by
    unfold targetAmplitudeCarlsonTwoHeightBalancedExponent at halphaHigh
    nlinarith
  have hhigh :
      alpha ≤
        (beta - max sigma theta) /
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    ((lt_div_iff₀ hslope).mpr hproduct).le
  unfold jointTwoHeightPrescribedCapOuterExponentCeiling
  exact le_min halphaOne (le_min hlow hhigh)

/-- A contour-compatible exponent and prescribed-cap endpoint exist exactly
when the contour floor lies below the optimized ceiling. -/
theorem
    exists_contourCompatible_jointTwoHeightPrescribedCapOuterExponent_iff
    {beta sigma theta : ℝ}
    (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        IsJointTwoHeightPrescribedCapOuterExponentFeasible
          beta sigma theta alpha) ↔
      1 - beta <
        jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta := by
  constructor
  · rintro ⟨alpha, hcontour, halpha⟩
    exact
      hcontour.trans_le
        (le_jointTwoHeightPrescribedCapOuterExponentCeiling_of_feasible
          hsigmaHalf hsigmaOne halpha)
  · intro hfloor
    let alpha :=
      ((1 - beta) +
        jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta) / 2
    have hcontour : 1 - beta < alpha := by
      dsimp [alpha]
      linarith
    have halphaCeiling :
        alpha <
          jointTwoHeightPrescribedCapOuterExponentCeiling
            beta sigma theta := by
      dsimp [alpha]
      linarith
    exact
      ⟨alpha, hcontour,
        jointTwoHeightPrescribedCapOuterExponentFeasible_of_lt_ceiling
          hbetaOne hsigmaHalf hsigmaOne hcontour halphaCeiling⟩

/-- Exact arithmetic criterion for the contour floor to lie below the
endpoint-optimized prescribed-cap ceiling. -/
theorem
    contourFloor_lt_jointTwoHeightPrescribedCapOuterExponentCeiling_iff
    {beta sigma theta : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    1 - beta <
        jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta ↔
      0 < beta ∧
      sigma < (3 * beta - 1) / 2 ∧
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) + max sigma theta - beta < 0 := by
  have hslope :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigmaHalf hsigmaOne
  constructor
  · intro hfloor
    unfold jointTwoHeightPrescribedCapOuterExponentCeiling at hfloor
    rcases lt_min_iff.mp hfloor with ⟨hone, hinner⟩
    rcases lt_min_iff.mp hinner with ⟨hlow, hhigh⟩
    refine ⟨by linarith, by linarith, ?_⟩
    have hproduct :=
      (lt_div_iff₀ hslope).mp hhigh
    nlinarith
  · rintro ⟨hbeta, hsigma, hhigh⟩
    unfold jointTwoHeightPrescribedCapOuterExponentCeiling
    apply lt_min
    · linarith
    apply lt_min
    · linarith
    · rw [lt_div_iff₀ hslope]
      nlinarith

/-- Exact arithmetic criterion for existence after jointly optimizing the
strip endpoint and common outer-height exponent. -/
theorem
    exists_contourCompatible_jointTwoHeightPrescribedCapOuterExponent_iff_arithmetic
    {beta sigma theta : ℝ}
    (hbetaOne : beta < 1)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    (∃ alpha : ℝ,
        1 - beta < alpha ∧
        IsJointTwoHeightPrescribedCapOuterExponentFeasible
          beta sigma theta alpha) ↔
      0 < beta ∧
      sigma < (3 * beta - 1) / 2 ∧
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) + max sigma theta - beta < 0 :=
  (exists_contourCompatible_jointTwoHeightPrescribedCapOuterExponent_iff
      hbetaOne hsigmaHalf hsigmaOne).trans
    (contourFloor_lt_jointTwoHeightPrescribedCapOuterExponentCeiling_iff
      hsigmaHalf hsigmaOne)

end PrimeNumberTheorem
