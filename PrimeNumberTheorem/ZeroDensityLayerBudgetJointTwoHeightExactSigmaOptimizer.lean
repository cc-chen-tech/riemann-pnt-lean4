import Mathlib.Topology.Order.IntermediateValue
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightMidpointSigmaImprovement

/-!
# Exact optimization of the density threshold

For a prescribed cap `1 / 2 < theta < beta`, the low-layer outer-height
constraint decreases with `sigma`, while the Carlson constraint increases
until the two constraints balance.  This module constructs a balancing
threshold and proves that it globally maximizes the prescribed-cap ceiling.
-/

namespace PrimeNumberTheorem

open Set

/-- The Carlson density exponent decreases on `[1 / 2, 1]`. -/
theorem carlsonTwoHeightDensityExponent_antitoneOn_half_one
    {sigma₁ sigma₂ : ℝ}
    (hhalf : 1 / 2 ≤ sigma₁)
    (hle : sigma₁ ≤ sigma₂) :
    carlsonTwoHeightDensityExponent sigma₂ ≤
      carlsonTwoHeightDensityExponent sigma₁ := by
  have hproduct :
      0 ≤ (sigma₂ - sigma₁) * (sigma₁ + sigma₂ - 1) :=
    mul_nonneg (sub_nonneg.mpr hle) (by linarith)
  unfold carlsonTwoHeightDensityExponent
  nlinarith

/-- The balanced Carlson slope inherits the same antitonicity. -/
theorem targetAmplitudeCarlsonTwoHeightBalancedSlope_antitoneOn_half_one
    {sigma₁ sigma₂ : ℝ}
    (hhalf : 1 / 2 ≤ sigma₁)
    (hle : sigma₁ ≤ sigma₂)
    (hone : sigma₂ ≤ 1) :
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ ≤
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ := by
  let q₁ := carlsonTwoHeightDensityExponent sigma₁
  let q₂ := carlsonTwoHeightDensityExponent sigma₂
  have hq₁ : 0 ≤ q₁ := by
    dsimp [q₁, carlsonTwoHeightDensityExponent]
    have hsigma₁One : sigma₁ ≤ 1 := hle.trans hone
    have hproduct : 0 ≤ sigma₁ * (1 - sigma₁) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hq₂ : 0 ≤ q₂ := by
    dsimp [q₂, carlsonTwoHeightDensityExponent]
    have hsigma₂Half : 1 / 2 ≤ sigma₂ := hhalf.trans hle
    have hproduct : 0 ≤ sigma₂ * (1 - sigma₂) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hq₂q₁ : q₂ ≤ q₁ := by
    simpa [q₁, q₂] using
      carlsonTwoHeightDensityExponent_antitoneOn_half_one
        hhalf hle
  have hden₁ : 0 < q₁ + 1 := by linarith
  have hden₂ : 0 < q₂ + 1 := by linarith
  have hfactor :
      0 ≤ (q₁ - q₂) * (q₁ + q₂ + q₁ * q₂) :=
    mul_nonneg (sub_nonneg.mpr hq₂q₁)
      (add_nonneg (add_nonneg hq₁ hq₂) (mul_nonneg hq₁ hq₂))
  unfold targetAmplitudeCarlsonTwoHeightBalancedSlope
  change q₂ ^ 2 / (q₂ + 1) ≤ q₁ ^ 2 / (q₁ + 1)
  rw [div_le_div_iff₀ hden₂ hden₁]
  nlinarith

/-- Polynomial obtained by clearing the positive denominator from the
equation which balances the low-layer and Carlson outer-height constraints. -/
noncomputable def jointTwoHeightSigmaBalancePolynomial
    (beta theta sigma : ℝ) : ℝ :=
  2 * carlsonTwoHeightDensityExponent sigma ^ 2 * (beta - sigma) -
    (beta - theta) * (carlsonTwoHeightDensityExponent sigma + 1)

theorem continuous_jointTwoHeightSigmaBalancePolynomial
    (beta theta : ℝ) :
    Continuous (jointTwoHeightSigmaBalancePolynomial beta theta) := by
  unfold jointTwoHeightSigmaBalancePolynomial
    carlsonTwoHeightDensityExponent
  fun_prop

theorem jointTwoHeightSigmaBalancePolynomial_half
    (beta theta : ℝ) :
    jointTwoHeightSigmaBalancePolynomial beta theta (1 / 2) =
      2 * theta - 1 := by
  unfold jointTwoHeightSigmaBalancePolynomial
    carlsonTwoHeightDensityExponent
  ring

theorem jointTwoHeightSigmaBalancePolynomial_theta_neg
    {beta theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1) :
    jointTwoHeightSigmaBalancePolynomial beta theta theta < 0 := by
  have hthetaOne : theta < 1 := hthetaBeta.trans hbetaOne
  let q := carlsonTwoHeightDensityExponent theta
  have hq : 0 < q := by
    simpa [q] using
      carlsonTwoHeightDensityExponent_pos hthetaHalf hthetaOne
  have hden : 0 < q + 1 := by linarith
  have hslopeHalf :
      targetAmplitudeCarlsonTwoHeightBalancedSlope theta < 1 / 2 :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half
      hthetaHalf hthetaOne
  have hdiff : 0 < beta - theta := sub_pos.mpr hthetaBeta
  have hinner :
      2 *
          targetAmplitudeCarlsonTwoHeightBalancedSlope theta *
          (beta - theta) -
        (beta - theta) < 0 := by
    have hgain :
        0 <
          (beta - theta) *
            (1 / 2 -
              targetAmplitudeCarlsonTwoHeightBalancedSlope theta) :=
      mul_pos hdiff (sub_pos.mpr hslopeHalf)
    nlinarith
  have hid :
      jointTwoHeightSigmaBalancePolynomial beta theta theta =
        (q + 1) *
          (2 *
              targetAmplitudeCarlsonTwoHeightBalancedSlope theta *
              (beta - theta) -
            (beta - theta)) := by
    unfold jointTwoHeightSigmaBalancePolynomial
      targetAmplitudeCarlsonTwoHeightBalancedSlope
    change
      2 * q ^ 2 * (beta - theta) -
          (beta - theta) * (q + 1) =
        (q + 1) *
          (2 * (q ^ 2 / (q + 1)) * (beta - theta) -
            (beta - theta))
    field_simp [hden.ne']
  rw [hid]
  exact mul_neg_of_pos_of_neg hden hinner

/-- A density threshold is balancing when it lies inside the cap interval and
the low-layer exponent equals the Carlson exponent after cross multiplication. -/
def IsJointTwoHeightSigmaOptimizer
    (beta theta sigma : ℝ) : Prop :=
  1 / 2 < sigma ∧
    sigma < theta ∧
    2 *
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
        (beta - sigma) =
      beta - theta

/-- The balancing density threshold exists by the intermediate value theorem
applied to the denominator-cleared balance polynomial. -/
theorem exists_jointTwoHeightSigmaOptimizer
    {beta theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1) :
    ∃ sigma : ℝ, IsJointTwoHeightSigmaOptimizer beta theta sigma := by
  let f := jointTwoHeightSigmaBalancePolynomial beta theta
  have hhalfPos : 0 < f (1 / 2) := by
    dsimp [f]
    rw [jointTwoHeightSigmaBalancePolynomial_half]
    linarith
  have hthetaNeg : f theta < 0 := by
    dsimp [f]
    exact
      jointTwoHeightSigmaBalancePolynomial_theta_neg
        hthetaHalf hthetaBeta hbetaOne
  have hzero :
      (0 : ℝ) ∈ Set.Icc (f theta) (f (1 / 2)) :=
    ⟨hthetaNeg.le, hhalfPos.le⟩
  have himage :
      (0 : ℝ) ∈ f '' Set.Icc (1 / 2) theta :=
    intermediate_value_Icc' hthetaHalf.le
      (continuous_jointTwoHeightSigmaBalancePolynomial beta theta).continuousOn
      hzero
  rcases himage with ⟨sigma, hsigmaIcc, hsigmaZero⟩
  have hsigmaNeHalf : sigma ≠ 1 / 2 := by
    intro hsigma
    subst sigma
    linarith
  have hsigmaNeTheta : sigma ≠ theta := by
    intro hsigma
    subst sigma
    linarith
  have hsigmaHalf : 1 / 2 < sigma :=
    lt_of_le_of_ne hsigmaIcc.1 (Ne.symm hsigmaNeHalf)
  have hsigmaTheta : sigma < theta :=
    lt_of_le_of_ne hsigmaIcc.2 hsigmaNeTheta
  have hsigmaOne : sigma < 1 :=
    hsigmaTheta.trans (hthetaBeta.trans hbetaOne)
  let q := carlsonTwoHeightDensityExponent sigma
  have hq : 0 < q := by
    simpa [q] using
      carlsonTwoHeightDensityExponent_pos hsigmaHalf hsigmaOne
  have hden : q + 1 ≠ 0 := by linarith
  have hid :
      jointTwoHeightSigmaBalancePolynomial beta theta sigma =
        (q + 1) *
          (2 *
              targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
              (beta - sigma) -
            (beta - theta)) := by
    unfold jointTwoHeightSigmaBalancePolynomial
      targetAmplitudeCarlsonTwoHeightBalancedSlope
    change
      2 * q ^ 2 * (beta - sigma) -
          (beta - theta) * (q + 1) =
        (q + 1) *
          (2 * (q ^ 2 / (q + 1)) * (beta - sigma) -
            (beta - theta))
    field_simp [hden]
  have hscaled :
      (q + 1) *
          (2 *
              targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
              (beta - sigma) -
            (beta - theta)) =
        0 := by
    rw [← hid]
    exact hsigmaZero
  have hbalance :
      2 *
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (beta - sigma) =
        beta - theta := by
    have :=
      (mul_eq_zero.mp hscaled).resolve_left hden
    linarith
  exact ⟨sigma, hsigmaHalf, hsigmaTheta, hbalance⟩

/-- At a balancing threshold, the two nontrivial ceiling components coincide,
so the ceiling has the explicit value `min 1 (2 * (beta - sigma))`. -/
theorem jointTwoHeightPrescribedCapOuterExponentCeiling_eq_of_sigmaOptimizer
    {beta theta sigma : ℝ}
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1)
    (hoptimizer : IsJointTwoHeightSigmaOptimizer beta theta sigma) :
    jointTwoHeightPrescribedCapOuterExponentCeiling beta sigma theta =
      min 1 (2 * (beta - sigma)) := by
  rcases hoptimizer with ⟨hsigmaHalf, hsigmaTheta, hbalance⟩
  have hsigmaOne : sigma < 1 :=
    hsigmaTheta.trans (hthetaBeta.trans hbetaOne)
  have hslopePos :
      0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
      hsigmaHalf hsigmaOne
  have hratio :
      (beta - max sigma theta) /
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma =
        2 * (beta - sigma) := by
    rw [max_eq_right hsigmaTheta.le]
    rw [div_eq_iff hslopePos.ne']
    nlinarith
  unfold jointTwoHeightPrescribedCapOuterExponentCeiling
  rw [hratio, min_self]

/-- Every admissible density threshold has ceiling at most the ceiling of a
balancing threshold.  Hence any balancing threshold is a global optimizer,
without requiring a closed-form solution of the resulting polynomial. -/
theorem
    jointTwoHeightPrescribedCapOuterExponentCeiling_le_at_sigmaOptimizer
    {beta theta sigmaOpt sigma : ℝ}
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1)
    (hoptimizer : IsJointTwoHeightSigmaOptimizer beta theta sigmaOpt)
    (hsigmaHalf : 1 / 2 < sigma)
    (hsigmaBeta : sigma < beta) :
    jointTwoHeightPrescribedCapOuterExponentCeiling beta sigma theta ≤
      jointTwoHeightPrescribedCapOuterExponentCeiling
        beta sigmaOpt theta := by
  rcases hoptimizer with
    ⟨hsigmaOptHalf, hsigmaOptTheta, hbalanceOpt⟩
  have hsigmaOne : sigma < 1 := hsigmaBeta.trans hbetaOne
  have hsigmaOptOne : sigmaOpt < 1 :=
    hsigmaOptTheta.trans (hthetaBeta.trans hbetaOne)
  have hceilingOne :
      jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta ≤
        1 := by
    unfold jointTwoHeightPrescribedCapOuterExponentCeiling
    exact min_le_left _ _
  have hceilingLow :
      jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigma theta ≤
        2 * (beta - sigma) := by
    unfold jointTwoHeightPrescribedCapOuterExponentCeiling
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hoptimizerCeiling :
      jointTwoHeightPrescribedCapOuterExponentCeiling
          beta sigmaOpt theta =
        min 1 (2 * (beta - sigmaOpt)) :=
    jointTwoHeightPrescribedCapOuterExponentCeiling_eq_of_sigmaOptimizer
      hthetaBeta hbetaOne
      ⟨hsigmaOptHalf, hsigmaOptTheta, hbalanceOpt⟩
  rw [hoptimizerCeiling]
  apply le_min hceilingOne
  by_cases hthetaSigma : theta ≤ sigma
  · exact hceilingLow.trans (by linarith)
  · have hsigmaTheta : sigma < theta := lt_of_not_ge hthetaSigma
    by_cases hsigmaOpt : sigma ≤ sigmaOpt
    · have hslopeAnti :
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigmaOpt ≤
            targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
        targetAmplitudeCarlsonTwoHeightBalancedSlope_antitoneOn_half_one
          hsigmaHalf.le hsigmaOpt hsigmaOptOne.le
      have hslopePos :
          0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma :=
        targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
          hsigmaHalf hsigmaOne
      have hslopeOptPos :
          0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigmaOpt :=
        targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
          hsigmaOptHalf hsigmaOptOne
      have hgap : 0 ≤ beta - theta :=
        (sub_pos.mpr hthetaBeta).le
      have hdivision :
          (beta - theta) /
              targetAmplitudeCarlsonTwoHeightBalancedSlope sigma ≤
            (beta - theta) /
              targetAmplitudeCarlsonTwoHeightBalancedSlope sigmaOpt := by
        rw [div_le_div_iff₀ hslopePos hslopeOptPos]
        exact mul_le_mul_of_nonneg_left hslopeAnti hgap
      have hceilingHigh :
          jointTwoHeightPrescribedCapOuterExponentCeiling
              beta sigma theta ≤
            (beta - theta) /
              targetAmplitudeCarlsonTwoHeightBalancedSlope sigma := by
        unfold jointTwoHeightPrescribedCapOuterExponentCeiling
        rw [max_eq_right hsigmaTheta.le]
        exact (min_le_right _ _).trans (min_le_right _ _)
      have hratioOpt :
          (beta - theta) /
              targetAmplitudeCarlsonTwoHeightBalancedSlope sigmaOpt =
            2 * (beta - sigmaOpt) := by
        rw [div_eq_iff hslopeOptPos.ne']
        nlinarith
      exact hceilingHigh.trans (hdivision.trans_eq hratioOpt)
    · have hsigmaOptLt : sigmaOpt < sigma := lt_of_not_ge hsigmaOpt
      exact hceilingLow.trans (by linarith)

end PrimeNumberTheorem
