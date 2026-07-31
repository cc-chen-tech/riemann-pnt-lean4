import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightThetaOnlyTargetAsymptotic

/-!
# Cubic strict target exponent

The midpoint strict target is replaced by an interpolation whose coefficient
vanishes quadratically in `1 - theta`. It remains strictly feasible for every
cap in `(1 / 2, 1)` while preserving the cubic target scale.
-/

namespace PrimeNumberTheorem

open Filter Set
open scoped Topology

/-- A strict target obtained by moving quadratically from the inverse boundary
toward one. -/
noncomputable def jointTwoHeightCubicStrictTargetExponent
    (theta : ℝ) : ℝ :=
  let betaBoundary := jointTwoHeightOptimalTargetExponent theta
  betaBoundary +
    ((1 - theta) ^ 2 / 2) * (1 - betaBoundary)

/-- Complete feasibility and comparison specification for the cubic strict
target exponent. -/
theorem jointTwoHeightCubicStrictTargetExponent_spec
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    let betaBoundary := jointTwoHeightOptimalTargetExponent theta
    let beta := jointTwoHeightCubicStrictTargetExponent theta
    2 / 3 < betaBoundary ∧
      betaBoundary < beta ∧
      beta < jointTwoHeightCanonicalStrictTargetExponent theta ∧
      beta < 1 ∧
      2 / 3 < beta ∧
      theta < betaBoundary ∧
      theta < beta ∧
      jointTwoHeightImprovedGlobalCapThreshold betaBoundary = theta ∧
      theta < jointTwoHeightImprovedGlobalCapThreshold beta := by
  let betaBoundary := jointTwoHeightOptimalTargetExponent theta
  let beta := jointTwoHeightCubicStrictTargetExponent theta
  let c := (1 - theta) ^ 2 / 2
  have hboundary :
      IsJointTwoHeightOptimalTargetExponent theta betaBoundary := by
    simpa [betaBoundary] using
      jointTwoHeightOptimalTargetExponent_spec hthetaHalf hthetaOne
  rcases hboundary with
    ⟨hboundaryLower, hboundaryOne, hboundaryThreshold⟩
  have hthetaBoundary : theta < betaBoundary := by
    have hthresholdLt :=
      (jointTwoHeightImprovedGlobalCapThreshold_spec
        hboundaryLower hboundaryOne).2
    linarith
  have hdeltaPos : 0 < 1 - theta := by linarith
  have hdeltaLtOne : 1 - theta < 1 := by linarith
  have hdeltaComplementPos : 0 < 1 - (1 - theta) := by linarith
  have hdeltaSqLtDelta : (1 - theta) ^ 2 < 1 - theta := by
    have hproduct :=
      mul_pos hdeltaPos hdeltaComplementPos
    nlinarith [hproduct]
  have hdeltaSqLtOne : (1 - theta) ^ 2 < 1 := by
    linarith
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hcHalf : c < 1 / 2 := by
    dsimp [c]
    linarith
  have hboundaryGap : 0 < 1 - betaBoundary := by
    linarith
  have hbetaEq :
      beta = betaBoundary + c * (1 - betaBoundary) := by
    dsimp [beta, jointTwoHeightCubicStrictTargetExponent, c, betaBoundary]
  have hboundaryBeta : betaBoundary < beta := by
    rw [hbetaEq]
    have hpositive := mul_pos hcPos hboundaryGap
    linarith
  have hbetaMidpoint :
      beta < jointTwoHeightCanonicalStrictTargetExponent theta := by
    have hproduct :=
      mul_lt_mul_of_pos_right hcHalf hboundaryGap
    rw [hbetaEq]
    dsimp [jointTwoHeightCanonicalStrictTargetExponent, betaBoundary]
    linarith
  have hbetaOne : beta < 1 :=
    hbetaMidpoint.trans
      (jointTwoHeightCanonicalStrictTargetExponent_lt_one
        hthetaHalf hthetaOne)
  have hbetaLower : 2 / 3 < beta :=
    hboundaryLower.trans hboundaryBeta
  have hthetaBeta : theta < beta :=
    hthetaBoundary.trans hboundaryBeta
  have hstrictThreshold :
      theta < jointTwoHeightImprovedGlobalCapThreshold beta := by
    have hmono :=
      jointTwoHeightImprovedGlobalCapThreshold_strictMono
        hboundaryLower hboundaryBeta hbetaOne
    linarith
  exact
    ⟨hboundaryLower, hboundaryBeta, hbetaMidpoint, hbetaOne,
      hbetaLower, hthetaBoundary, hthetaBeta,
      hboundaryThreshold, hstrictThreshold⟩

theorem jointTwoHeightCubicStrictTargetExponent_lower
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    2 / 3 < jointTwoHeightCubicStrictTargetExponent theta :=
  (jointTwoHeightCubicStrictTargetExponent_spec
    hthetaHalf hthetaOne).2.2.2.2.1

theorem jointTwoHeightCubicStrictTargetExponent_lt_one
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    jointTwoHeightCubicStrictTargetExponent theta < 1 :=
  (jointTwoHeightCubicStrictTargetExponent_spec
    hthetaHalf hthetaOne).2.2.2.1

theorem theta_lt_jointTwoHeightCubicStrictTargetExponent
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    theta < jointTwoHeightCubicStrictTargetExponent theta :=
  (jointTwoHeightCubicStrictTargetExponent_spec
    hthetaHalf hthetaOne).2.2.2.2.2.2.1

theorem theta_lt_improvedThreshold_cubicStrictTargetExponent
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    theta <
      jointTwoHeightImprovedGlobalCapThreshold
        (jointTwoHeightCubicStrictTargetExponent theta) :=
  (jointTwoHeightCubicStrictTargetExponent_spec
    hthetaHalf hthetaOne).2.2.2.2.2.2.2.2

/-- The cubic strict target exceeds `theta` by
`(73 / 2) * (1 - theta)^3` to first order. -/
theorem tendsto_jointTwoHeightCubicStrictTargetExponent_cubicExcess :
    Tendsto
      (fun theta : ℝ =>
        (jointTwoHeightCubicStrictTargetExponent theta - theta) /
          (1 - theta) ^ 3)
      (𝓝[<] (1 : ℝ)) (𝓝 (73 / 2 : ℝ)) := by
  let betaBoundary := jointTwoHeightOptimalTargetExponent
  have hcubic :
      Tendsto
        (fun theta : ℝ =>
          (betaBoundary theta - theta) / (1 - theta) ^ 3)
        (𝓝[<] (1 : ℝ)) (𝓝 36) := by
    simpa [betaBoundary] using
      tendsto_jointTwoHeightOptimalTargetExponent_cubicExcess
  have hratio :
      Tendsto
        (fun theta : ℝ =>
          (1 - betaBoundary theta) / (1 - theta))
        (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    simpa [betaBoundary] using
      tendsto_jointTwoHeightOptimalTargetExponent_gapRatio_one
  have hhalf :
      Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
        (𝓝[<] (1 : ℝ)) (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun theta : ℝ =>
          (betaBoundary theta - theta) / (1 - theta) ^ 3 +
            (1 / 2 : ℝ) *
              ((1 - betaBoundary theta) / (1 - theta)))
        (𝓝[<] (1 : ℝ)) (𝓝 (73 / 2 : ℝ)) := by
    convert hcubic.add (hhalf.mul hratio) using 1 <;> norm_num
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with theta hthetaOne
  have hthetaLt : theta < 1 := by
    simpa only [mem_Iio] using hthetaOne
  have hne : 1 - theta ≠ 0 := by linarith
  dsimp [jointTwoHeightCubicStrictTargetExponent, betaBoundary]
  field_simp [hne]
  ring

end PrimeNumberTheorem
