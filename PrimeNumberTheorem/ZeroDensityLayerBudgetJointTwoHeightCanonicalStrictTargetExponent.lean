import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightUniqueOptimalTargetExponent

/-!
# Canonical strict target exponent

The unique inverse target exponent is the boundary where the global contour
gap closes.  Its midpoint with `1` gives a canonical strict target exponent
with positive improved-cap slack.
-/

namespace PrimeNumberTheorem

/-- Canonical strict target exponent halfway between the unique boundary
exponent and `1`. -/
noncomputable def jointTwoHeightCanonicalStrictTargetExponent
    (theta : ℝ) : ℝ :=
  (jointTwoHeightOptimalTargetExponent theta + 1) / 2

/-- Complete strict-feasibility specification of the canonical target
exponent. -/
theorem jointTwoHeightCanonicalStrictTargetExponent_spec
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    let betaBoundary := jointTwoHeightOptimalTargetExponent theta
    let beta := jointTwoHeightCanonicalStrictTargetExponent theta
    2 / 3 < betaBoundary ∧
      betaBoundary < beta ∧
      beta < 1 ∧
      2 / 3 < beta ∧
      theta < betaBoundary ∧
      theta < beta ∧
      jointTwoHeightImprovedGlobalCapThreshold betaBoundary = theta ∧
      theta < jointTwoHeightImprovedGlobalCapThreshold beta := by
  let betaBoundary := jointTwoHeightOptimalTargetExponent theta
  let beta := jointTwoHeightCanonicalStrictTargetExponent theta
  have hboundary :
      IsJointTwoHeightOptimalTargetExponent theta betaBoundary := by
    simpa [betaBoundary] using
      jointTwoHeightOptimalTargetExponent_spec hthetaHalf hthetaOne
  rcases hboundary with
    ⟨hboundaryLower, hboundaryOne, hboundaryEq⟩
  have hboundaryBeta : betaBoundary < beta := by
    dsimp [beta, jointTwoHeightCanonicalStrictTargetExponent]
    linarith
  have hbetaOne : beta < 1 := by
    dsimp [beta, jointTwoHeightCanonicalStrictTargetExponent]
    linarith
  have hbetaLower : 2 / 3 < beta :=
    hboundaryLower.trans hboundaryBeta
  have hthetaBoundary : theta < betaBoundary := by
    have hthresholdBeta :
        jointTwoHeightImprovedGlobalCapThreshold betaBoundary <
          betaBoundary :=
      (jointTwoHeightImprovedGlobalCapThreshold_spec
        hboundaryLower hboundaryOne).2
    linarith
  have hthetaBeta : theta < beta :=
    hthetaBoundary.trans hboundaryBeta
  have hstrictThreshold :
      theta < jointTwoHeightImprovedGlobalCapThreshold beta := by
    have hmono :=
      jointTwoHeightImprovedGlobalCapThreshold_strictMono
        hboundaryLower hboundaryBeta hbetaOne
    linarith
  exact
    ⟨hboundaryLower, hboundaryBeta, hbetaOne, hbetaLower,
      hthetaBoundary, hthetaBeta, hboundaryEq, hstrictThreshold⟩

theorem jointTwoHeightCanonicalStrictTargetExponent_lower
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    2 / 3 < jointTwoHeightCanonicalStrictTargetExponent theta :=
  (jointTwoHeightCanonicalStrictTargetExponent_spec
    hthetaHalf hthetaOne).2.2.2.1

theorem jointTwoHeightCanonicalStrictTargetExponent_lt_one
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    jointTwoHeightCanonicalStrictTargetExponent theta < 1 :=
  (jointTwoHeightCanonicalStrictTargetExponent_spec
    hthetaHalf hthetaOne).2.2.1

theorem theta_lt_jointTwoHeightCanonicalStrictTargetExponent
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    theta < jointTwoHeightCanonicalStrictTargetExponent theta :=
  (jointTwoHeightCanonicalStrictTargetExponent_spec
    hthetaHalf hthetaOne).2.2.2.2.2.1

theorem theta_lt_improvedThreshold_canonicalStrictTargetExponent
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    theta <
      jointTwoHeightImprovedGlobalCapThreshold
        (jointTwoHeightCanonicalStrictTargetExponent theta) :=
  (jointTwoHeightCanonicalStrictTargetExponent_spec
    hthetaHalf hthetaOne).2.2.2.2.2.2.2

end PrimeNumberTheorem
