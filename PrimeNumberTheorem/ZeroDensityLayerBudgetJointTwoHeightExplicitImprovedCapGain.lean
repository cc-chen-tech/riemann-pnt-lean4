import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightImprovedGlobalCapThreshold

/-!
# Explicit gain in the improved global cap threshold

The improved real-part cap threshold is reduced to a rational expression in
`beta`.  Its strict gain over the old canonical threshold is factored into
positive terms, giving a quantitative certificate of the optimization gain.
-/

namespace PrimeNumberTheorem

/-- Carlson density exponent evaluated at the canonical density threshold,
written directly as a polynomial in `beta`. -/
noncomputable def jointTwoHeightCanonicalDensityExponent
    (beta : ℝ) : ℝ :=
  3 * (3 * beta - 1) * (1 - beta)

theorem carlsonTwoHeightDensityExponent_canonical
    (beta : ℝ) :
    carlsonTwoHeightDensityExponent
        (targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) =
      jointTwoHeightCanonicalDensityExponent beta := by
  unfold carlsonTwoHeightDensityExponent
    targetAmplitudeCarlsonTwoHeightCanonicalThreshold
    jointTwoHeightCanonicalDensityExponent
  ring

/-- Closed rational formula for the globally improved cap threshold. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_explicit
    (beta : ℝ) :
    jointTwoHeightImprovedGlobalCapThreshold beta =
      beta -
        (1 - beta) *
          (jointTwoHeightCanonicalDensityExponent beta ^ 2 /
            (jointTwoHeightCanonicalDensityExponent beta + 1)) := by
  unfold jointTwoHeightImprovedGlobalCapThreshold
    jointTwoHeightSigmaBalanceValue
    targetAmplitudeCarlsonTwoHeightBalancedSlope
  rw [carlsonTwoHeightDensityExponent_canonical]
  unfold targetAmplitudeCarlsonTwoHeightCanonicalThreshold
  ring

/-- Exact positive-factor formula for the gain over the old canonical cap
threshold. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_gain_eq
    {beta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    jointTwoHeightImprovedGlobalCapThreshold beta -
        targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta =
      (1 - beta) *
        (1 - jointTwoHeightCanonicalDensityExponent beta) *
        (2 * jointTwoHeightCanonicalDensityExponent beta + 1) /
        (2 * (jointTwoHeightCanonicalDensityExponent beta + 1)) := by
  let c := targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta
  let q := jointTwoHeightCanonicalDensityExponent beta
  rcases
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
        hbeta hbetaOne with
    ⟨hcHalf, _hcBeta, hcOne⟩
  have hqPos : 0 < q := by
    have hpositive :=
      carlsonTwoHeightDensityExponent_pos hcHalf hcOne
    rw [carlsonTwoHeightDensityExponent_canonical] at hpositive
    simpa [q] using hpositive
  have hden : q + 1 ≠ 0 := by linarith
  rw [jointTwoHeightImprovedGlobalCapThreshold_explicit]
  change
    beta - (1 - beta) * (q ^ 2 / (q + 1)) - c =
      (1 - beta) * (1 - q) * (2 * q + 1) /
        (2 * (q + 1))
  dsimp [c]
  unfold targetAmplitudeCarlsonTwoHeightCanonicalThreshold
  field_simp [hden]
  ring

/-- Relative fraction of the canonical-to-`beta` cap gap recovered by global
density-threshold optimization. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_relativeGain_eq
    {beta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    (jointTwoHeightImprovedGlobalCapThreshold beta -
        targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) /
        (beta -
          targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) =
      (1 - jointTwoHeightCanonicalDensityExponent beta) *
        (2 * jointTwoHeightCanonicalDensityExponent beta + 1) /
        (jointTwoHeightCanonicalDensityExponent beta + 1) := by
  let c := targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta
  let q := jointTwoHeightCanonicalDensityExponent beta
  rcases
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
        hbeta hbetaOne with
    ⟨hcHalf, _hcBeta, hcOne⟩
  have hqPos : 0 < q := by
    have hpositive :=
      carlsonTwoHeightDensityExponent_pos hcHalf hcOne
    rw [carlsonTwoHeightDensityExponent_canonical] at hpositive
    simpa [q] using hpositive
  have hqDen : q + 1 ≠ 0 := by linarith
  have honeMinus : 1 - beta ≠ 0 :=
    (sub_pos.mpr hbetaOne).ne'
  rw [jointTwoHeightImprovedGlobalCapThreshold_gain_eq
    hbeta hbetaOne]
  have hgapEq : beta - c = (1 - beta) / 2 := by
    dsimp [c]
    unfold targetAmplitudeCarlsonTwoHeightCanonicalThreshold
    ring
  rw [hgapEq]
  change
    ((1 - beta) * (1 - q) * (2 * q + 1) /
        (2 * (q + 1))) /
        ((1 - beta) / 2) =
      (1 - q) * (2 * q + 1) / (q + 1)
  field_simp [hqDen, honeMinus]

/-- The recovered fraction is strictly between zero and one. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_relativeGain_mem_Ioo
    {beta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    0 <
        (jointTwoHeightImprovedGlobalCapThreshold beta -
          targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) /
          (beta -
            targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) ∧
      (jointTwoHeightImprovedGlobalCapThreshold beta -
          targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) /
          (beta -
            targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) < 1 := by
  rcases
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
        hbeta hbetaOne with
    ⟨_hcHalf, hcBeta, _hcOne⟩
  rcases
      jointTwoHeightImprovedGlobalCapThreshold_spec
        hbeta hbetaOne with
    ⟨hcanonicalImproved, himprovedBeta⟩
  have hden :
      0 <
        beta -
          targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta :=
    sub_pos.mpr hcBeta
  have hnum :
      0 <
        jointTwoHeightImprovedGlobalCapThreshold beta -
          targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta :=
    sub_pos.mpr hcanonicalImproved
  constructor
  · exact div_pos hnum hden
  · rw [div_lt_one hden]
    linarith

end PrimeNumberTheorem
