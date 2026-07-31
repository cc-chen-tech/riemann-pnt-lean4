import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightExplicitImprovedCapGain

/-!
# Cubic asymptotic of the improved cap deficit

As `beta` tends to one from below, the globally improved cap threshold lies
at cubic rather than linear distance from `beta`.  The normalized cubic
deficit tends to the explicit constant `36`.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

/-- Exact cubic normalization of the improved cap deficit. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_cubicDeficit_eq
    {beta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    (beta - jointTwoHeightImprovedGlobalCapThreshold beta) /
        (1 - beta) ^ 3 =
      9 * (3 * beta - 1) ^ 2 /
        (jointTwoHeightCanonicalDensityExponent beta + 1) := by
  let q := jointTwoHeightCanonicalDensityExponent beta
  have honeMinus : 1 - beta ≠ 0 :=
    (sub_pos.mpr hbetaOne).ne'
  have hqPos : 0 < q := by
    have hpositive :=
      carlsonTwoHeightDensityExponent_pos
        (targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
          hbeta hbetaOne).1
        (targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
          hbeta hbetaOne).2.2
    rw [carlsonTwoHeightDensityExponent_canonical] at hpositive
    simpa [q] using hpositive
  have hqDen : q + 1 ≠ 0 := by
    linarith
  rw [jointTwoHeightImprovedGlobalCapThreshold_explicit]
  rw [show
    beta -
        (beta -
          (1 - beta) *
            (jointTwoHeightCanonicalDensityExponent beta ^ 2 /
              (jointTwoHeightCanonicalDensityExponent beta + 1))) =
      (1 - beta) *
        (jointTwoHeightCanonicalDensityExponent beta ^ 2 /
          (jointTwoHeightCanonicalDensityExponent beta + 1)) by
    ring]
  change
    ((1 - beta) * (q ^ 2 / (q + 1))) / (1 - beta) ^ 3 =
      9 * (3 * beta - 1) ^ 2 / (q + 1)
  field_simp [honeMinus, hqDen]
  dsimp [q, jointTwoHeightCanonicalDensityExponent]
  ring

/-- Exact ratio between the new cubic deficit and the old canonical linear
deficit. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_deficitRatio_eq
    {beta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    (beta - jointTwoHeightImprovedGlobalCapThreshold beta) /
        (beta -
          targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta) =
      2 * jointTwoHeightCanonicalDensityExponent beta ^ 2 /
        (jointTwoHeightCanonicalDensityExponent beta + 1) := by
  let q := jointTwoHeightCanonicalDensityExponent beta
  have honeMinus : 1 - beta ≠ 0 :=
    (sub_pos.mpr hbetaOne).ne'
  have hqPos : 0 < q := by
    have hpositive :=
      carlsonTwoHeightDensityExponent_pos
        (targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
          hbeta hbetaOne).1
        (targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
          hbeta hbetaOne).2.2
    rw [carlsonTwoHeightDensityExponent_canonical] at hpositive
    simpa [q] using hpositive
  have hqDen : q + 1 ≠ 0 := by
    linarith
  rw [jointTwoHeightImprovedGlobalCapThreshold_explicit]
  rw [show
    beta -
        (beta -
          (1 - beta) *
            (jointTwoHeightCanonicalDensityExponent beta ^ 2 /
              (jointTwoHeightCanonicalDensityExponent beta + 1))) =
      (1 - beta) *
        (jointTwoHeightCanonicalDensityExponent beta ^ 2 /
          (jointTwoHeightCanonicalDensityExponent beta + 1)) by
    ring]
  have hgapEq :
      beta -
          targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta =
        (1 - beta) / 2 := by
    unfold targetAmplitudeCarlsonTwoHeightCanonicalThreshold
    ring
  rw [hgapEq]
  change
    ((1 - beta) * (q ^ 2 / (q + 1))) /
        ((1 - beta) / 2) =
      2 * q ^ 2 / (q + 1)
  field_simp [honeMinus, hqDen]

/-- The improved cap deficit is asymptotic to
`36 * (1 - beta)^3` as `beta -> 1-`. -/
theorem tendsto_jointTwoHeightImprovedGlobalCapThreshold_cubicDeficit :
    Tendsto
      (fun beta : ℝ =>
        (beta - jointTwoHeightImprovedGlobalCapThreshold beta) /
          (1 - beta) ^ 3)
      (𝓝[<] (1 : ℝ)) (𝓝 36) := by
  let rational :=
    fun beta : ℝ =>
      9 * (3 * beta - 1) ^ 2 /
        (jointTwoHeightCanonicalDensityExponent beta + 1)
  have hcontinuous : ContinuousAt rational 1 := by
    apply ContinuousAt.div
    · fun_prop
    · unfold jointTwoHeightCanonicalDensityExponent
      fun_prop
    · norm_num [jointTwoHeightCanonicalDensityExponent]
  have hrational :
      Tendsto rational (𝓝[<] (1 : ℝ)) (𝓝 36) := by
    have hrestricted :
        Tendsto rational (𝓝[<] (1 : ℝ)) (𝓝 (rational 1)) :=
      hcontinuous.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from inf_le_left)
    have hvalue : rational 1 = 36 := by
      norm_num [rational, jointTwoHeightCanonicalDensityExponent]
    simpa only [hvalue] using hrestricted
  have hbetaLower :
      ∀ᶠ beta : ℝ in 𝓝[<] (1 : ℝ), 2 / 3 < beta :=
    (eventually_gt_nhds (by norm_num : (2 / 3 : ℝ) < 1)).filter_mono
      inf_le_left
  have hbetaUpper :
      ∀ᶠ beta : ℝ in 𝓝[<] (1 : ℝ), beta < 1 :=
    self_mem_nhdsWithin
  apply hrational.congr'
  filter_upwards [hbetaLower, hbetaUpper] with beta hbeta hbetaOne
  symm
  exact
    jointTwoHeightImprovedGlobalCapThreshold_cubicDeficit_eq
      hbeta hbetaOne

/-- Relative to the old canonical linear deficit, the globally improved
deficit tends to zero. -/
theorem tendsto_jointTwoHeightImprovedGlobalCapThreshold_deficitRatio_zero :
    Tendsto
      (fun beta : ℝ =>
        (beta - jointTwoHeightImprovedGlobalCapThreshold beta) /
          (beta -
            targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  let rational :=
    fun beta : ℝ =>
      2 * jointTwoHeightCanonicalDensityExponent beta ^ 2 /
        (jointTwoHeightCanonicalDensityExponent beta + 1)
  have hcontinuous : ContinuousAt rational 1 := by
    apply ContinuousAt.div
    · unfold jointTwoHeightCanonicalDensityExponent
      fun_prop
    · unfold jointTwoHeightCanonicalDensityExponent
      fun_prop
    · norm_num [jointTwoHeightCanonicalDensityExponent]
  have hrational :
      Tendsto rational (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hrestricted :
        Tendsto rational (𝓝[<] (1 : ℝ)) (𝓝 (rational 1)) :=
      hcontinuous.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from inf_le_left)
    have hvalue : rational 1 = 0 := by
      norm_num [rational, jointTwoHeightCanonicalDensityExponent]
    simpa only [hvalue] using hrestricted
  have hbetaLower :
      ∀ᶠ beta : ℝ in 𝓝[<] (1 : ℝ), 2 / 3 < beta :=
    (eventually_gt_nhds (by norm_num : (2 / 3 : ℝ) < 1)).filter_mono
      inf_le_left
  have hbetaUpper :
      ∀ᶠ beta : ℝ in 𝓝[<] (1 : ℝ), beta < 1 :=
    self_mem_nhdsWithin
  apply hrational.congr'
  filter_upwards [hbetaLower, hbetaUpper] with beta hbeta hbetaOne
  symm
  exact
    jointTwoHeightImprovedGlobalCapThreshold_deficitRatio_eq
      hbeta hbetaOne

end PrimeNumberTheorem
