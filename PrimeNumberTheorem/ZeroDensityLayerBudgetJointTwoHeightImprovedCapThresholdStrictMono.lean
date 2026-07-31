import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightCubicCapDeficitAsymptotic

/-!
# Strict monotonicity of the improved cap threshold

The explicit improved cap threshold increases strictly from `1 / 2` to `1`
as `beta` moves from `2 / 3` to `1`.  This prepares a unique inverse target
exponent for every prescribed cap in `(1 / 2, 1)`.
-/

namespace PrimeNumberTheorem

/-- The canonical Carlson density exponent strictly decreases for
`beta > 2 / 3`. -/
theorem jointTwoHeightCanonicalDensityExponent_strictAnti
    {beta₁ beta₂ : ℝ}
    (hbeta₁ : 2 / 3 < beta₁)
    (hbeta₁Beta₂ : beta₁ < beta₂) :
    jointTwoHeightCanonicalDensityExponent beta₂ <
      jointTwoHeightCanonicalDensityExponent beta₁ := by
  have hfactor :
      0 <
        (beta₂ - beta₁) *
          (9 * (beta₁ + beta₂) - 12) :=
    mul_pos (sub_pos.mpr hbeta₁Beta₂) (by linarith)
  unfold jointTwoHeightCanonicalDensityExponent
  nlinarith

/-- The improved global cap threshold is strictly increasing on
`(2 / 3, 1)`. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_strictMono
    {beta₁ beta₂ : ℝ}
    (hbeta₁ : 2 / 3 < beta₁)
    (hbeta₁Beta₂ : beta₁ < beta₂)
    (hbeta₂One : beta₂ < 1) :
    jointTwoHeightImprovedGlobalCapThreshold beta₁ <
      jointTwoHeightImprovedGlobalCapThreshold beta₂ := by
  let q₁ := jointTwoHeightCanonicalDensityExponent beta₁
  let q₂ := jointTwoHeightCanonicalDensityExponent beta₂
  have hbeta₁One : beta₁ < 1 :=
    hbeta₁Beta₂.trans hbeta₂One
  have hq₁ : 0 < q₁ := by
    dsimp [q₁, jointTwoHeightCanonicalDensityExponent]
    have hleft : 0 < 3 * beta₁ - 1 := by linarith
    have hright : 0 < 1 - beta₁ := sub_pos.mpr hbeta₁One
    positivity
  have hq₂ : 0 < q₂ := by
    have hbeta₂ : 2 / 3 < beta₂ :=
      hbeta₁.trans hbeta₁Beta₂
    dsimp [q₂, jointTwoHeightCanonicalDensityExponent]
    have hleft : 0 < 3 * beta₂ - 1 := by linarith
    have hright : 0 < 1 - beta₂ := sub_pos.mpr hbeta₂One
    positivity
  have hq₂q₁ : q₂ < q₁ := by
    simpa [q₁, q₂] using
      jointTwoHeightCanonicalDensityExponent_strictAnti
        hbeta₁ hbeta₁Beta₂
  have hden₁ : 0 < q₁ + 1 := by linarith
  have hden₂ : 0 < q₂ + 1 := by linarith
  have hfactor :
      0 < (q₁ - q₂) * (q₁ + q₂ + q₁ * q₂) :=
    mul_pos (sub_pos.mpr hq₂q₁) (by positivity)
  have hslope :
      q₂ ^ 2 / (q₂ + 1) < q₁ ^ 2 / (q₁ + 1) := by
    rw [div_lt_div_iff₀ hden₂ hden₁]
    nlinarith
  have hgap :
      1 - beta₂ < 1 - beta₁ := by
    linarith
  have hgap₂ : 0 < 1 - beta₂ :=
    sub_pos.mpr hbeta₂One
  have hslope₁ : 0 < q₁ ^ 2 / (q₁ + 1) :=
    div_pos (sq_pos_of_pos hq₁) hden₁
  have hdeficit :
      (1 - beta₂) * (q₂ ^ 2 / (q₂ + 1)) <
        (1 - beta₁) * (q₁ ^ 2 / (q₁ + 1)) :=
    (mul_lt_mul_of_pos_left hslope hgap₂).trans
      (mul_lt_mul_of_pos_right hgap hslope₁)
  rw [jointTwoHeightImprovedGlobalCapThreshold_explicit,
    jointTwoHeightImprovedGlobalCapThreshold_explicit]
  change
    beta₁ - (1 - beta₁) * (q₁ ^ 2 / (q₁ + 1)) <
      beta₂ - (1 - beta₂) * (q₂ ^ 2 / (q₂ + 1))
  linarith

@[simp]
theorem jointTwoHeightImprovedGlobalCapThreshold_twoThird :
    jointTwoHeightImprovedGlobalCapThreshold (2 / 3 : ℝ) =
      1 / 2 := by
  rw [jointTwoHeightImprovedGlobalCapThreshold_explicit]
  norm_num [jointTwoHeightCanonicalDensityExponent]

@[simp]
theorem jointTwoHeightImprovedGlobalCapThreshold_one :
    jointTwoHeightImprovedGlobalCapThreshold (1 : ℝ) = 1 := by
  rw [jointTwoHeightImprovedGlobalCapThreshold_explicit]
  norm_num [jointTwoHeightCanonicalDensityExponent]

/-- The improved threshold maps the target interval into the prescribed-cap
interval. -/
theorem jointTwoHeightImprovedGlobalCapThreshold_mem_Ioo
    {beta : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1) :
    1 / 2 < jointTwoHeightImprovedGlobalCapThreshold beta ∧
      jointTwoHeightImprovedGlobalCapThreshold beta < 1 := by
  rcases
      targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
        hbeta hbetaOne with
    ⟨hhalfCanonical, _hcanonicalBeta, _hcanonicalOne⟩
  rcases
      jointTwoHeightImprovedGlobalCapThreshold_spec
        hbeta hbetaOne with
    ⟨hcanonicalImproved, himprovedBeta⟩
  exact
    ⟨hhalfCanonical.trans hcanonicalImproved,
      himprovedBeta.trans hbetaOne⟩

end PrimeNumberTheorem
