import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightExactSigmaOptimizer

/-!
# Uniqueness of the optimal density threshold

The exact optimizer constructed by the balance polynomial is unique because
both the Carlson density exponent and its balanced slope strictly decrease
to the right of `1 / 2`.
-/

namespace PrimeNumberTheorem

/-- The Carlson density exponent strictly decreases to the right of
`1 / 2`. -/
theorem carlsonTwoHeightDensityExponent_strictAntiOn_half
    {sigma₁ sigma₂ : ℝ}
    (hhalf : 1 / 2 < sigma₁)
    (hlt : sigma₁ < sigma₂) :
    carlsonTwoHeightDensityExponent sigma₂ <
      carlsonTwoHeightDensityExponent sigma₁ := by
  have hproduct :
      0 < (sigma₂ - sigma₁) * (sigma₁ + sigma₂ - 1) :=
    mul_pos (sub_pos.mpr hlt) (by linarith)
  unfold carlsonTwoHeightDensityExponent
  nlinarith

/-- The balanced Carlson slope strictly decreases on `(1 / 2, 1)`. -/
theorem targetAmplitudeCarlsonTwoHeightBalancedSlope_strictAntiOn_half_one
    {sigma₁ sigma₂ : ℝ}
    (hhalf : 1 / 2 < sigma₁)
    (hlt : sigma₁ < sigma₂)
    (hone : sigma₂ < 1) :
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ <
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ := by
  let q₁ := carlsonTwoHeightDensityExponent sigma₁
  let q₂ := carlsonTwoHeightDensityExponent sigma₂
  have hsigma₁One : sigma₁ < 1 := hlt.trans hone
  have hsigma₂Half : 1 / 2 < sigma₂ := hhalf.trans hlt
  have hq₁ : 0 < q₁ := by
    simpa [q₁] using
      carlsonTwoHeightDensityExponent_pos hhalf hsigma₁One
  have hq₂ : 0 < q₂ := by
    simpa [q₂] using
      carlsonTwoHeightDensityExponent_pos hsigma₂Half hone
  have hq₂q₁ : q₂ < q₁ := by
    simpa [q₁, q₂] using
      carlsonTwoHeightDensityExponent_strictAntiOn_half hhalf hlt
  have hden₁ : 0 < q₁ + 1 := by linarith
  have hden₂ : 0 < q₂ + 1 := by linarith
  have hfactor :
      0 < (q₁ - q₂) * (q₁ + q₂ + q₁ * q₂) :=
    mul_pos (sub_pos.mpr hq₂q₁)
      (by positivity)
  unfold targetAmplitudeCarlsonTwoHeightBalancedSlope
  change q₂ ^ 2 / (q₂ + 1) < q₁ ^ 2 / (q₁ + 1)
  rw [div_lt_div_iff₀ hden₂ hden₁]
  nlinarith

/-- Two balancing thresholds for the same `beta` and `theta` coincide. -/
theorem IsJointTwoHeightSigmaOptimizer.unique
    {beta theta sigma₁ sigma₂ : ℝ}
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1)
    (hoptimizer₁ :
      IsJointTwoHeightSigmaOptimizer beta theta sigma₁)
    (hoptimizer₂ :
      IsJointTwoHeightSigmaOptimizer beta theta sigma₂) :
    sigma₁ = sigma₂ := by
  rcases hoptimizer₁ with
    ⟨hsigma₁Half, hsigma₁Theta, hbalance₁⟩
  rcases hoptimizer₂ with
    ⟨hsigma₂Half, hsigma₂Theta, hbalance₂⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsigma₂One : sigma₂ < 1 :=
      hsigma₂Theta.trans (hthetaBeta.trans hbetaOne)
    have hslope :
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ <
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ :=
      targetAmplitudeCarlsonTwoHeightBalancedSlope_strictAntiOn_half_one
        hsigma₁Half hlt hsigma₂One
    have hbetaSigma₂ : 0 < beta - sigma₂ := by
      linarith
    have hbetaSigma :
        beta - sigma₂ < beta - sigma₁ := by
      linarith
    have hslope₁Pos :
        0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ :=
      targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
        hsigma₁Half
        (hsigma₁Theta.trans (hthetaBeta.trans hbetaOne))
    have hproduct :
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ *
            (beta - sigma₂) <
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ *
            (beta - sigma₁) :=
      (mul_lt_mul_of_pos_right hslope hbetaSigma₂).trans
        (mul_lt_mul_of_pos_left hbetaSigma hslope₁Pos)
    nlinarith
  · have hsigma₁One : sigma₁ < 1 :=
      hsigma₁Theta.trans (hthetaBeta.trans hbetaOne)
    have hslope :
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ <
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ :=
      targetAmplitudeCarlsonTwoHeightBalancedSlope_strictAntiOn_half_one
        hsigma₂Half hgt hsigma₁One
    have hbetaSigma₁ : 0 < beta - sigma₁ := by
      linarith
    have hbetaSigma :
        beta - sigma₁ < beta - sigma₂ := by
      linarith
    have hslope₂Pos :
        0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ :=
      targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
        hsigma₂Half
        (hsigma₂Theta.trans (hthetaBeta.trans hbetaOne))
    have hproduct :
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₁ *
            (beta - sigma₁) <
          targetAmplitudeCarlsonTwoHeightBalancedSlope sigma₂ *
            (beta - sigma₂) :=
      (mul_lt_mul_of_pos_right hslope hbetaSigma₁).trans
        (mul_lt_mul_of_pos_left hbetaSigma hslope₂Pos)
    nlinarith

/-- For every prescribed cap strictly between `1 / 2` and `beta < 1`, there
exists exactly one balancing, hence globally optimal, density threshold. -/
theorem existsUnique_jointTwoHeightSigmaOptimizer
    {beta theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaBeta : theta < beta)
    (hbetaOne : beta < 1) :
    ∃! sigma : ℝ, IsJointTwoHeightSigmaOptimizer beta theta sigma := by
  rcases
      exists_jointTwoHeightSigmaOptimizer
        hthetaHalf hthetaBeta hbetaOne with
    ⟨sigma, hoptimizer⟩
  refine ⟨sigma, hoptimizer, ?_⟩
  intro sigma' hoptimizer'
  exact
    (IsJointTwoHeightSigmaOptimizer.unique
      hthetaBeta hbetaOne hoptimizer hoptimizer').symm

end PrimeNumberTheorem
