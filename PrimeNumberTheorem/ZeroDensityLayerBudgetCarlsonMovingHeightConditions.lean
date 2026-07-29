import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingHeightScale

namespace PrimeNumberTheorem

open Filter Topology

/-- A moving polynomial height diverges when its logarithmic exponent
`gamma(m) * log m` diverges. -/
theorem tendsto_movingPolynomialHeight_atTop
    {gamma : ℕ → ℝ}
    (hlogHeight :
      Tendsto
        (fun m : ℕ => gamma m * Real.log (m : ℝ))
        atTop atTop) :
    Tendsto
      (fun m : ℕ => carlsonPolynomialHeight (gamma m) (m : ℝ))
      atTop atTop := by
  have hexp :
      Tendsto
        (fun m : ℕ =>
          Real.exp (gamma m * Real.log (m : ℝ)))
        atTop atTop :=
    Real.tendsto_exp_atTop.comp hlogHeight
  apply hexp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hmPos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  unfold carlsonPolynomialHeight
  rw [Real.rpow_def_of_pos hmPos]
  congr 1
  ring

/-- The logarithm of a moving polynomial height agrees eventually with its
defining exponent. -/
theorem tendsto_log_movingPolynomialHeight_atTop
    {gamma : ℕ → ℝ}
    (hlogHeight :
      Tendsto
        (fun m : ℕ => gamma m * Real.log (m : ℝ))
        atTop atTop) :
    Tendsto
      (fun m : ℕ =>
        Real.log (carlsonPolynomialHeight (gamma m) (m : ℝ)))
      atTop atTop := by
  apply hlogHeight.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hmPos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  unfold carlsonPolynomialHeight
  rw [Real.log_rpow hmPos]

/-- Cofinality of a height and its logarithm, together with the elementary
moving-line margins, supplies every explicit Carlson pointwise condition. -/
theorem eventually_carlsonPointwiseHeightConditions_of_tendsto
    {C₁ C₂ : ℝ} {sigma T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop)
    (hlogT : Tendsto (fun m => Real.log (T m)) atTop atTop)
    (hgap : ∀ᶠ m : ℕ in atTop,
      1 / 4 ≤ sigma m - 1 / 2)
    (hexponent : ∀ᶠ m : ℕ in atTop,
      0 ≤ 2 * sigma m - 1) :
    ∀ᶠ m : ℕ in atTop,
      CarlsonPointwiseHeightConditions C₁ C₂ (sigma m) (T m) := by
  filter_upwards
      [hT.eventually_ge_atTop 6,
        hT.eventually_ge_atTop C₁,
        hT.eventually_ge_atTop C₂,
        hlogT.eventually_ge_atTop 17,
        hgap, hexponent] with
      m hT6 hC₁T hC₂T hlog17 hgapm hexponentm
  have hlogPos : 0 < Real.log (T m) := by linarith
  have hsmall : 4 / Real.log (T m) < 1 / 4 := by
    rw [div_lt_iff₀ hlogPos]
    nlinarith
  have hTOne : 1 ≤ T m := by linarith
  exact
    ⟨hT6, by linarith, hsmall.trans_le hgapm,
      Real.one_le_rpow hTOne hexponentm, hC₁T, hC₂T⟩

/-- The balanced intermediate height automatically satisfies Carlson's
pointwise parameter conditions under the complete logarithmic gap. -/
theorem eventually_balancedCarlsonPointwiseHeightConditions
    {C₁ C₂ alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    ∀ᶠ m : ℕ in atTop,
      CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta m)
        (carlsonPolynomialHeight
          (carlsonMovingBalancedCut alpha delta m) (m : ℝ)) := by
  have hlogHeight :=
    tendsto_carlsonMovingBalancedCut_mul_log halpha hdelta hgap
  apply eventually_carlsonPointwiseHeightConditions_of_tendsto
    (tendsto_movingPolynomialHeight_atTop hlogHeight)
    (tendsto_log_movingPolynomialHeight_atTop hlogHeight)
  · filter_upwards [hdelta] with m hm
    linarith
  · filter_upwards [hdelta] with m hm
    linarith

/-- The final fixed positive polynomial height automatically satisfies the
same moving Carlson conditions. -/
theorem eventually_fixedCarlsonPointwiseHeightConditions
    {C₁ C₂ alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8) :
    ∀ᶠ m : ℕ in atTop,
      CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta m)
        (carlsonPolynomialHeight alpha (m : ℝ)) := by
  have hlogNat :
      Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogHeight :
      Tendsto
        (fun m : ℕ => alpha * Real.log (m : ℝ))
        atTop atTop :=
    hlogNat.const_mul_atTop halpha
  let gamma : ℕ → ℝ := fun _ => alpha
  have hheight :
      Tendsto
        (fun m : ℕ =>
          carlsonPolynomialHeight (gamma m) (m : ℝ))
        atTop atTop :=
    tendsto_movingPolynomialHeight_atTop hlogHeight
  have hheightLog :
      Tendsto
        (fun m : ℕ =>
          Real.log (carlsonPolynomialHeight (gamma m) (m : ℝ)))
        atTop atTop :=
    tendsto_log_movingPolynomialHeight_atTop hlogHeight
  apply eventually_carlsonPointwiseHeightConditions_of_tendsto
    (by simpa [gamma] using hheight)
    (by simpa [gamma] using hheightLog)
  · filter_upwards [hdelta] with m hm
    linarith
  · filter_upwards [hdelta] with m hm
    linarith

end PrimeNumberTheorem
