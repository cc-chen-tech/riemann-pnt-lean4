import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonContourAutomaticDecay

namespace PrimeNumberTheorem

open Filter Topology

/-- The complete logarithmic Carlson gap forces the basic moving scale
`delta(m) * log m` to diverge. -/
theorem tendsto_delta_mul_log_of_quadraticLogPowerGap
    {delta : ℕ → ℝ}
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    Tendsto
      (fun m : ℕ => delta m * Real.log (m : ℝ))
      atTop atTop := by
  unfold IsCarlsonMovingQuadraticLogPowerGap at hgap
  have hlogOne :
      ∀ᶠ m : ℕ in atTop, 1 ≤ Real.log (m : ℝ) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  apply tendsto_atTop_mono' atTop ?_ hgap
  filter_upwards [hdelta, hlogOne] with m hdm hlogm
  have hdeltaOne : delta m ≤ 1 := hdm.2.trans (by norm_num)
  have hinvOne : 1 ≤ (delta m)⁻¹ :=
    (one_le_inv₀ hdm.1).2 hdeltaOne
  have hlogInv : 0 ≤ Real.log (delta m)⁻¹ :=
    Real.log_nonneg hinvOne
  have hlogLog : 0 ≤ Real.log (Real.log (m : ℝ)) :=
    Real.log_nonneg hlogm
  have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
    zero_le_one.trans hlogm
  nlinarith

/-- On `0 < delta ≤ 1/8`, Carlson's balanced cut is bounded below by
`3 * alpha * delta`. -/
theorem three_mul_alpha_mul_delta_le_carlsonMovingBalancedCut
    {alpha delta : ℝ}
    (halpha : 0 < alpha) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 8) :
    3 * alpha * delta ≤
      carlsonTwoHeightBalancedCut (1 - 2 * delta) alpha := by
  let q := carlsonTwoHeightDensityExponent (1 - 2 * delta)
  have hsigma : 1 / 2 < 1 - 2 * delta := by linarith
  have hsigmaOne : 1 - 2 * delta < 1 := by linarith
  have hqPos : 0 < q := by
    dsimp [q]
    exact carlsonTwoHeightDensityExponent_pos hsigma hsigmaOne
  have hqLower : 6 * delta ≤ q := by
    dsimp [q, carlsonTwoHeightDensityExponent]
    nlinarith
  have hqUpper : q ≤ 1 := by
    dsimp [q, carlsonTwoHeightDensityExponent]
    nlinarith
  have hdenPos : 0 < q + 1 := by linarith
  unfold carlsonTwoHeightBalancedCut
  change 3 * alpha * delta ≤ q * alpha / (q + 1)
  rw [le_div_iff₀ hdenPos]
  have hcore : 3 * delta * (q + 1) ≤ q := by
    calc
      3 * delta * (q + 1) ≤ 3 * delta * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 6 * delta := by ring
      _ ≤ q := hqLower
  have hscaled :=
    mul_le_mul_of_nonneg_left hcore halpha.le
  nlinarith

/-- The logarithm of the balanced intermediate polynomial height diverges
under the complete moving Carlson gap. -/
theorem tendsto_carlsonMovingBalancedCut_mul_log
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    Tendsto
      (fun m : ℕ =>
        carlsonMovingBalancedCut alpha delta m *
          Real.log (m : ℝ))
      atTop atTop := by
  have hdeltaLog :=
    tendsto_delta_mul_log_of_quadraticLogPowerGap hdelta hgap
  have hscaled :
      Tendsto
        (fun m : ℕ =>
          (3 * alpha) * (delta m * Real.log (m : ℝ)))
        atTop atTop :=
    hdeltaLog.const_mul_atTop (by positivity : 0 < 3 * alpha)
  apply tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [hdelta,
      (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop 0] with
      m hdm hlogm
  have hcut :=
    three_mul_alpha_mul_delta_le_carlsonMovingBalancedCut
      halpha hdm.1 hdm.2
  have hmul := mul_le_mul_of_nonneg_right hcut hlogm
  simpa [carlsonMovingBalancedCut, Function.comp_apply, mul_assoc] using hmul

end PrimeNumberTheorem
