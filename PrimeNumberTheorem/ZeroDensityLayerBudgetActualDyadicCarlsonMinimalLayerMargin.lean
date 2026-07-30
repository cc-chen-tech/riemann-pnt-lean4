import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDyadicCarlsonMinimalLayers

/-!
# Margin cost of the minimal dyadic Carlson layer schedule

The elementary inequality `L + 1 <= 2 ^ L`, combined with the minimal-layer
outer bound `2 ^ L * delta <= 1 / 4`, gives

`log (L + 1) <= log (delta⁻¹)`.

Consequently the dynamic number of dyadic strips costs only one additional
copy of `log (delta⁻¹)` in the Carlson logarithmic margin.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- A real-valued form of the elementary binary growth bound. -/
theorem natCast_add_one_le_two_pow (L : ℕ) :
    (L : ℝ) + 1 ≤ (2 : ℝ) ^ L := by
  induction L with
  | zero =>
      norm_num
  | succ L ih =>
      rw [Nat.cast_succ, pow_succ]
      have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
      nlinarith

/-- The minimal dyadic layer count is at most the reciprocal gap, in the
precise form needed under a logarithm. -/
theorem dyadicCarlsonLayerCount_add_one_le_inv
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 8) :
    (dyadicCarlsonLayerCount delta : ℝ) + 1 ≤ delta⁻¹ := by
  have hcount :
      (dyadicCarlsonLayerCount delta : ℝ) + 1 ≤
        (2 : ℝ) ^ (dyadicCarlsonLayerCount delta) :=
    natCast_add_one_le_two_pow _
  have houter :
      (2 : ℝ) ^ (dyadicCarlsonLayerCount delta) * delta ≤
        1 / 4 :=
    dyadicCarlsonLayerCount_outer_le_quarter hdelta hdeltaUpper
  have hpowInv :
      (2 : ℝ) ^ (dyadicCarlsonLayerCount delta) ≤ delta⁻¹ := by
    calc
      (2 : ℝ) ^ (dyadicCarlsonLayerCount delta) ≤
          (1 / 4 : ℝ) / delta :=
        (le_div_iff₀ hdelta).2 houter
      _ ≤ delta⁻¹ := by
        rw [div_eq_mul_inv]
        have hinv : 0 ≤ delta⁻¹ := inv_nonneg.mpr hdelta.le
        nlinarith
  exact hcount.trans hpowInv

/-- The exact logarithmic price of the minimal dyadic layer schedule is
bounded by one reciprocal-gap logarithm. -/
theorem carlsonDynamicMinimalLayerCountLogCost_le
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 8) :
    Real.log ((dyadicCarlsonLayerCount delta : ℝ) + 1) ≤
      Real.log delta⁻¹ := by
  exact Real.log_le_log (by positivity)
    (dyadicCarlsonLayerCount_add_one_le_inv hdelta hdeltaUpper)

/-- Single-scale margin strong enough to pay for the automatically selected
minimal dyadic layer count. -/
def IsCarlsonMovingDyadicLogPowerGap (delta : ℕ → ℝ) : Prop :=
  Tendsto
    (fun m =>
      delta m / 2 * Real.log (m : ℝ) -
        3 * Real.log (delta m)⁻¹ -
        4 * Real.log (Real.log (m : ℝ)))
    atTop atTop

/-- The third reciprocal-gap logarithm exactly absorbs the dynamic layer
count. -/
theorem isCarlsonMovingQuadraticLogPowerLayerCountGap_minimalSchedule
    {delta : ℕ → ℝ}
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    IsCarlsonMovingQuadraticLogPowerLayerCountGap delta
      (dyadicCarlsonLayerSchedule delta) := by
  unfold IsCarlsonMovingDyadicLogPowerGap at hgap
  unfold IsCarlsonMovingQuadraticLogPowerLayerCountGap
  apply tendsto_atTop_mono' atTop ?_ hgap
  filter_upwards [hdelta, hdeltaUpper] with m hm hmUpper
  have hcost :
      carlsonDynamicLayerCountLogCost
          (dyadicCarlsonLayerSchedule delta) m ≤
        Real.log (delta m)⁻¹ := by
    unfold carlsonDynamicLayerCountLogCost
      dyadicCarlsonLayerSchedule
    exact carlsonDynamicMinimalLayerCountLogCost_le hm hmUpper
  linarith

/-- Minimal-layer fixed-anchor transfer with the layer-count margin reduced
to a single explicit moving-gap condition. -/
theorem exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero_of_margin
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (halphaUpper : alpha ≤ 1 / 16)
    (hdeltaNonneg : ∀ m, 0 ≤ delta m)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    ∃ A C₁ C₂ : ℝ,
      0 ≤ A ∧
      1 ≤ C₁ ∧
      1 ≤ C₂ ∧
      (ActualDynamicCarlsonGapFamilyHeightConditions C₁ C₂ alpha
          (dyadicCarlsonLayerSchedule delta) (dyadicCarlsonGap delta) →
        Tendsto
          (actualDyadicCarlsonFixedAnchorMass alpha delta
            (dyadicCarlsonLayerSchedule delta))
          atTop (𝓝 0)) := by
  exact
    exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero
      halpha halphaUpper hdeltaNonneg hdelta hdeltaUpper
      (isCarlsonMovingQuadraticLogPowerLayerCountGap_minimalSchedule
        hdelta hdeltaUpper hgap)

end

end PrimeNumberTheorem
