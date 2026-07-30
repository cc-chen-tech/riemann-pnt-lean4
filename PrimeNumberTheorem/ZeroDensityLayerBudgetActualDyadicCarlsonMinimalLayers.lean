import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDyadicCarlsonFixedAnchor

/-!
# Minimal dyadic layer count for the Carlson fixed-anchor cover

For `0 < delta <= 1 / 8`, choose the least `L` such that

`1 / 8 <= 2 ^ L * delta`.

Minimality forces the matching upper bound `2 ^ L * delta <= 1 / 4`.
Thus the fixed-anchor scale sandwich is generated automatically rather than
supplied as an external layer schedule.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

theorem exists_dyadicCarlsonLayerCount
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ L : ℕ, (1 / 8 : ℝ) ≤ (2 : ℝ) ^ L * delta := by
  have hpow :
      Tendsto (fun L : ℕ => (2 : ℝ) ^ L) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hexists :
      ∃ L : ℕ, (1 / 8 : ℝ) / delta ≤ (2 : ℝ) ^ L :=
    (hpow.eventually
      (eventually_ge_atTop ((1 / 8 : ℝ) / delta))).exists
  obtain ⟨L, hL⟩ := hexists
  refine ⟨L, ?_⟩
  calc
    (1 / 8 : ℝ) = ((1 / 8 : ℝ) / delta) * delta := by
      field_simp
    _ ≤ (2 : ℝ) ^ L * delta :=
      mul_le_mul_of_nonneg_right hL hdelta.le

/-- Least dyadic layer count whose outer scale reaches `1 / 8`.  It is set
to zero outside the positive-gap regime. -/
noncomputable def dyadicCarlsonLayerCount (delta : ℝ) : ℕ :=
  if hdelta : 0 < delta then
    Nat.find (exists_dyadicCarlsonLayerCount hdelta)
  else
    0

theorem dyadicCarlsonLayerCount_spec
    {delta : ℝ} (hdelta : 0 < delta) :
    (1 / 8 : ℝ) ≤
      (2 : ℝ) ^ (dyadicCarlsonLayerCount delta) * delta := by
  rw [dyadicCarlsonLayerCount, dif_pos hdelta]
  exact Nat.find_spec (exists_dyadicCarlsonLayerCount hdelta)

theorem dyadicCarlsonLayerCount_min
    {delta : ℝ} (hdelta : 0 < delta) {n : ℕ}
    (hn : n < dyadicCarlsonLayerCount delta) :
    ¬(1 / 8 : ℝ) ≤ (2 : ℝ) ^ n * delta := by
  rw [dyadicCarlsonLayerCount, dif_pos hdelta] at hn
  exact Nat.find_min (exists_dyadicCarlsonLayerCount hdelta) hn

/-- Minimality loses at most one factor of two. -/
theorem dyadicCarlsonLayerCount_outer_le_quarter
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 8) :
    (2 : ℝ) ^ (dyadicCarlsonLayerCount delta) * delta ≤ 1 / 4 := by
  by_cases hzero : dyadicCarlsonLayerCount delta = 0
  · simpa [hzero] using hdeltaUpper.trans (by norm_num)
  · obtain ⟨n, hn⟩ :=
      Nat.exists_eq_succ_of_ne_zero hzero
    have hnlt : n < dyadicCarlsonLayerCount delta := by
      rw [hn]
      exact Nat.lt_succ_self n
    have hprevious :
        (2 : ℝ) ^ n * delta < 1 / 8 :=
      lt_of_not_ge (dyadicCarlsonLayerCount_min hdelta hnlt)
    rw [hn, pow_succ]
    nlinarith

/-- Pointwise minimal-layer schedule attached to a moving gap. -/
noncomputable def dyadicCarlsonLayerSchedule
    (delta : ℕ → ℝ) (m : ℕ) : ℕ :=
  dyadicCarlsonLayerCount (delta m)

theorem dyadicCarlsonLayerSchedule_scale
    {delta : ℕ → ℝ} {m : ℕ}
    (hdelta : 0 < delta m)
    (hdeltaUpper : delta m ≤ 1 / 8) :
    (1 / 8 : ℝ) ≤
        (2 : ℝ) ^ (dyadicCarlsonLayerSchedule delta m) * delta m ∧
      (2 : ℝ) ^ (dyadicCarlsonLayerSchedule delta m) * delta m ≤
        1 / 4 := by
  exact ⟨dyadicCarlsonLayerCount_spec hdelta,
    dyadicCarlsonLayerCount_outer_le_quarter hdelta hdeltaUpper⟩

theorem eventually_dyadicCarlsonLayerSchedule_scale
    {delta : ℕ → ℝ}
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8) :
    ∀ᶠ m : ℕ in atTop,
      (1 / 8 : ℝ) ≤
          (2 : ℝ) ^ (dyadicCarlsonLayerSchedule delta m) * delta m ∧
        (2 : ℝ) ^ (dyadicCarlsonLayerSchedule delta m) * delta m ≤
          1 / 4 := by
  filter_upwards [hdelta, hdeltaUpper] with m hm hmUpper
  exact dyadicCarlsonLayerSchedule_scale hm hmUpper

/-- Any actual positive zeta zero in the fixed anchor window is captured by
the automatically selected minimal dyadic layers. -/
theorem mem_actualDyadicCarlsonMinimalFixedAnchorWindow
    {alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ} {rho : ℂ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im)
    (himHeight : rho.im ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hdelta : 0 < delta m)
    (hreAnchor : (7 / 8 : ℝ) < rho.re)
    (hreUpper : rho.re ≤ 1 - delta m) :
    rho ∈ actualDyadicCarlsonFixedAnchorWindow alpha delta
      (dyadicCarlsonLayerSchedule delta) m := by
  exact mem_actualDyadicCarlsonFixedAnchorWindow
    hzero him himHeight (dyadicCarlsonLayerCount_spec hdelta)
      hreAnchor hreUpper

/-- Fully scheduled fixed-anchor transfer.  No externally chosen layer-count
function or outer-scale sandwich remains. -/
theorem exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (halphaUpper : alpha ≤ 1 / 16)
    (hdeltaNonneg : ∀ m, 0 ≤ delta m)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hmargin :
      IsCarlsonMovingQuadraticLogPowerLayerCountGap delta
        (dyadicCarlsonLayerSchedule delta)) :
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
  exact exists_constants_tendsto_actualDyadicCarlsonFixedAnchorMass_zero
    halpha halphaUpper hdeltaNonneg hdelta
      (eventually_dyadicCarlsonLayerSchedule_scale hdelta hdeltaUpper)
      hmargin

end

end PrimeNumberTheorem
