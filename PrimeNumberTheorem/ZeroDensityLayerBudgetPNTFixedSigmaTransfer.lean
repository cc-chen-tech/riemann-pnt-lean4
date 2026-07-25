import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTTwoStripDensityDecay

/-!
# Fixed-threshold dynamic PNT transfer

The density limit is naturally stated for a fixed threshold family `sigma`,
while the positive-zero bucket itself depends on the selected contour height.
This module isolates the compatibility condition needed to join those two
interfaces: every height-dependent bucket in the schedule must expose the same
threshold function.

The resulting transfer applies to arbitrary finite fixed threshold families.
The concrete two-strip instance then gives an actual PNT upper transfer whose
low strip uses global counting and whose `sigma = 3/4` high strip uses Carlson.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- A cofinal explicit-formula schedule with height-dependent buckets sharing
one fixed threshold family. -/
structure FixedSigmaPNTUpperSchedule
    {n : ℕ} (C rate : ℝ) (sigma : Fin n → ℝ) where
  height : ℕ → ℝ
  input : ∀ m, PositiveZeroBucketInput (height m) n
  input_sigma : ∀ m, (input m).sigma = sigma
  height_mem_interval :
    ∀ᶠ m : ℕ in atTop,
      height m ∈ Set.Icc
        (pintzCarlsonGoodHeightBase rate (m : ℝ))
        (pintzCarlsonGoodHeightBase rate (m : ℝ) + 1)
  relative_upper :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
          (pintzCarlsonGoodHeightBase rate (m : ℝ))
          (height m) rate m 0 (input m)

/-- Complete relative upper budget along a fixed-threshold schedule. -/
noncomputable def FixedSigmaPNTUpperSchedule.relativeBudget
    {n : ℕ} {C rate : ℝ} {sigma : Fin n → ℝ}
    (schedule : FixedSigmaPNTUpperSchedule C rate sigma)
    (m : ℕ) : ℝ :=
  naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
    (pintzCarlsonGoodHeightBase rate (m : ℝ))
    (schedule.height m) rate m 0 (schedule.input m)

/-- Any height-indexed bucket family with fixed thresholds can be attached to
the cofinal good-height explicit-formula certificate. -/
theorem exists_fixedSigmaPNTUpperSchedule
    {n : ℕ} {rate : ℝ} (hrate : 0 < rate)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n)
    (hsigma : ∀ T : ℝ, (inputAtHeight T).sigma =
      (inputAtHeight 0).sigma) :
    ∃ C : ℝ, 0 ≤ C ∧
      Nonempty
        (FixedSigmaPNTUpperSchedule C rate (inputAtHeight 0).sigma) := by
  classical
  rcases exists_naturalPoint_pintzCarlson_goodHeight_hybrid_PNT_upper
      (fun _ => rate) with ⟨C, hC, htransfer⟩
  have hbase :=
    eventually_pintzCarlsonGoodHeightBase_ge_eight hrate
  have heligible :
      ∀ᶠ m : ℕ in atTop,
        3 ≤ m ∧ 8 ≤ pintzCarlsonGoodHeightBase rate (m : ℝ) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hbase] with m hm hbasem
    exact ⟨hm, hbasem⟩
  have hexists :
      ∀ m : ℕ,
        3 ≤ m ∧ 8 ≤ pintzCarlsonGoodHeightBase rate (m : ℝ) →
          ∃ T : ℝ,
            T ∈ Set.Icc
              (pintzCarlsonGoodHeightBase rate (m : ℝ))
              (pintzCarlsonGoodHeightBase rate (m : ℝ) + 1) ∧
            |relativeChebyshevPsi0Error (m : ℝ)| ≤
              naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
                (pintzCarlsonGoodHeightBase rate (m : ℝ))
                T rate m 0 (inputAtHeight T) := by
    intro m hm
    rcases htransfer m 0 hm.1 hm.2 with
      ⟨T, hT, _hgood, _certificate, _htrivial, _hremainder, hbounds⟩
    exact ⟨T, hT, (hbounds (inputAtHeight T)).2⟩
  let height : ℕ → ℝ := fun m =>
    if hm :
        3 ≤ m ∧ 8 ≤ pintzCarlsonGoodHeightBase rate (m : ℝ) then
      Classical.choose (hexists m hm)
    else
      0
  let input : ∀ m, PositiveZeroBucketInput (height m) n :=
    fun m => inputAtHeight (height m)
  refine ⟨C, hC, ⟨{
    height := height
    input := input
    input_sigma := ?_
    height_mem_interval := ?_
    relative_upper := ?_
  }⟩⟩
  · intro m
    exact hsigma (height m)
  · filter_upwards [heligible] with m hm
    dsimp only [height]
    rw [dif_pos hm]
    exact (Classical.choose_spec (hexists m hm)).1
  · filter_upwards [heligible] with m hm
    dsimp only [height, input]
    rw [dif_pos hm]
    exact (Classical.choose_spec (hexists m hm)).2

/-- Heights selected by a fixed-threshold schedule are eventually
nonnegative. -/
theorem FixedSigmaPNTUpperSchedule.eventually_height_nonneg
    {n : ℕ} {C rate : ℝ} {sigma : Fin n → ℝ}
    (schedule : FixedSigmaPNTUpperSchedule C rate sigma)
    (hrate : 0 < rate) :
    ∀ᶠ m : ℕ in atTop, 0 ≤ schedule.height m := by
  filter_upwards
      [schedule.height_mem_interval,
        eventually_pintzCarlsonGoodHeightBase_ge_eight hrate]
      with m hm hbase
  linarith [hm.1]

/-- A fixed-threshold density limit automatically absorbs every remaining
term in the natural-point relative explicit-formula budget. -/
theorem FixedSigmaPNTUpperSchedule.relativeBudget_tendsto
    {n : ℕ} {C rate : ℝ} {sigma : Fin n → ℝ}
    (schedule : FixedSigmaPNTUpperSchedule C rate sigma)
    (hC : 0 ≤ C) (hrate : 0 < rate) (hrateOne : rate ≤ 1)
    (hdensity :
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget sigma x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0)) :
    Tendsto schedule.relativeBudget atTop (nhds 0) := by
  have hdensityNat :
      Tendsto
        (fun m : ℕ =>
          pintzCarlsonHybridDensityBudget sigma (m : ℝ)
            (pintzCarlsonHeight rate (m : ℝ)))
        atTop (nhds 0) :=
    hdensity.comp tendsto_natCast_atTop_atTop
  have hfixed :=
    tendsto_naturalPoint_fixedRelativeResidual_zeroDepth schedule.height
      (schedule.eventually_height_nonneg hrate)
  have hremainder :=
    cofinalPNTFormulaRemainderBound_zero_relative_tendsto
      hC hrate hrateOne schedule.height schedule.height_mem_interval
  unfold FixedSigmaPNTUpperSchedule.relativeBudget
  simpa only [naturalPointPintzPNTHybridCeilingRelativeUpperBudget,
      schedule.input_sigma, add_div, add_assoc, mul_zero, zero_add] using
    ((hdensityNat.const_mul 2).add hfixed).add hremainder

/-- Vanishing fixed-threshold budget transfers to the actual relative PNT
error. -/
theorem FixedSigmaPNTUpperSchedule.relativeError_tendsto
    {n : ℕ} {C rate : ℝ} {sigma : Fin n → ℝ}
    (schedule : FixedSigmaPNTUpperSchedule C rate sigma)
    (hbudget : Tendsto schedule.relativeBudget atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero'
      (Filter.Eventually.of_forall fun m : ℕ =>
        abs_nonneg (relativeChebyshevPsi0Error (m : ℝ)))
      schedule.relative_upper hbudget

/-- The concrete two-strip bucket family admits a cofinal actual PNT upper
schedule. -/
theorem exists_pntTwoStripPNTUpperSchedule
    {rate : ℝ} (hrate : 0 < rate) :
    ∃ C : ℝ, 0 ≤ C ∧
      Nonempty (FixedSigmaPNTUpperSchedule C rate pntTwoStripSigma) := by
  simpa only [pntTwoStripBucketInput_sigma] using
    exists_fixedSigmaPNTUpperSchedule hrate pntTwoStripBucketInput
      (fun T => rfl)

/-- There exists a positive fixed rate for which the actual natural-point
relative PNT error decays through a genuine low/global plus high/Carlson
two-strip decomposition. -/
theorem exists_fixedRate_pntTwoStrip_relativeChebyshevPsi0Error_tendsto :
    ∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) := by
  rcases exists_pintzConstant_pntTwoStripHybridDensityBudget_tendsto with
    ⟨c, hc, hdensity⟩
  let rate : ℝ := min 1 (Real.sqrt c)
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hrate : 0 < rate := by
    dsimp [rate]
    exact lt_min zero_lt_one hsqrt
  have hrateOne : rate ≤ 1 := by
    dsimp [rate]
    exact min_le_left _ _
  have hgap : rate < 2 * Real.sqrt c := by
    have hle : rate ≤ Real.sqrt c := by
      dsimp [rate]
      exact min_le_right _ _
    linarith
  rcases exists_pntTwoStripPNTUpperSchedule hrate with
    ⟨C, hC, ⟨schedule⟩⟩
  have hbudget :=
    schedule.relativeBudget_tendsto hC hrate hrateOne
      (hdensity rate hrate hgap)
  exact
    ⟨rate, hrate, hrateOne,
      schedule.relativeError_tendsto hbudget⟩

end PrimeNumberTheorem
