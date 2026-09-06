import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridDensityDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridUpper
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFixedResidualDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFormulaRemainderDecay

/-!
# Complete fixed-rate relative PNT decay

This module closes the fixed-rate upper-transfer chain.  A canonical single
bucket with threshold zero covers every positive-height nontrivial zero, so
the bucket threshold is independent of the selected contour height.  The
global low-density estimate then supplies one Pintz constant valid for every
sufficiently small fixed rate.

The resulting density decay is combined with the real-ordinate residual,
fixed explicit-formula constants, trivial-zero contribution, and contour
remainder.  Finally, the existing good-height certificate is turned into a
cofinal height schedule, yielding relative PNT decay along natural points.

No zero-density result beyond the already proved global multiplicity estimate
is asserted, and no statement about the Riemann hypothesis is made.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- The canonical one-bucket decomposition.  Its threshold is fixed at zero,
independently of the contour height. -/
noncomputable def singletonZeroThresholdBucketInput
    (T : ℝ) : PositiveZeroBucketInput T 1 where
  bucket := fun _ => 0
  sigma := fun _ => 0
  sigma_lt_re := by
    intro rho hrho
    exact (mem_positiveNontrivialZerosFinset.mp hrho).1.2.1

@[simp]
theorem singletonZeroThresholdBucketInput_sigma
    (T : ℝ) (i : Fin 1) :
    (singletonZeroThresholdBucketInput T).sigma i = 0 :=
  rfl

/-- For the zero-threshold singleton bucket, the hybrid density budget is
entirely the global low-density budget. -/
theorem singletonZeroThreshold_hybridDensityBudget_eq_global
    (x T : ℝ) :
    pintzCarlsonHybridDensityBudget (fun _ : Fin 1 => 0) x T =
      pintzGlobalLowDensityBudget (fun _ : Fin 1 => 0) x T := by
  simp [pintzCarlsonHybridDensityBudget, pintzCarlsonHighDensityIndices,
    pintzCarlsonClassicalAggregatedDensityLayerTerm,
    pintzCarlsonAggregatedDensityLayerTerm]

/-- One Pintz constant controls the singleton hybrid budget at every positive
fixed rate below the corresponding gap.  The constant is chosen before the
rate. -/
theorem exists_pintzConstant_singletonZeroThresholdHybridDensity_tendsto :
    ∃ c > 0, ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget (fun _ : Fin 1 => 0) x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0) := by
  let sigma : Fin 1 → ℝ := fun _ => 0
  rcases exists_globalCoefficient_lowDensityBudget_le_growthMajorant sigma with
    ⟨C, hC, hglobal⟩
  rcases exists_pintzConstant_globalLowDensityGrowthMajorant_tendsto
      C sigma hC with ⟨c, hc, hgrowth⟩
  refine ⟨c, hc, ?_⟩
  intro rate hrate hgap
  have hheight : Tendsto (pintzCarlsonHeight rate) atTop atTop :=
    tendsto_pintzCarlsonHeight_atTop hrate
  have hdominated :
      ∀ᶠ x : ℝ in atTop,
        pintzGlobalLowDensityBudget sigma x
            (pintzCarlsonHeight rate x) ≤
          pintzGlobalLowDensityGrowthMajorant C sigma x
            (pintzCarlsonHeight rate x) := by
    filter_upwards
        [hheight.eventually (eventually_ge_atTop (4 : ℝ))] with x hx
    exact hglobal x (pintzCarlsonHeight rate x) hx
  have hlow :
      Tendsto
        (fun x : ℝ =>
          pintzGlobalLowDensityBudget sigma x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ hdominated (hgrowth rate hrate hgap)
    exact Filter.Eventually.of_forall fun x =>
      pintzGlobalLowDensityBudget_nonneg sigma x
        (pintzCarlsonHeight rate x)
  simpa only [sigma,
    singletonZeroThreshold_hybridDensityBudget_eq_global] using hlow

/-- The base of the fixed-rate good-height interval is eventually at least
eight, as required by the cofinal explicit formula. -/
theorem eventually_pintzCarlsonGoodHeightBase_ge_eight
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᶠ m : ℕ in atTop,
      8 ≤ pintzCarlsonGoodHeightBase rate (m : ℝ) := by
  have hheight :
      Tendsto
        (fun m : ℕ => pintzCarlsonHeight rate (m : ℝ))
        atTop atTop :=
    (tendsto_pintzCarlsonHeight_atTop hrate).comp
      tendsto_natCast_atTop_atTop
  filter_upwards
      [hheight.eventually (eventually_ge_atTop (9 : ℝ))] with m hm
  dsimp [pintzCarlsonGoodHeightBase]
  linarith

/-- A cofinal fixed-rate schedule carrying the actual relative PNT upper
certificate. -/
structure FixedRatePNTUpperSchedule (C rate : ℝ) where
  height : ℕ → ℝ
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
          (height m) rate m 0
          (singletonZeroThresholdBucketInput (height m))

/-- The complete relative budget attached to a fixed-rate schedule. -/
noncomputable def FixedRatePNTUpperSchedule.relativeBudget
    {C rate : ℝ} (schedule : FixedRatePNTUpperSchedule C rate)
    (m : ℕ) : ℝ :=
  naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
    (pintzCarlsonGoodHeightBase rate (m : ℝ))
    (schedule.height m) rate m 0
    (singletonZeroThresholdBucketInput (schedule.height m))

/-- Every positive fixed rate admits a cofinal good-height schedule and the
corresponding actual relative PNT upper certificate. -/
theorem exists_fixedRatePNTUpperSchedule
    {rate : ℝ} (hrate : 0 < rate) :
    ∃ C : ℝ, 0 ≤ C ∧ Nonempty (FixedRatePNTUpperSchedule C rate) := by
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
                T rate m 0 (singletonZeroThresholdBucketInput T) := by
    intro m hm
    rcases htransfer m 0 hm.1 hm.2 with
      ⟨T, hT, _hgood, _certificate, _htrivial, _hremainder, hbounds⟩
    exact
      ⟨T, hT,
        (hbounds (singletonZeroThresholdBucketInput T)).2⟩
  let height : ℕ → ℝ := fun m =>
    if hm :
        3 ≤ m ∧ 8 ≤ pintzCarlsonGoodHeightBase rate (m : ℝ) then
      Classical.choose (hexists m hm)
    else
      0
  refine ⟨C, hC, ⟨{
    height := height
    height_mem_interval := ?_
    relative_upper := ?_
  }⟩⟩
  · filter_upwards [heligible] with m hm
    dsimp only [height]
    rw [dif_pos hm]
    exact (Classical.choose_spec (hexists m hm)).1
  · filter_upwards [heligible] with m hm
    dsimp only [height]
    rw [dif_pos hm]
    exact (Classical.choose_spec (hexists m hm)).2

/-- Every schedule height is eventually nonnegative. -/
theorem FixedRatePNTUpperSchedule.eventually_height_nonneg
    {C rate : ℝ} (schedule : FixedRatePNTUpperSchedule C rate)
    (hrate : 0 < rate) :
    ∀ᶠ m : ℕ in atTop, 0 ≤ schedule.height m := by
  filter_upwards
      [schedule.height_mem_interval,
        eventually_pintzCarlsonGoodHeightBase_ge_eight hrate]
      with m hm hbase
  linarith [hm.1]

/-- Along a fixed-rate schedule, all density, zero-residual, fixed, trivial,
and contour terms in the complete relative budget tend to zero. -/
theorem FixedRatePNTUpperSchedule.relativeBudget_tendsto
    {C rate : ℝ} (schedule : FixedRatePNTUpperSchedule C rate)
    (hC : 0 ≤ C) (hrate : 0 < rate) (hrateOne : rate ≤ 1)
    (hdensity :
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget (fun _ : Fin 1 => 0) x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0)) :
    Tendsto schedule.relativeBudget atTop (nhds 0) := by
  have hdensityNat :
      Tendsto
        (fun m : ℕ =>
          pintzCarlsonHybridDensityBudget (fun _ : Fin 1 => 0) (m : ℝ)
            (pintzCarlsonHeight rate (m : ℝ)))
        atTop (nhds 0) :=
    hdensity.comp tendsto_natCast_atTop_atTop
  have hfixed :=
    tendsto_naturalPoint_fixedRelativeResidual_zeroDepth schedule.height
      (schedule.eventually_height_nonneg hrate)
  have hremainder :=
    cofinalPNTFormulaRemainderBound_zero_relative_tendsto
      hC hrate hrateOne schedule.height schedule.height_mem_interval
  unfold FixedRatePNTUpperSchedule.relativeBudget
  simpa only [
      naturalPointPintzPNTHybridCeilingRelativeUpperBudget,
      singletonZeroThresholdBucketInput, add_div, add_assoc, mul_zero, zero_add]
    using
    ((hdensityNat.const_mul 2).add hfixed).add hremainder

/-- A vanishing complete schedule budget transfers to the actual relative PNT
error. -/
theorem FixedRatePNTUpperSchedule.relativeError_tendsto
    {C rate : ℝ} (schedule : FixedRatePNTUpperSchedule C rate)
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

/-- There exists a positive fixed Pintz--Carlson rate at which the complete
machine-verified transfer proves relative PNT decay along natural points. -/
theorem exists_fixedRate_relativeChebyshevPsi0Error_tendsto :
    ∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) := by
  rcases exists_pintzConstant_singletonZeroThresholdHybridDensity_tendsto with
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
  rcases exists_fixedRatePNTUpperSchedule hrate with
    ⟨C, hC, ⟨schedule⟩⟩
  have hbudget :=
    schedule.relativeBudget_tendsto hC hrate hrateOne
      (hdensity rate hrate hgap)
  exact
    ⟨rate, hrate, hrateOne,
      schedule.relativeError_tendsto hbudget⟩

end PrimeNumberTheorem
