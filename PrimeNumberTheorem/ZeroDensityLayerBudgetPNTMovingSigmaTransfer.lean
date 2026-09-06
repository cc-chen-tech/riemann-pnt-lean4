import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFixedSigmaTransfer

/-!
# Moving-threshold density transfer to the actual PNT error

Carlson's proved zero-density theorem supplies an eventual estimate after a
real-part threshold `sigma` has been fixed.  It cannot be applied directly to
a threshold that moves with the explicit-formula height: the corresponding
constants and eventual cutoffs need not be uniform.

This module isolates the exact stronger input needed for such a moving
threshold.  The density hypothesis must hold uniformly for every height
selection in the unit good-height interval.  Under that hypothesis, the same
explicit-formula machinery transfers the moving density budget to the actual
relative `chebyshevPsi0` error.  Fixed-threshold Carlson decay is recovered as
a special case.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- A cofinal explicit-formula schedule whose threshold family may vary with
the selected good height. -/
structure MovingSigmaPNTUpperSchedule
    {n : ℕ} (C rate : ℝ)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n) where
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
          (height m) rate m 0 (inputAtHeight (height m))

/-- Complete relative explicit-formula budget along a moving-threshold
schedule. -/
noncomputable def MovingSigmaPNTUpperSchedule.relativeBudget
    {n : ℕ} {C rate : ℝ}
    {inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n}
    (schedule :
      MovingSigmaPNTUpperSchedule (n := n) C rate inputAtHeight)
    (m : ℕ) : ℝ :=
  naturalPointPintzPNTHybridCeilingRelativeUpperBudget C
    (pintzCarlsonGoodHeightBase rate (m : ℝ))
    (schedule.height m) rate m 0 (inputAtHeight (schedule.height m))

/-- Any height-indexed bucket family can be attached to the cofinal good-height
certificate.  No fixed-threshold assumption is made. -/
theorem exists_movingSigmaPNTUpperSchedule
    {n : ℕ} {rate : ℝ} (hrate : 0 < rate)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n) :
    ∃ C : ℝ, 0 ≤ C ∧
      Nonempty
        (MovingSigmaPNTUpperSchedule (n := n) C rate inputAtHeight) := by
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

/-- Selected moving-threshold heights are eventually nonnegative. -/
theorem MovingSigmaPNTUpperSchedule.eventually_height_nonneg
    {n : ℕ} {C rate : ℝ}
    {inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n}
    (schedule :
      MovingSigmaPNTUpperSchedule (n := n) C rate inputAtHeight)
    (hrate : 0 < rate) :
    ∀ᶠ m : ℕ in atTop, 0 ≤ schedule.height m := by
  filter_upwards
      [schedule.height_mem_interval,
        eventually_pintzCarlsonGoodHeightBase_ge_eight hrate]
      with m hm hbase
  linarith [hm.1]

/-- The uniform density input needed when the threshold family depends on the
height chosen inside the unit good-height interval. -/
def UniformMovingSigmaHybridDensityDecay
    {n : ℕ} (rate : ℝ)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n) : Prop :=
  ∀ height : ℕ → ℝ,
    (∀ᶠ m : ℕ in atTop,
      height m ∈ Set.Icc
        (pintzCarlsonGoodHeightBase rate (m : ℝ))
        (pintzCarlsonGoodHeightBase rate (m : ℝ) + 1)) →
    Tendsto
      (fun m : ℕ =>
        pintzCarlsonHybridDensityBudget
          (inputAtHeight (height m)).sigma (m : ℝ)
          (pintzCarlsonHeight rate (m : ℝ)))
      atTop (nhds 0)

/-- A fixed threshold family automatically satisfies the moving-threshold
interface once its ordinary real-variable density budget tends to zero. -/
theorem uniformMovingSigmaHybridDensityDecay_of_fixed
    {n : ℕ} {rate : ℝ} {sigma : Fin n → ℝ}
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n)
    (hsigma : ∀ T : ℝ, (inputAtHeight T).sigma = sigma)
    (hdensity :
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget sigma x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0)) :
    UniformMovingSigmaHybridDensityDecay rate inputAtHeight := by
  intro height _hheight
  have hdensityNat :=
    hdensity.comp tendsto_natCast_atTop_atTop
  change Tendsto
      (fun m : ℕ =>
        pintzCarlsonHybridDensityBudget sigma (m : ℝ)
          (pintzCarlsonHeight rate (m : ℝ)))
      atTop (nhds 0) at hdensityNat
  simpa only [hsigma] using hdensityNat

/-- A moving-threshold density limit absorbs the remaining real-ordinate,
fixed, trivial-zero, and contour terms in the relative explicit formula. -/
theorem MovingSigmaPNTUpperSchedule.relativeBudget_tendsto
    {n : ℕ} {C rate : ℝ}
    {inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n}
    (schedule :
      MovingSigmaPNTUpperSchedule (n := n) C rate inputAtHeight)
    (hC : 0 ≤ C) (hrate : 0 < rate) (hrateOne : rate ≤ 1)
    (hdensity :
      Tendsto
        (fun m : ℕ =>
          pintzCarlsonHybridDensityBudget
            (inputAtHeight (schedule.height m)).sigma (m : ℝ)
            (pintzCarlsonHeight rate (m : ℝ)))
        atTop (nhds 0)) :
    Tendsto schedule.relativeBudget atTop (nhds 0) := by
  have hfixed :=
    tendsto_naturalPoint_fixedRelativeResidual_zeroDepth schedule.height
      (schedule.eventually_height_nonneg hrate)
  have hremainder :=
    cofinalPNTFormulaRemainderBound_zero_relative_tendsto
      hC hrate hrateOne schedule.height schedule.height_mem_interval
  unfold MovingSigmaPNTUpperSchedule.relativeBudget
  simpa only [naturalPointPintzPNTHybridCeilingRelativeUpperBudget,
      add_div, add_assoc, mul_zero, zero_add] using
    ((hdensity.const_mul 2).add hfixed).add hremainder

/-- Vanishing moving-threshold budget transfers to the actual relative PNT
error. -/
theorem MovingSigmaPNTUpperSchedule.relativeError_tendsto
    {n : ℕ} {C rate : ℝ}
    {inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n}
    (schedule :
      MovingSigmaPNTUpperSchedule (n := n) C rate inputAtHeight)
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

/-- Uniform moving-threshold density decay is sufficient for an actual
natural-point relative PNT theorem. -/
theorem exists_movingSigma_relativeChebyshevPsi0Error_tendsto
    {n : ℕ} {rate : ℝ}
    (hrate : 0 < rate) (hrateOne : rate ≤ 1)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n)
    (hdensity :
      UniformMovingSigmaHybridDensityDecay rate inputAtHeight) :
    ∃ C : ℝ, 0 ≤ C ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) := by
  rcases exists_movingSigmaPNTUpperSchedule hrate inputAtHeight with
    ⟨C, hC, ⟨schedule⟩⟩
  have hbudget :=
    schedule.relativeBudget_tendsto hC hrate hrateOne
      (hdensity schedule.height schedule.height_mem_interval)
  exact ⟨C, hC, schedule.relativeError_tendsto hbudget⟩

end PrimeNumberTheorem
