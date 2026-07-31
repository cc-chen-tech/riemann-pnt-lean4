import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPintzCarlsonFiniteRateRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFullRelativeDecay

/-!
# Pointwise optimization of the complete actual PNT budget over Pintz rates

The cost minimized here is the complete hybrid relative PNT upper budget at an
actual certified good height.  It contains the density, real-ordinate, fixed,
trivial-zero, and contour terms.  The minimum is squeezed by the least-rate
budget, yielding relative PNT decay under the existing Pintz density gap.

This is exact finite-rate optimality, not continuous-rate sharpness.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Complete machine-checked relative PNT budget for one actual rate
candidate. -/
noncomputable def actualPintzCarlsonRateFullRelativeBudget
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (k : ℝ) (m : ℕ) : ℝ :=
  naturalPointPintzPNTHybridCeilingRelativeUpperBudget
    grid.selection.constant
    (pintzCarlsonGoodHeightBase k (m : ℝ))
    (actualPintzCarlsonRateCandidateHeight grid k (m : ℝ))
    k m 0
    (singletonZeroThresholdBucketInput
      (actualPintzCarlsonRateCandidateHeight grid k (m : ℝ)))

/-- Every sufficiently large certified rate candidate bounds the real relative
PNT error by its complete hybrid budget. -/
theorem abs_relativeChebyshevPsi0Error_le_actualPintzCarlsonRateFullBudget
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {k : ℝ}
    (m : ℕ) (hm : 3 ≤ m)
    (hlarge : 9 ≤ pintzCarlsonHeight k (m : ℝ)) :
    |relativeChebyshevPsi0Error (m : ℝ)| ≤
      actualPintzCarlsonRateFullRelativeBudget grid k m := by
  have hbase : 8 ≤ pintzCarlsonGoodHeightBase k (m : ℝ) := by
    dsimp [pintzCarlsonGoodHeightBase]
    linarith
  let T := grid.selection.height
    (pintzCarlsonGoodHeightBase k (m : ℝ))
  have hTmem :
      T ∈ Set.Icc (pintzCarlsonGoodHeightBase k (m : ℝ))
        (pintzCarlsonGoodHeightBase k (m : ℝ) + 1) :=
    grid.selection.height_mem
      (pintzCarlsonGoodHeightBase k (m : ℝ)) hbase
  have hTceiling : T ≤ pintzCarlsonHeight k (m : ℝ) :=
    goodHeightInterval_le_pintzCarlsonHeight hTmem
  rcases grid.selection.truncated_certificate
      (pintzCarlsonGoodHeightBase k (m : ℝ)) hbase m 0 hm with
    ⟨certificate, htrivial, hremainder⟩
  let input := singletonZeroThresholdBucketInput T
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) hm)
  have hrelative :=
    certificate.abs_relativeChebyshevPsi0Error_le_pintz input hmReal
  rw [htrivial, hremainder] at hrelative
  have hceiling := hrelative.trans
    (naturalPointPintzPNTRelativeUpperBudget_le_ceilingDensity
      input hTceiling)
  have hhybrid := hceiling.trans
    (naturalPointPintzPNTCeilingDensityRelativeUpperBudget_le_hybrid input)
  have hcandidate :
      actualPintzCarlsonRateCandidateHeight grid k (m : ℝ) = T := by
    simp [actualPintzCarlsonRateCandidateHeight, hlarge, T]
  unfold actualPintzCarlsonRateFullRelativeBudget
  rw [hcandidate]
  exact hhybrid

/-- For a fixed grid rate, the complete hybrid relative budget tends to zero
whenever its hybrid density term does. -/
theorem actualPintzCarlsonRateFullRelativeBudget_tendsto_zero
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {k : ℝ} (hk : k ∈ grid.rates) (hkOne : k ≤ 1)
    (hdensity :
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget (fun _ : Fin 1 => 0) x
            (pintzCarlsonHeight k x))
        atTop (nhds 0)) :
    Tendsto (actualPintzCarlsonRateFullRelativeBudget grid k)
      atTop (nhds 0) := by
  have hdensityNat := hdensity.comp tendsto_natCast_atTop_atTop
  have hfixed :=
    tendsto_naturalPoint_fixedRelativeResidual_zeroDepth
      (fun m : ℕ =>
        actualPintzCarlsonRateCandidateHeight grid k (m : ℝ))
      (Filter.Eventually.of_forall fun m =>
        (actualPintzCarlsonRateCandidateHeight_pos grid k (m : ℝ)).le)
  have hcontour :=
    cofinalPNTFormulaRemainderBound_zero_relative_tendsto
      grid.selection.constant_nonneg (grid.rates_pos k hk) hkOne
      (fun m : ℕ =>
        actualPintzCarlsonRateCandidateHeight grid k (m : ℝ))
      (eventually_actualPintzCarlsonRateCandidateHeight_mem grid hk)
  unfold actualPintzCarlsonRateFullRelativeBudget
  simpa only [
      naturalPointPintzPNTHybridCeilingRelativeUpperBudget,
      singletonZeroThresholdBucketInput_sigma, add_div, add_assoc, mul_zero,
      zero_add] using
    ((hdensityNat.const_mul 2).add hfixed).add hcontour

/-- Pointwise rate minimizing the complete actual hybrid relative budget. -/
noncomputable def actualPintzCarlsonFullBudgetOptimalRate
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (m : ℕ) : ℝ :=
  Classical.choose (Finset.exists_min_image grid.rates
    (fun k => actualPintzCarlsonRateFullRelativeBudget grid k m)
    ⟨grid.baseRate, grid.baseRate_mem⟩)

theorem actualPintzCarlsonFullBudgetOptimalRate_mem
    (grid : ActualPintzCarlsonGoodHeightRateGrid) (m : ℕ) :
    actualPintzCarlsonFullBudgetOptimalRate grid m ∈ grid.rates :=
  (Classical.choose_spec (Finset.exists_min_image grid.rates
    (fun k => actualPintzCarlsonRateFullRelativeBudget grid k m)
    ⟨grid.baseRate, grid.baseRate_mem⟩)).1

theorem actualPintzCarlsonFullBudgetOptimalRate_le_of_mem
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (m : ℕ) {k : ℝ} (hk : k ∈ grid.rates) :
    actualPintzCarlsonRateFullRelativeBudget grid
        (actualPintzCarlsonFullBudgetOptimalRate grid m) m ≤
      actualPintzCarlsonRateFullRelativeBudget grid k m :=
  (Classical.choose_spec (Finset.exists_min_image grid.rates
    (fun k => actualPintzCarlsonRateFullRelativeBudget grid k m)
    ⟨grid.baseRate, grid.baseRate_mem⟩)).2 k hk

/-- Actual good height generated by the full-budget minimizing rate. -/
noncomputable def actualPintzCarlsonFullBudgetOptimalHeight
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (m : ℕ) : ℝ :=
  actualPintzCarlsonRateCandidateHeight grid
    (actualPintzCarlsonFullBudgetOptimalRate grid m) (m : ℝ)

/-- Minimum complete relative PNT budget on the finite rate grid. -/
noncomputable def actualPintzCarlsonFullBudgetMinimum
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (m : ℕ) : ℝ :=
  actualPintzCarlsonRateFullRelativeBudget grid
    (actualPintzCarlsonFullBudgetOptimalRate grid m) m

/-- The real relative PNT error is eventually bounded by the pointwise minimum
complete budget. -/
theorem eventually_abs_relativeChebyshevPsi0Error_le_actualPintzCarlsonFullBudgetMinimum
    (grid : ActualPintzCarlsonGoodHeightRateGrid) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        actualPintzCarlsonFullBudgetMinimum grid m := by
  have hbasePos : 0 < grid.baseRate :=
    grid.rates_pos grid.baseRate grid.baseRate_mem
  have hlarge :
      ∀ᶠ m : ℕ in atTop,
        9 ≤ pintzCarlsonHeight grid.baseRate (m : ℝ) :=
    (tendsto_atTop.1
      ((tendsto_pintzCarlsonHeight_atTop hbasePos).comp
        tendsto_natCast_atTop_atTop)) 9
  filter_upwards [hlarge, eventually_ge_atTop (3 : ℕ)] with m hlargeM hm
  let k := actualPintzCarlsonFullBudgetOptimalRate grid m
  have hk : k ∈ grid.rates :=
    actualPintzCarlsonFullBudgetOptimalRate_mem grid m
  have hraw := pintzCarlsonHeight_mono_rate (grid.baseRate_le k hk) (m : ℝ)
  have hkLarge : 9 ≤ pintzCarlsonHeight k (m : ℝ) := hlargeM.trans hraw
  simpa [actualPintzCarlsonFullBudgetMinimum, k] using
    abs_relativeChebyshevPsi0Error_le_actualPintzCarlsonRateFullBudget
      grid m hm hkLarge

/-- The minimum complete budget tends to zero because it is squeezed by the
least-rate budget. -/
theorem actualPintzCarlsonFullBudgetMinimum_tendsto_zero
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (hbaseRateOne : grid.baseRate ≤ 1)
    (hdensity :
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget (fun _ : Fin 1 => 0) x
            (pintzCarlsonHeight grid.baseRate x))
        atTop (nhds 0)) :
    Tendsto (actualPintzCarlsonFullBudgetMinimum grid)
      atTop (nhds 0) := by
  have hbaseBudget :=
    actualPintzCarlsonRateFullRelativeBudget_tendsto_zero
      grid grid.baseRate_mem hbaseRateOne hdensity
  refine squeeze_zero' ?_ ?_ hbaseBudget
  · filter_upwards
      [eventually_abs_relativeChebyshevPsi0Error_le_actualPintzCarlsonFullBudgetMinimum
        grid] with m hm
    exact (abs_nonneg _).trans hm
  · exact Filter.Eventually.of_forall fun m =>
      actualPintzCarlsonFullBudgetOptimalRate_le_of_mem
        grid m grid.baseRate_mem

/-- The pointwise minimum complete actual Pintz budget proves relative PNT
decay. -/
theorem actualPintzCarlsonFullBudgetOptimal_relativeError_tendsto_zero
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (hbaseRateOne : grid.baseRate ≤ 1)
    (hdensity :
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget (fun _ : Fin 1 => 0) x
            (pintzCarlsonHeight grid.baseRate x))
        atTop (nhds 0)) :
    Tendsto (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have habs :
      Tendsto (fun m : ℕ => |relativeChebyshevPsi0Error (m : ℝ)|)
        atTop (nhds 0) := by
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun m => abs_nonneg _) ?_
      (actualPintzCarlsonFullBudgetMinimum_tendsto_zero
        grid hbaseRateOne hdensity)
    exact
      eventually_abs_relativeChebyshevPsi0Error_le_actualPintzCarlsonFullBudgetMinimum
        grid
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [Real.norm_eq_abs] using habs

/-- The existing global Pintz density theorem automatically supplies one
positive density constant for the full-budget rate optimizer. -/
theorem exists_pintzConstant_actualPintzCarlsonFullBudgetOptimal_PNT_decay
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (hbaseRateOne : grid.baseRate ≤ 1) :
    ∃ c > 0, grid.baseRate < 2 * Real.sqrt c →
      Tendsto (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) := by
  rcases exists_pintzConstant_singletonZeroThresholdHybridDensity_tendsto with
    ⟨c, hc, hdensity⟩
  refine ⟨c, hc, ?_⟩
  intro hgap
  exact actualPintzCarlsonFullBudgetOptimal_relativeError_tendsto_zero
    grid hbaseRateOne
      (hdensity grid.baseRate
        (grid.rates_pos grid.baseRate grid.baseRate_mem) hgap)

end PrimeNumberTheorem
