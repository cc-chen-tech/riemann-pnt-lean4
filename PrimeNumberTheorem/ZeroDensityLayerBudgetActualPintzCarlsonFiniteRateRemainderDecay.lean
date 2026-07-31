import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPintzCarlsonGoodHeightRateGrid
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonClosedFormFullPNT

/-!
# Actual remainder decay under finite Pintz-rate switching

Each fixed-rate actual good-height candidate has a vanishing contour remainder.
The pointwise optimizer may switch rates arbitrarily, but its absolute actual
remainder is bounded by the finite sum of all fixed-rate absolute remainders.

This is ordinary relative remainder decay, not target-amplitude negligibility.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

/-- A fixed actual rate candidate is eventually in its Pintz good-height
interval. -/
theorem eventually_actualPintzCarlsonRateCandidateHeight_mem
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {k : ℝ} (hk : k ∈ grid.rates) :
    ∀ᶠ m : ℕ in atTop,
      actualPintzCarlsonRateCandidateHeight grid k (m : ℝ) ∈
        Set.Icc (pintzCarlsonGoodHeightBase k (m : ℝ))
          (pintzCarlsonGoodHeightBase k (m : ℝ) + 1) := by
  have hrate : 0 < k := grid.rates_pos k hk
  have hlarge :
      ∀ᶠ m : ℕ in atTop, 9 ≤ pintzCarlsonHeight k (m : ℝ) :=
    (tendsto_atTop.1
      ((tendsto_pintzCarlsonHeight_atTop hrate).comp
        tendsto_natCast_atTop_atTop)) 9
  filter_upwards [hlarge] with m hm
  have hbase : 8 ≤ pintzCarlsonGoodHeightBase k (m : ℝ) := by
    dsimp [pintzCarlsonGoodHeightBase]
    linarith
  simpa [actualPintzCarlsonRateCandidateHeight, hm] using
    grid.selection.height_mem
      (pintzCarlsonGoodHeightBase k (m : ℝ)) hbase

/-- Exact contour-plus-closed-log upper bound for one actual rate candidate. -/
noncomputable def actualPintzCarlsonRateNaturalRemainderUpperBound
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (k : ℝ) (m : ℕ) : ℝ :=
  cofinalPNTFormulaRemainderBound grid.selection.constant
      (pintzCarlsonGoodHeightBase k (m : ℝ))
      (actualPintzCarlsonRateCandidateHeight grid k (m : ℝ)) m 0 /
      (m : ℝ) +
    classicalClosedLogRelativeMajorant m

theorem actualPintzCarlsonRateNaturalRemainderUpperBound_tendsto_zero
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {k : ℝ} (hk : k ∈ grid.rates) (hkOne : k ≤ 1) :
    Tendsto (actualPintzCarlsonRateNaturalRemainderUpperBound grid k)
      atTop (nhds 0) := by
  have hcontour :=
    cofinalPNTFormulaRemainderBound_zero_relative_tendsto
      grid.selection.constant_nonneg (grid.rates_pos k hk) hkOne
      (fun m : ℕ =>
        actualPintzCarlsonRateCandidateHeight grid k (m : ℝ))
      (eventually_actualPintzCarlsonRateCandidateHeight_mem grid hk)
  unfold actualPintzCarlsonRateNaturalRemainderUpperBound
  simpa only [add_zero] using
    hcontour.add tendsto_classicalClosedLogRelativeMajorant_zero

/-- The actual multiplicity-aware relative remainder is eventually dominated
by the fixed-rate contour-plus-closed-log upper bound. -/
theorem eventually_abs_actualPintzCarlsonRate_actualRemainder_le
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {k : ℝ} (hk : k ∈ grid.rates) :
    ∀ᶠ m : ℕ in atTop,
      |actualPNTExplicitFormulaRelativeRemainder
        (actualPintzCarlsonRateCandidateHeight grid k) (m : ℝ)| ≤
        actualPintzCarlsonRateNaturalRemainderUpperBound grid k m := by
  have hrate : 0 < k := grid.rates_pos k hk
  have hlarge :
      ∀ᶠ m : ℕ in atTop, 9 ≤ pintzCarlsonHeight k (m : ℝ) :=
    (tendsto_atTop.1
      ((tendsto_pintzCarlsonHeight_atTop hrate).comp
        tendsto_natCast_atTop_atTop)) 9
  filter_upwards [hlarge, eventually_ge_atTop (3 : ℕ)] with m hm hthree
  have hbase : 8 ≤ pintzCarlsonGoodHeightBase k (m : ℝ) := by
    dsimp [pintzCarlsonGoodHeightBase]
    linarith
  rcases grid.selection.truncated_certificate
      (pintzCarlsonGoodHeightBase k (m : ℝ)) hbase m 0 hthree with
    ⟨certificate, htrivial, hremainder⟩
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hthree)
  have hbound :=
    certificate.abs_actualPNTExplicitFormulaRelativeRemainder_le
      (htrivial.trans (cofinalTrivialZeroContribution_zero m)) hmpos
  have hheight :
      actualPintzCarlsonRateCandidateHeight grid k (m : ℝ) =
        grid.selection.height
          (pintzCarlsonGoodHeightBase k (m : ℝ)) := by
    simp [actualPintzCarlsonRateCandidateHeight, hm]
  unfold actualPNTExplicitFormulaRelativeRemainder
  rw [hheight]
  rw [hremainder] at hbound
  simpa [actualPintzCarlsonRateNaturalRemainderUpperBound,
    classicalClosedLogRelativeMajorant, add_div, hheight] using hbound

/-- Ordinary actual relative remainder decay for one fixed grid rate. -/
theorem actualPintzCarlsonRate_actualRemainder_tendsto_zero
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {k : ℝ} (hk : k ∈ grid.rates) (hkOne : k ≤ 1) :
    Tendsto
      (fun m : ℕ =>
        actualPNTExplicitFormulaRelativeRemainder
          (actualPintzCarlsonRateCandidateHeight grid k) (m : ℝ))
      atTop (nhds 0) := by
  have habs :
      Tendsto
        (fun m : ℕ =>
          |actualPNTExplicitFormulaRelativeRemainder
            (actualPintzCarlsonRateCandidateHeight grid k) (m : ℝ)|)
        atTop (nhds 0) := by
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun m => abs_nonneg _) ?_
      (actualPintzCarlsonRateNaturalRemainderUpperBound_tendsto_zero
        grid hk hkOne)
    exact eventually_abs_actualPintzCarlsonRate_actualRemainder_le grid hk
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [Real.norm_eq_abs] using habs

/-- Pointwise switching among finitely many rates preserves ordinary actual
relative remainder decay. -/
theorem actualPintzCarlsonGoodHeightOptimalHeight_actualRemainder_tendsto_zero
    (cost : ℝ → ℝ → ℝ)
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (hratesOne : ∀ k ∈ grid.rates, k ≤ 1) :
    Tendsto
      (fun m : ℕ =>
        actualPNTExplicitFormulaRelativeRemainder
          (actualPintzCarlsonGoodHeightOptimalHeight cost grid) (m : ℝ))
      atTop (nhds 0) := by
  classical
  have hsum :
      Tendsto
        (fun m : ℕ =>
          ∑ k ∈ grid.rates,
            |actualPNTExplicitFormulaRelativeRemainder
              (actualPintzCarlsonRateCandidateHeight grid k) (m : ℝ)|)
        atTop (nhds 0) := by
    have hraw := tendsto_finset_sum grid.rates fun k hk => by
        have hrate :=
          actualPintzCarlsonRate_actualRemainder_tendsto_zero
            grid hk (hratesOne k hk)
        simpa [Real.norm_eq_abs] using hrate.norm
    have hzero : (∑ k ∈ grid.rates, (0 : ℝ)) = 0 := by simp
    rw [hzero] at hraw
    exact hraw
  have habs :
      Tendsto
        (fun m : ℕ =>
          |actualPNTExplicitFormulaRelativeRemainder
            (actualPintzCarlsonGoodHeightOptimalHeight cost grid) (m : ℝ)|)
        atTop (nhds 0) := by
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun m => abs_nonneg _) ?_ hsum
    filter_upwards [] with m
    rcases actualPintzCarlsonGoodHeightOptimalHeight_eq_candidate
        cost grid (m : ℝ) with ⟨k, hk, heq⟩
    have hremainder :
        actualPNTExplicitFormulaRelativeRemainder
            (actualPintzCarlsonGoodHeightOptimalHeight cost grid) (m : ℝ) =
          actualPNTExplicitFormulaRelativeRemainder
            (actualPintzCarlsonRateCandidateHeight grid k) (m : ℝ) := by
      unfold actualPNTExplicitFormulaRelativeRemainder
      rw [heq]
    rw [hremainder]
    exact Finset.single_le_sum
      (fun j _ => abs_nonneg
        (actualPNTExplicitFormulaRelativeRemainder
          (actualPintzCarlsonRateCandidateHeight grid j) (m : ℝ))) hk
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [Real.norm_eq_abs] using habs

end PrimeNumberTheorem
