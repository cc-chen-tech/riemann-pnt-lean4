import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonTruncatedSplit
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterBoundaryLimit

/-!
# Truncated Carlson split with boundary zeros

The finite-high-sum comparison only needs the normalized power factor to be
at most one.  Consequently its real-part hypothesis can be weakened from
`Re rho < beta` to `Re rho <= beta`.  This module records the non-strict
versions without changing the existing strict-gap API.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

theorem pntPowerLayerToTargetRatio_le_one_of_le
    {beta tau : ℝ} {m : ℕ} (htau : tau ≤ beta) (hm : 1 ≤ m) :
    pntPowerLayerToTargetRatio beta tau m ≤ 1 := by
  rw [pntPowerLayerToTargetRatio]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr htau)
    (Real.log_nonneg (by exact_mod_cast hm))

theorem summable_actualCarlsonOutsideClusterNormalizedKernelTerm_of_le
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    {m : ℕ} (hm : 1 ≤ m) :
    Summable
      (actualCarlsonOutsideClusterNormalizedKernelTerm
        (sigma := sigma) beta S m) := by
  let model : ActualCarlsonPositiveZeroIndex sigma → ℝ :=
    fun index =>
      actualCarlsonOutsideClusterWeight S index *
        pntPowerLayerToTargetRatio beta
          (actualCarlsonOutsideClusterRealPart beta S index) m
  have hmodel : Summable model := by
    refine Summable.of_nonneg_of_le ?_ ?_
      (summable_actualCarlsonOutsideClusterWeight S hhalf hone)
    · intro index
      exact mul_nonneg
        (actualCarlsonOutsideClusterWeight_nonneg S index)
        (pntPowerLayerToTargetRatio_nonneg _ _ _)
    · intro index
      exact mul_le_of_le_one_right
        (actualCarlsonOutsideClusterWeight_nonneg S index)
        (pntPowerLayerToTargetRatio_le_one_of_le
          (actualCarlsonOutsideClusterRealPart_le S hre index) hm)
  apply hmodel.congr
  intro index
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · simp [model, actualCarlsonOutsideClusterNormalizedKernelTerm,
      actualCarlsonOutsideClusterWeight,
      actualCarlsonOutsideClusterRealPart, hmem]
  · simp only [model, actualCarlsonOutsideClusterNormalizedKernelTerm,
      actualCarlsonOutsideClusterWeight,
      actualCarlsonOutsideClusterRealPart, hmem, if_false]
    exact
      (normalized_actualCarlsonPositiveZeroKernel_eq_weightedPower
        index (Nat.zero_lt_of_lt hm)).symm

/-- Any finite high-strip family outside `S` is bounded by the complete
Carlson tail under the non-strict right-boundary condition. -/
theorem finite_actualHighPositiveZeroKernelSum_le_CarlsonTail_of_le
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hre :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (s : Finset (ActualCarlsonHighPositiveZero sigma))
    (houtside : ∀ rho ∈ s, rho.1 ∉ S)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑ rho ∈ s,
      ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
        (m : ℝ) ^ (beta - 1)) ≤
      actualCarlsonOutsideClusterNormalizedKernelTail
        (sigma := sigma) beta S m := by
  let e := actualCarlsonPositiveZeroIndexEmbedding sigma
  let term :=
    actualCarlsonOutsideClusterNormalizedKernelTerm
      (sigma := sigma) beta S m
  have hsum :
      (∑ rho ∈ s,
        ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
          (m : ℝ) ^ (beta - 1)) =
        ∑ index ∈ s.map e, term index := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro rho hrho
    change
      ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
          (m : ℝ) ^ (beta - 1) =
        if actualCarlsonPositiveZero
            (actualCarlsonPositiveZeroIndexOf rho) ∈ S then 0
        else
          ‖pntRelativeZeroContribution (m : ℝ)
              (actualCarlsonPositiveZero
                (actualCarlsonPositiveZeroIndexOf rho))‖ /
            (m : ℝ) ^ (beta - 1)
    rw [actualCarlsonPositiveZero_indexOf]
    simp [houtside rho hrho]
  rw [hsum, actualCarlsonOutsideClusterNormalizedKernelTail_eq_tsum_term]
  exact
    (summable_actualCarlsonOutsideClusterNormalizedKernelTerm_of_le
      S hhalf hone hre hm).sum_le_tsum
        (s.map e)
        (fun index _ =>
          actualCarlsonOutsideClusterNormalizedKernelTerm_nonneg
            S m index)

/-- The truncated positive-zero sum is bounded by the low layer plus the
complete Carlson tail even when high-strip zeros may lie on `Re rho = beta`. -/
theorem truncatedPositiveZeroKernelSum_div_target_le_low_add_CarlsonTail_of_le
    {T sigma beta : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n) (i : Fin n)
    (hreLow : ∀ rho ∈ input.layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        rho.re ≤ sigma → input.bucket rho = i)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        pntRelativeZeroContribution (m : ℝ) rho‖ /
          (m : ℝ) ^ (beta - 1) ≤
      ‖∑ rho ∈ input.layer i,
          pntRelativeZeroContribution (m : ℝ) rho‖ /
            (m : ℝ) ^ (beta - 1) +
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta S m := by
  let all := positiveNontrivialZerosOutsideClusterFinset T S
  let high := actualHighPositiveZerosOutsideClusterFinset sigma T S
  let contribution : ℂ → ℂ :=
    fun rho => pntRelativeZeroContribution (m : ℝ) rho
  have hlow :
      input.layer i = all.filter (fun rho => rho.re ≤ sigma) :=
    lowLayer_eq_filter_re_le input i hreLow hlowCover
  have hhigh :
      high = all.filter (fun rho => ¬rho.re ≤ sigma) := by
    ext rho
    simp only [high, all, actualHighPositiveZerosOutsideClusterFinset,
      Finset.mem_filter]
    constructor
    · rintro ⟨hbase, hlt⟩
      exact ⟨hbase, not_le.mpr hlt⟩
    · rintro ⟨hbase, hnle⟩
      exact ⟨hbase, lt_of_not_ge hnle⟩
  have hpartition :
      (∑ rho ∈ all, contribution rho) =
        (∑ rho ∈ input.layer i, contribution rho) +
          ∑ rho ∈ high, contribution rho := by
    rw [hlow, hhigh]
    exact
      (Finset.sum_filter_add_sum_filter_not
        all (fun rho => rho.re ≤ sigma) contribution).symm
  have hnorm :
      ‖∑ rho ∈ all, contribution rho‖ ≤
        ‖∑ rho ∈ input.layer i, contribution rho‖ +
          ∑ rho ∈ high, ‖contribution rho‖ := by
    rw [hpartition]
    exact (norm_add_le _ _).trans
      (add_le_add_right (norm_sum_le high contribution) _)
  have hamp : 0 < (m : ℝ) ^ (beta - 1) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _
  have hnormDiv :=
    (div_le_div_iff_of_pos_right hamp).mpr hnorm
  have houtside :
      ∀ rho ∈ actualHighPositiveZeroSubtypeFinset sigma T S,
        rho.1 ∉ S :=
    fun _ hrho => actualHighPositiveZeroSubtypeFinset_outside hrho
  have hfinite :=
    finite_actualHighPositiveZeroKernelSum_le_CarlsonTail_of_le
      S hhalf hone hreHigh
      (actualHighPositiveZeroSubtypeFinset sigma T S)
      houtside hm
  have hfinite' :
      (∑ rho ∈ high,
        ‖contribution rho‖ / (m : ℝ) ^ (beta - 1)) ≤
          actualCarlsonOutsideClusterNormalizedKernelTail
            (sigma := sigma) beta S m := by
    change
      (∑ rho ∈ actualHighPositiveZerosOutsideClusterFinset sigma T S,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖ /
          (m : ℝ) ^ (beta - 1)) ≤
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta S m
    rw [← sum_actualHighPositiveZeroSubtypeFinset sigma T S]
    exact hfinite
  rw [add_div] at hnormDiv
  have hsumDiv :
      (∑ rho ∈ high, ‖contribution rho‖) /
          (m : ℝ) ^ (beta - 1) =
        ∑ rho ∈ high,
          ‖contribution rho‖ / (m : ℝ) ^ (beta - 1) := by
    rw [Finset.sum_div]
  rw [hsumDiv] at hnormDiv
  exact hnormDiv.trans (add_le_add_right hfinite' _)

end

end PrimeNumberTheorem
