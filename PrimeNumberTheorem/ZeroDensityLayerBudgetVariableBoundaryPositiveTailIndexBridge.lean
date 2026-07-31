import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryRealTailDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryTruncatedSplit

/-!
# Variable-boundary positive-tail index bridge

The finite high positive-zero family visible at the current height embeds into
the Carlson index type.  Outside the moving package, each normalized kernel is
exactly its visible Carlson term.  This closes the finite-sum-to-`tsum` bridge
and leaves only the explicit low strip to be estimated.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

theorem actualHighPositiveZeroSubtypeFinset_visible
    {sigma T : ℝ} {S : Finset ℂ}
    {rho : ActualCarlsonHighPositiveZero sigma}
    (hrho : rho ∈ actualHighPositiveZeroSubtypeFinset sigma T S) :
    |rho.1.im| ≤ T := by
  simp only [actualHighPositiveZeroSubtypeFinset, Finset.mem_map] at hrho
  rcases hrho with ⟨source, _, rfl⟩
  have hsource :=
    mem_actualHighPositiveZerosOutsideClusterFinset.mp source.property
  simpa [actualHighPositiveZeroSubtypeEmbedding,
    abs_of_pos hsource.2.1] using hsource.2.2.1

theorem summable_variableBoundaryVisibleWeightedPowerTerm
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    {m : ℕ} (hm : 1 ≤ m) :
    Summable
      (fun index : ActualCarlsonPositiveZeroIndex sigma =>
        variableBoundaryVisibleWeightedPowerTerm H beta index m) := by
  refine Summable.of_nonneg_of_le
    (fun index =>
      variableBoundaryVisibleWeightedPowerTerm_nonneg H beta index m)
    ?_ (summable_actualCarlsonPositiveZeroWeight hhalf hone)
  intro index
  have hnonneg :=
    variableBoundaryVisibleWeightedPowerTerm_nonneg H beta index m
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
    norm_variableBoundaryVisibleWeightedPowerTerm_le
      hright index hm

theorem finite_actualHighPositiveZeroKernelSum_le_variableBoundaryVisibleTail
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑ rho ∈ actualHighPositiveZeroSubtypeFinset sigma (H (m : ℝ))
          (variableBoundaryZeroPackage H beta (m : ℝ)),
        ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
          variableBoundaryTargetAmplitude beta (m : ℝ)) ≤
      variableBoundaryVisibleNormalizedKernelTail
        (sigma := sigma) H beta m := by
  let S := variableBoundaryZeroPackage H beta (m : ℝ)
  let s := actualHighPositiveZeroSubtypeFinset sigma (H (m : ℝ)) S
  let e := actualCarlsonPositiveZeroIndexEmbedding sigma
  let term := fun index : ActualCarlsonPositiveZeroIndex sigma =>
    variableBoundaryVisibleWeightedPowerTerm H beta index m
  have hsum :
      (∑ rho ∈ s,
          ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
            variableBoundaryTargetAmplitude beta (m : ℝ)) =
        ∑ index ∈ s.map e, term index := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro rho hrho
    have hvisible := actualHighPositiveZeroSubtypeFinset_visible hrho
    have houtside := actualHighPositiveZeroSubtypeFinset_outside hrho
    have houtside' :
        rho.1 ∉ variableBoundaryZeroPackage H beta (m : ℝ) := by
      simpa [S] using houtside
    change
      ‖pntRelativeZeroContribution (m : ℝ) rho.1‖ /
          variableBoundaryTargetAmplitude beta (m : ℝ) =
        variableBoundaryVisibleWeightedPowerTerm H beta
          (actualCarlsonPositiveZeroIndexOf rho) m
    unfold variableBoundaryVisibleWeightedPowerTerm
    rw [actualCarlsonPositiveZero_indexOf]
    simp only [hvisible, houtside', if_true, if_false]
    rw [← actualCarlsonPositiveZero_indexOf rho]
    simpa [variableBoundaryTargetAmplitude, targetZeroPowerAmplitude] using
      normalized_actualCarlsonPositiveZeroKernel_eq_weightedPower
        (beta := beta (m : ℝ))
        (actualCarlsonPositiveZeroIndexOf rho)
        (Nat.zero_lt_of_lt hm)
  have hfinite :
      (∑ index ∈ s.map e, term index) ≤ ∑' index, term index :=
    (summable_variableBoundaryVisibleWeightedPowerTerm
      hhalf hone hright hm).sum_le_tsum
        (s.map e)
        (fun index _ =>
          variableBoundaryVisibleWeightedPowerTerm_nonneg H beta index m)
  have hkernel :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        (if |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ) then
          if actualCarlsonPositiveZero index ∈ S then 0
          else
            ‖pntRelativeZeroContribution (m : ℝ)
                (actualCarlsonPositiveZero index)‖ /
              variableBoundaryTargetAmplitude beta (m : ℝ)
        else 0) = term index := by
    intro index
    unfold term variableBoundaryVisibleWeightedPowerTerm
    dsimp [S]
    by_cases hvisible : |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ)
    · by_cases hmem :
          actualCarlsonPositiveZero index ∈
            variableBoundaryZeroPackage H beta (m : ℝ)
      · simp [hvisible, hmem]
      · simp only [hvisible, hmem, if_true, if_false]
        simpa [variableBoundaryTargetAmplitude,
          targetZeroPowerAmplitude] using
          normalized_actualCarlsonPositiveZeroKernel_eq_weightedPower
            (beta := beta (m : ℝ)) index (Nat.zero_lt_of_lt hm)
    · simp [hvisible]
  rw [hsum]
  calc
    (∑ index ∈ s.map e, term index) ≤ ∑' index, term index := hfinite
    _ = variableBoundaryVisibleNormalizedKernelTail
          (sigma := sigma) H beta m := by
      unfold variableBoundaryVisibleNormalizedKernelTail
      symm
      exact tsum_congr hkernel

/-- Explicit low positive strip outside the moving package. -/
noncomputable def variableBoundaryLowPositiveNormalizedSum
    (sigma : ℝ) (H beta : ℝ → ℝ) (m : ℕ) : ℝ :=
  ‖∑ rho ∈
      (positiveNontrivialZerosOutsideClusterFinset
        (H (m : ℝ)) (variableBoundaryZeroPackage H beta (m : ℝ))).filter
          (fun rho => rho.re ≤ sigma),
      pntRelativeZeroContribution (m : ℝ) rho‖ /
    variableBoundaryTargetAmplitude beta (m : ℝ)

theorem variableBoundaryVisiblePositiveTailMajorized_low
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta) :
    VariableBoundaryVisiblePositiveTailMajorized
      (sigma := sigma) H beta
      (variableBoundaryLowPositiveNormalizedSum sigma H beta) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  let S := variableBoundaryZeroPackage H beta (m : ℝ)
  let all := positiveNontrivialZerosOutsideClusterFinset (H (m : ℝ)) S
  let low := all.filter (fun rho => rho.re ≤ sigma)
  let high := actualHighPositiveZerosOutsideClusterFinset sigma (H (m : ℝ)) S
  let contribution : ℂ → ℂ :=
    fun rho => pntRelativeZeroContribution (m : ℝ) rho
  have hhigh : high = all.filter (fun rho => ¬rho.re ≤ sigma) := by
    ext rho
    simp [high, all, actualHighPositiveZerosOutsideClusterFinset]
  have hpartition :
      (∑ rho ∈ all, contribution rho) =
        (∑ rho ∈ low, contribution rho) +
          ∑ rho ∈ high, contribution rho := by
    rw [show low = all.filter (fun rho => rho.re ≤ sigma) by rfl, hhigh]
    exact (Finset.sum_filter_add_sum_filter_not
      all (fun rho => rho.re ≤ sigma) contribution).symm
  have hnorm :
      ‖∑ rho ∈ all, contribution rho‖ ≤
        ‖∑ rho ∈ low, contribution rho‖ +
          ∑ rho ∈ high, ‖contribution rho‖ := by
    rw [hpartition]
    exact (norm_add_le _ _).trans
      (add_le_add_right (norm_sum_le high contribution) _)
  have hamp : 0 < variableBoundaryTargetAmplitude beta (m : ℝ) := by
    unfold variableBoundaryTargetAmplitude targetZeroPowerAmplitude
    exact Real.rpow_pos_of_pos
      (by exact_mod_cast (Nat.zero_lt_of_lt hm)) _
  have hnormDiv := (div_le_div_iff_of_pos_right hamp).2 hnorm
  have hfinite :=
    finite_actualHighPositiveZeroKernelSum_le_variableBoundaryVisibleTail
      hhalf hone hright hm
  have hfinite' :
      (∑ rho ∈ high, ‖contribution rho‖) /
          variableBoundaryTargetAmplitude beta (m : ℝ) ≤
        variableBoundaryVisibleNormalizedKernelTail
          (sigma := sigma) H beta m := by
    rw [Finset.sum_div]
    rw [← sum_actualHighPositiveZeroSubtypeFinset sigma (H (m : ℝ)) S]
    exact hfinite
  unfold variableBoundaryPositiveNormalizedSum
  unfold variableBoundaryLowPositiveNormalizedSum
  change
    ‖∑ rho ∈ all, contribution rho‖ /
        variableBoundaryTargetAmplitude beta (m : ℝ) ≤ _
  change
    _ ≤ ‖∑ rho ∈ low, contribution rho‖ /
      variableBoundaryTargetAmplitude beta (m : ℝ) + _
  rw [add_div] at hnormDiv
  exact hnormDiv.trans (add_le_add (le_refl _) hfinite')

end

end PrimeNumberTheorem
