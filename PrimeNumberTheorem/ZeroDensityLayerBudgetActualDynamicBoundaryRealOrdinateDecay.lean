import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticLowLayer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualRealOrdinateExcludingCluster

/-!
# Real-ordinate decay outside a dynamic boundary package

The real-ordinate nontrivial-zero set is finite and fixed once the selected
height is nonnegative.  Zeros strictly left of the target boundary decay
pointwise after normalization.  A zero on the boundary is eventually included
in the moving equal-real-part package and therefore contributes zero to the
complement.  Finite dominated convergence then removes the complete
real-ordinate residual without a uniform strict gap.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Filter

/-- One fixed real-ordinate zero contribution, deleted when it belongs to the
current moving boundary package. -/
noncomputable def actualDynamicBoundaryRealOrdinateTerm
    (H : ℝ → ℝ) (beta : ℝ) (rho : ℂ) (m : ℕ) : ℝ :=
  if rho ∈ dynamicEqualRealPartZeroPackage H beta (m : ℝ) then 0
  else
    ‖pntRelativeZeroContribution (m : ℝ) rho‖ /
      targetZeroPowerAmplitude beta (m : ℝ)

theorem actualDynamicBoundaryRealOrdinateTerm_nonneg
    (H : ℝ → ℝ) (beta : ℝ) (rho : ℂ) (m : ℕ) :
    0 ≤ actualDynamicBoundaryRealOrdinateTerm H beta rho m := by
  unfold actualDynamicBoundaryRealOrdinateTerm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg m) _)

/-- Summing after deleting a finite set is the same as inserting a zero on
the deleted members. -/
theorem sum_sdiff_eq_sum_if_mem_zero
    {ι : Type*} [DecidableEq ι]
    (A S : Finset ι) (f : ι → ℝ) :
    (∑ x ∈ A \ S, f x) =
      ∑ x ∈ A, if x ∈ S then 0 else f x := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp
  | @insert a A ha ih =>
      by_cases hmem : a ∈ S
      · have hdiff : insert a A \ S = A \ S := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hxNotS⟩
            · exact False.elim (hxNotS (hx ▸ hmem))
            · exact ⟨hx, hxNotS⟩
          · rintro ⟨hx, hxNotS⟩
            exact ⟨Or.inr hx, hxNotS⟩
        rw [hdiff]
        simpa [ha, hmem] using ih
      · have hdiff : insert a A \ S = insert a (A \ S) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hxNotS⟩
            · exact Or.inl hx
            · exact Or.inr ⟨hx, hxNotS⟩
          · rintro (hx | ⟨hx, hxNotS⟩)
            · exact ⟨Or.inl hx, hx ▸ hmem⟩
            · exact ⟨Or.inr hx, hxNotS⟩
        have haDiff : a ∉ A \ S := by simp [ha]
        rw [hdiff, Finset.sum_insert haDiff, ih]
        simp [ha, hmem]

/--
Every fixed real-ordinate zero at or left of `beta` disappears after target
normalization: strict-left zeros decay, while boundary zeros are eventually
deleted by the moving package.
-/
theorem actualDynamicBoundaryRealOrdinateTerm_tendsto_zero
    {H : ℝ → ℝ} {beta : ℝ} {rho : ℂ}
    (hH : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hrho :
      rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅)
    (hright : rho.re ≤ beta) :
    Tendsto
      (actualDynamicBoundaryRealOrdinateTerm H beta rho)
      atTop (nhds 0) := by
  rcases mem_realOrdinateNontrivialZerosFinset.mp
      (Finset.mem_sdiff.mp hrho).1 with
    ⟨hrhoZero, hrhoIm⟩
  have hzero :=
    (mem_nontrivialZerosFinset.mp hrhoZero).1
  rcases lt_or_eq_of_le hright with hstrict | heq
  · have hdecay :=
      (tendsto_norm_pntRelativeZeroContribution_div_targetZeroPowerAmplitude
        hstrict).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have htermNonneg :
        ∀ᶠ m : ℕ in atTop,
          0 ≤ actualDynamicBoundaryRealOrdinateTerm H beta rho m := by
      filter_upwards with m
      exact actualDynamicBoundaryRealOrdinateTerm_nonneg H beta rho m
    refine squeeze_zero' htermNonneg ?_ hdecay
    filter_upwards with m
    unfold actualDynamicBoundaryRealOrdinateTerm
    split_ifs
    · exact div_nonneg (norm_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    · exact le_rfl
  · have hnonneg :
        ∀ᶠ m : ℕ in atTop, 0 ≤ H (m : ℝ) :=
      hH.eventually (eventually_ge_atTop (0 : ℝ))
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [hnonneg] with m hm
    have hmem :
        rho ∈ dynamicEqualRealPartZeroPackage H beta (m : ℝ) := by
      rw [mem_dynamicEqualRealPartZeroPackage]
      refine ⟨hzero, ?_, heq⟩
      simpa [hrhoIm] using hm
    simp [actualDynamicBoundaryRealOrdinateTerm, hmem]

/-- The finite sum of all fixed real-ordinate moving-complement terms tends
to zero. -/
theorem
    actualDynamicBoundaryRealOrdinateTerm_sum_tendsto_zero
    {H : ℝ → ℝ} {beta : ℝ}
    (hH : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hright :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta) :
    Tendsto
      (fun m : ℕ =>
        ∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
          actualDynamicBoundaryRealOrdinateTerm H beta rho m)
      atTop (nhds 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finset_sum
      (realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅)
      (fun rho hrho =>
        actualDynamicBoundaryRealOrdinateTerm_tendsto_zero
          hH hrho (hright rho hrho))

/--
The complete real-ordinate zero complement outside the moving boundary
package is negligible at the target amplitude under a non-strict right-edge
condition.
-/
theorem actualDynamicBoundaryRealNormalizedSum_tendsto_zero
    {H : ℝ → ℝ} {beta : ℝ}
    (hH : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hright :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta) :
    Tendsto
      (actualDynamicBoundaryRealNormalizedSum H beta)
      atTop (nhds 0) := by
  have hsum :=
    actualDynamicBoundaryRealOrdinateTerm_sum_tendsto_zero hH hright
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  · have hnonneg :
        ∀ᶠ m : ℕ in atTop, 0 ≤ H (m : ℝ) :=
      hH.eventually (eventually_ge_atTop (0 : ℝ))
    have hAmplitude :
        ∀ᶠ m : ℕ in atTop,
          0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta)
    filter_upwards [hnonneg, hAmplitude] with m hm hAmp
    let S := dynamicEqualRealPartZeroPackage H beta (m : ℝ)
    let base := realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅
    have hset :
        realOrdinateNontrivialZerosOutsideClusterFinset
            (H (m : ℝ)) S =
          realOrdinateNontrivialZerosFinset 0 \ S := by
      unfold realOrdinateNontrivialZerosOutsideClusterFinset
      rw [realOrdinateNontrivialZerosFinset_eq_zeroHeight hm]
    have hnorm :
        ‖∑ rho ∈ realOrdinateNontrivialZerosFinset 0 \ S,
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          ∑ rho ∈ realOrdinateNontrivialZerosFinset 0 \ S,
            ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
      norm_sum_le _ _
    have hterms :
        (∑ rho ∈ realOrdinateNontrivialZerosFinset 0 \ S,
            ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
            targetZeroPowerAmplitude beta (m : ℝ) =
          ∑ rho ∈ base,
            actualDynamicBoundaryRealOrdinateTerm H beta rho m := by
      dsimp [base, S]
      rw [Finset.sum_div]
      unfold actualDynamicBoundaryRealOrdinateTerm
      simp only [realOrdinateNontrivialZerosOutsideClusterFinset,
        Finset.sdiff_empty]
      exact sum_sdiff_eq_sum_if_mem_zero
        (realOrdinateNontrivialZerosFinset 0)
        (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
        (fun rho =>
          ‖pntRelativeZeroContribution (m : ℝ) rho‖ /
            targetZeroPowerAmplitude beta (m : ℝ))
    unfold actualDynamicBoundaryRealNormalizedSum
    rw [dynamicRealOrdinateOutsideClusterPNTZeroTailNorm, hset]
    calc
      ‖∑ rho ∈ realOrdinateNontrivialZerosFinset 0 \ S,
          pntRelativeZeroContribution (m : ℝ) rho‖ /
          targetZeroPowerAmplitude beta (m : ℝ)
          ≤
            (∑ rho ∈ realOrdinateNontrivialZerosFinset 0 \ S,
              ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
              targetZeroPowerAmplitude beta (m : ℝ) :=
        (div_le_div_iff_of_pos_right hAmp).2 hnorm
      _ =
          ∑ rho ∈ base,
            actualDynamicBoundaryRealOrdinateTerm H beta rho m :=
        hterms

end PrimeNumberTheorem
