import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryVisibleCarlsonTail

/-!
# Monotone moving boundaries automatically absorb or separate fixed zeros

Once a fixed zero becomes visible, a monotone finite-height right edge has
only two possibilities.  Either the boundary eventually moves strictly to
its right, creating a permanent positive gap, or it never does, in which case
the pointwise right-edge inequality forces equality and the complete boundary
package absorbs the zero.
-/

namespace PrimeNumberTheorem

open Filter Complex

noncomputable section

/-- Cofinal height, monotone boundary, and the visible right-edge property
automatically imply absorption-or-gap for every indexed Carlson zero. -/
theorem variableBoundaryAbsorptionOrGap_of_monotone
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hH : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)))
    (hright : IsIndexedVariableBoundaryVisibleRightEdge
      (sigma := sigma) H beta) :
    VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta := by
  intro index
  have hspec := actualCarlsonPositiveZero_spec index
  have hheight :
      ∀ᶠ m : ℕ in atTop,
        |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ) :=
    (tendsto_atTop.1 hH) |(actualCarlsonPositiveZero index).im|
  obtain ⟨M, hM⟩ := eventually_atTop.mp hheight
  by_cases hcross :
      ∃ N : ℕ, M ≤ N ∧
        actualCarlsonPositiveZeroRealPart index < beta (N : ℝ)
  · rcases hcross with ⟨N, hMN, hstrict⟩
    let delta :=
      (beta (N : ℝ) - actualCarlsonPositiveZeroRealPart index) / 2
    have hdelta : 0 < delta := by
      dsimp [delta]
      linarith
    refine ⟨delta, hdelta, ?_⟩
    filter_upwards [eventually_ge_atTop N] with m hNm
    right
    have hmono : beta (N : ℝ) ≤ beta (m : ℝ) :=
      hbetaMono hNm
    dsimp [delta]
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [eventually_ge_atTop M] with m hMm
    left
    have hvis :
        |(actualCarlsonPositiveZero index).im| ≤ H (m : ℝ) :=
      hM m hMm
    have hreLe :
        actualCarlsonPositiveZeroRealPart index ≤ beta (m : ℝ) :=
      hright m index hvis
    have hnotStrict :
        ¬ actualCarlsonPositiveZeroRealPart index < beta (m : ℝ) := by
      intro hstrict
      exact hcross ⟨m, hMm, hstrict⟩
    have hreEq :
        actualCarlsonPositiveZeroRealPart index = beta (m : ℝ) :=
      le_antisymm hreLe (not_lt.mp hnotStrict)
    exact mem_variableBoundaryZeroPackage.mpr
      ⟨hspec.1, hvis, hreEq⟩

/-- The visible actual Carlson kernel tail therefore tends to zero for every
cofinal monotone boundary schedule satisfying the pointwise right edge. -/
theorem
    variableBoundaryVisibleNormalizedKernelTail_tendsto_zero_of_monotone
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hH : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)))
    (hright : IsIndexedVariableBoundaryVisibleRightEdge
      (sigma := sigma) H beta) :
    Tendsto
      (variableBoundaryVisibleNormalizedKernelTail
        (sigma := sigma) H beta)
      atTop (nhds 0) :=
  variableBoundaryVisibleNormalizedKernelTail_tendsto_zero
    hhalf hone hright
      (variableBoundaryAbsorptionOrGap_of_monotone hH hbetaMono hright)

end
end PrimeNumberTheorem
