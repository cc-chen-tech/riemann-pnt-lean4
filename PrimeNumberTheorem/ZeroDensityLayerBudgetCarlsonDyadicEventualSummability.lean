import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonDyadicReciprocalSummability

/-!
# Eventual dyadic Carlson comparison

Carlson's zero-density theorem supplies an asymptotic bound, so its dyadic
specialization controls only a tail of the shell sequence.  Summability is
unchanged by finitely many initial shells.  This module records that transfer
without strengthening an eventual Carlson estimate to an all-height estimate.
-/

namespace PrimeNumberTheorem

open Filter

/-- An eventual upper bound by the full dyadic Carlson reciprocal majorant
implies summability.  Finitely many shells below the eventual threshold are
retained rather than silently discarded from the sequence. -/
theorem summable_of_eventually_le_pntCarlsonDyadicLogFourthMajorant
    {mass : ℕ → ℝ} {C sigma : ℝ}
    (hmassNonneg : ∀ n, 0 ≤ mass n)
    (hmass :
      ∀ᶠ n : ℕ in atTop,
        mass n ≤ pntCarlsonDyadicLogFourthMajorant C sigma n)
    (hhalf : 1 / 2 < sigma) :
    Summable mass := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmass
  apply (summable_nat_add_iff N).mp
  exact Summable.of_nonneg_of_le
    (fun n => hmassNonneg (n + N))
    (fun n => hN (n + N) (Nat.le_add_left N n))
    ((summable_nat_add_iff N).mpr
      (summable_pntCarlsonDyadicLogFourthMajorant hhalf))

/-- Reciprocal-height normalization of an arbitrary dyadic counting
sequence.  The subsequent zeta specialization sets `count n` to
`zeroDensityCount sigma (2^n)`. -/
noncomputable def pntDyadicReciprocalWeightedCount
    (count : ℕ → ℝ) (n : ℕ) : ℝ :=
  count n / (2 : ℝ) ^ n

theorem pntDyadicReciprocalWeightedCount_nonneg
    {count : ℕ → ℝ} (hcount : ∀ n, 0 ≤ count n) (n : ℕ) :
    0 ≤ pntDyadicReciprocalWeightedCount count n := by
  exact div_nonneg (hcount n) (by positivity)

/-- Count-to-summability interface at dyadic heights.  It deliberately asks
only for the eventual normalized estimate that an actual Carlson certificate
provides. -/
theorem summable_pntDyadicReciprocalWeightedCount_of_eventually_le
    {count : ℕ → ℝ} {C sigma : ℝ}
    (hcount : ∀ n, 0 ≤ count n)
    (hbound :
      ∀ᶠ n : ℕ in atTop,
        pntDyadicReciprocalWeightedCount count n ≤
          pntCarlsonDyadicLogFourthMajorant C sigma n)
    (hhalf : 1 / 2 < sigma) :
    Summable (pntDyadicReciprocalWeightedCount count) := by
  exact
    summable_of_eventually_le_pntCarlsonDyadicLogFourthMajorant
      (pntDyadicReciprocalWeightedCount_nonneg hcount)
      hbound hhalf

end PrimeNumberTheorem
