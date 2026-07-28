import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowCountAntiCancellation

/-!
# Window second moments bound bad-point counts

This module supplies the finite arithmetic bridge needed by the window-count
anti-cancellation interface.  A positive threshold and a strict second-moment
budget force the number of threshold-bad points to be strictly smaller than
the ambient window.

The sequence here should be read as a normalized complementary contribution.
No zeta-specific second-moment estimate is asserted.
-/

namespace PrimeNumberTheorem

/-- A far-window second-moment certificate for a good predicate and a
normalized complementary sequence. -/
def HasFarWindowSecondMomentAdvantage
    (good : ℕ → Prop) (u : ℕ → ℝ) (threshold : ℝ) : Prop :=
  ∀ M : ℕ, ∃ G : Finset ℕ,
    (∀ m ∈ G, M ≤ m) ∧
    (∀ m ∈ G, good m) ∧
    (∑ m ∈ G.filter (fun n => threshold ≤ |u n|), (u m) ^ 2) <
      (G.card : ℝ) * threshold ^ 2

/-- A strict second-moment budget bounds the threshold-bad subset strictly
below the ambient window cardinality. -/
theorem filter_card_lt_of_sum_sq_lt_card_mul_sq
    (G : Finset ℕ) (u : ℕ → ℝ) {threshold : ℝ}
    (hthreshold : 0 < threshold)
    (hsum :
      (∑ m ∈ G.filter (fun n => threshold ≤ |u n|), (u m) ^ 2) <
        (G.card : ℝ) * threshold ^ 2) :
    (G.filter (fun n => threshold ≤ |u n|)).card < G.card := by
  let B := G.filter (fun n => threshold ≤ |u n|)
  have hterm :
      ∀ m ∈ B, threshold ^ 2 ≤ (u m) ^ 2 := by
    intro m hm
    have hmBad : threshold ≤ |u m| := (Finset.mem_filter.mp hm).2
    calc
      threshold ^ 2 ≤ |u m| ^ 2 := by
        nlinarith [abs_nonneg (u m)]
      _ = (u m) ^ 2 := sq_abs (u m)
  have hlower :
      (B.card : ℝ) * threshold ^ 2 ≤
        ∑ m ∈ B, (u m) ^ 2 := by
    calc
      (B.card : ℝ) * threshold ^ 2 =
          ∑ _m ∈ B, threshold ^ 2 := by simp
      _ ≤ ∑ m ∈ B, (u m) ^ 2 :=
        Finset.sum_le_sum fun m hm => hterm m hm
  have hsumB :
      (∑ m ∈ B, (u m) ^ 2) <
        (G.card : ℝ) * threshold ^ 2 := by
    simpa [B] using hsum
  have hthresholdSq : 0 < threshold ^ 2 := pow_pos hthreshold 2
  have hcardReal : (B.card : ℝ) < (G.card : ℝ) := by
    nlinarith
  have hcard : B.card < G.card := by
    exact_mod_cast hcardReal
  simpa [B] using hcard

/-- A far-window second-moment certificate yields the exact cardinality
advantage required by the anti-cancellation transfer. -/
theorem HasFarWindowSecondMomentAdvantage.toWindowCardAdvantage
    {good : ℕ → Prop} {u : ℕ → ℝ} {threshold : ℝ}
    (hthreshold : 0 < threshold)
    (hsecond :
      HasFarWindowSecondMomentAdvantage good u threshold) :
    HasFarWindowCardAdvantage
      good (fun m => threshold ≤ |u m|) := by
  intro M
  rcases hsecond M with ⟨G, hfar, hgood, hsum⟩
  let B := G.filter (fun m => threshold ≤ |u m|)
  refine ⟨G, B, hfar, hgood, ?_, ?_⟩
  · intro m hmG hmBad
    exact Finset.mem_filter.mpr ⟨hmG, hmBad⟩
  · exact
      filter_card_lt_of_sum_sq_lt_card_mul_sq
        G u hthreshold hsum

end PrimeNumberTheorem
