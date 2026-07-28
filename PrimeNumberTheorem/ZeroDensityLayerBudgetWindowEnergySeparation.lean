import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowSecondMomentBadCount

/-!
# Window energy separation

This module gives a quantitative finite-window criterion ensuring that a main
sequence has strictly more threshold-large points than a complementary
sequence.

The main-sequence lower energy and pointwise cap force more than `K` large
main points.  The complementary upper energy forces fewer than `K` bad
points.  This is the arithmetic shape needed before inserting local
mean-square and zero-density estimates.
-/

namespace PrimeNumberTheorem

/-- A quantitative second-moment budget bounds the threshold-bad count by an
arbitrary natural number `K`. -/
theorem filter_card_lt_of_sum_sq_lt_count_mul_sq
    (G : Finset ℕ) (u : ℕ → ℝ) (K : ℕ) {threshold : ℝ}
    (hthreshold : 0 < threshold)
    (hsum :
      (∑ m ∈ G.filter (fun n => threshold ≤ |u n|), (u m) ^ 2) <
        (K : ℝ) * threshold ^ 2) :
    (G.filter (fun n => threshold ≤ |u n|)).card < K := by
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
        (K : ℝ) * threshold ^ 2 := by
    simpa [B] using hsum
  have hthresholdSq : 0 < threshold ^ 2 := pow_pos hthreshold 2
  have hcardReal : (B.card : ℝ) < (K : ℝ) := by
    nlinarith
  exact_mod_cast hcardReal

/-- A lower square-sum bound and a pointwise cap force more than `K`
threshold-large main points. -/
theorem count_lt_filter_card_of_baseline_add_count_gap_lt_sum_sq
    (G : Finset ℕ) (main : ℕ → ℝ) (K : ℕ)
    {threshold cap : ℝ}
    (hthreshold : 0 ≤ threshold)
    (hthresholdCap : threshold < cap)
    (hcap : ∀ m ∈ G, |main m| ≤ cap)
    (henergy :
      (G.card : ℝ) * threshold ^ 2 +
          (K : ℝ) * (cap ^ 2 - threshold ^ 2) <
        ∑ m ∈ G, (main m) ^ 2) :
    K < (G.filter (fun m => threshold ≤ |main m|)).card := by
  let B := G.filter (fun m => threshold ≤ |main m|)
  have hpoint :
      ∀ m ∈ G,
        (main m) ^ 2 ≤
          threshold ^ 2 +
            if threshold ≤ |main m| then
              cap ^ 2 - threshold ^ 2
            else 0 := by
    intro m hm
    by_cases hmLarge : threshold ≤ |main m|
    · simp only [hmLarge, if_true]
      have hmCap := hcap m hm
      have hsq : |main m| ^ 2 ≤ cap ^ 2 := by
        nlinarith [abs_nonneg (main m)]
      rw [sq_abs] at hsq
      nlinarith
    · simp only [hmLarge, if_false, add_zero]
      have hmSmall : |main m| < threshold := lt_of_not_ge hmLarge
      have hsq : |main m| ^ 2 ≤ threshold ^ 2 := by
        nlinarith [abs_nonneg (main m)]
      simpa only [sq_abs] using hsq
  have hupper :
      (∑ m ∈ G, (main m) ^ 2) ≤
        (G.card : ℝ) * threshold ^ 2 +
          (B.card : ℝ) * (cap ^ 2 - threshold ^ 2) := by
    calc
      (∑ m ∈ G, (main m) ^ 2) ≤
          ∑ m ∈ G,
            (threshold ^ 2 +
              if threshold ≤ |main m| then
                cap ^ 2 - threshold ^ 2
              else 0) :=
        Finset.sum_le_sum fun m hm => hpoint m hm
      _ = (G.card : ℝ) * threshold ^ 2 +
          (B.card : ℝ) * (cap ^ 2 - threshold ^ 2) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · rw [Finset.sum_ite]
          simp [B]
          ring
  have hgap : 0 < cap ^ 2 - threshold ^ 2 := by
    nlinarith
  have hcardReal : (K : ℝ) < (B.card : ℝ) := by
    nlinarith
  have hcard : K < B.card := by
    exact_mod_cast hcardReal
  simpa [B] using hcard

/-- A far-window package containing exactly the two quantitative energy
budgets needed for strict main-good versus complementary-bad separation. -/
def HasFarWindowEnergySeparation
    (main extension : ℕ → ℝ)
    (mainThreshold extensionThreshold mainCap : ℝ) : Prop :=
  ∀ M : ℕ, ∃ G : Finset ℕ, ∃ K : ℕ,
    (∀ m ∈ G, M ≤ m) ∧
    (∀ m ∈ G, |main m| ≤ mainCap) ∧
    ((G.card : ℝ) * mainThreshold ^ 2 +
          (K : ℝ) * (mainCap ^ 2 - mainThreshold ^ 2) <
        ∑ m ∈ G, (main m) ^ 2) ∧
    ((∑ m ∈ G.filter
          (fun n => extensionThreshold ≤ |extension n|),
        (extension m) ^ 2) <
      (K : ℝ) * extensionThreshold ^ 2)

/-- Window energy separation implies the cardinality advantage consumed by
the anti-cancellation transfer. -/
theorem HasFarWindowEnergySeparation.toWindowCardAdvantage
    {main extension : ℕ → ℝ}
    {mainThreshold extensionThreshold mainCap : ℝ}
    (hmainThreshold : 0 ≤ mainThreshold)
    (hmainCap : mainThreshold < mainCap)
    (hextensionThreshold : 0 < extensionThreshold)
    (henergy :
      HasFarWindowEnergySeparation
        main extension mainThreshold extensionThreshold mainCap) :
    HasFarWindowCardAdvantage
      (fun m => mainThreshold ≤ |main m|)
      (fun m => extensionThreshold ≤ |extension m|) := by
  intro M
  rcases henergy M with
    ⟨G, K, hfar, hcap, hmainEnergy, hextensionEnergy⟩
  let Gmain := G.filter (fun m => mainThreshold ≤ |main m|)
  let B := G.filter (fun m => extensionThreshold ≤ |extension m|)
  refine ⟨Gmain, B, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact hfar m (Finset.mem_filter.mp hm).1
  · intro m hm
    exact (Finset.mem_filter.mp hm).2
  · intro m hmGmain hmBad
    exact
      Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hmGmain).1, hmBad⟩
  · have hbadCount :
        (G.filter
          (fun m => extensionThreshold ≤ |extension m|)).card < K :=
      filter_card_lt_of_sum_sq_lt_count_mul_sq
        G extension K hextensionThreshold hextensionEnergy
    have hmainCount :
        K < (G.filter (fun m => mainThreshold ≤ |main m|)).card :=
      count_lt_filter_card_of_baseline_add_count_gap_lt_sum_sq
        G main K hmainThreshold hmainCap hcap hmainEnergy
    simpa [B, Gmain] using lt_trans hbadCount hmainCount

end PrimeNumberTheorem
