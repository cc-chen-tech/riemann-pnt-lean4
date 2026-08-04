import MathlibAux.DyadicDriftingGaussianSchur
import PrimeNumberTheorem.HalfIsolatedZetaDyadicAdapter
import PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity

/-!
# Actual target-normalized energy on one dyadic zeta block

This module filters the genuine bucket-labelled zeta block to one actual
Carlson shell after deleting an arbitrary finite set `S`.  It then isolates
the target-side part `re rho ≤ beta` and records its exact unit-bucket
occupancy.  Later results in this module apply the whole-Gram Schur estimate
and the actual Carlson reciprocal-square capacity bound to this finite block.

There is deliberately no finite-range aggregation, high-tail estimate,
smoothing, two-height transfer, detect-or-count cluster mass, or witness
input here.
-/

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Bucket-labelled actual Carlson-shell zeros surviving deletion by `S`. -/
noncomputable def actualSRelativeDyadicBucketPairs
    (S : Finset ℂ) (sigma : ℝ) (k : ℕ) : Finset (ℕ × ℂ) :=
  (zetaDyadicBucketPairs k).filter fun p =>
    p.2 ∈ actualCarlsonDyadicZeroShell sigma k \ S

@[simp]
theorem mem_actualSRelativeDyadicBucketPairs
    {S : Finset ℂ} {sigma : ℝ} {k : ℕ} {p : ℕ × ℂ} :
    p ∈ actualSRelativeDyadicBucketPairs S sigma k ↔
      p ∈ zetaDyadicBucketPairs k ∧
        p.2 ∈ actualCarlsonDyadicZeroShell sigma k \ S := by
  simp [actualSRelativeDyadicBucketPairs]

/-- The target-side portion of the surviving actual block. -/
noncomputable def actualTargetDyadicBucketPairsExcluding
    (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) : Finset (ℕ × ℂ) :=
  (actualSRelativeDyadicBucketPairs S sigma k).filter fun p =>
    p.2.re ≤ beta

@[simp]
theorem mem_actualTargetDyadicBucketPairsExcluding
    {S : Finset ℂ} {sigma beta : ℝ} {k : ℕ} {p : ℕ × ℂ} :
    p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k ↔
      p ∈ actualSRelativeDyadicBucketPairs S sigma k ∧ p.2.re ≤ beta := by
  simp [actualTargetDyadicBucketPairsExcluding]

private theorem actualTargetDyadicBucketPairsExcluding_snd_inj
    (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    Set.InjOn Prod.snd
      (actualTargetDyadicBucketPairsExcluding S sigma beta k :
        Set (ℕ × ℂ)) := by
  intro p hp q hq hpq
  apply zetaDyadicBucketPairs_snd_inj k
  · exact (mem_actualSRelativeDyadicBucketPairs.mp
      (mem_actualTargetDyadicBucketPairsExcluding.mp hp).1).1
  · exact (mem_actualSRelativeDyadicBucketPairs.mp
      (mem_actualTargetDyadicBucketPairsExcluding.mp hq).1).1
  · exact hpq

/-- Forgetting bucket labels lands inside the S-relative actual Carlson strip.

This is intentionally a subset statement.  The bucket block has upper-open
height while the actual Carlson shell has upper-closed height.
-/
theorem image_snd_actualTargetDyadicBucketPairsExcluding_subset
    (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    (actualTargetDyadicBucketPairsExcluding S sigma beta k).image Prod.snd ⊆
      actualCarlsonDyadicZeroStrip sigma beta k \ S := by
  intro rho hrho
  rcases Finset.mem_image.mp hrho with ⟨p, hp, rfl⟩
  have hpTarget := mem_actualTargetDyadicBucketPairsExcluding.mp hp
  have hpSurviving := mem_actualSRelativeDyadicBucketPairs.mp hpTarget.1
  have hpShell := Finset.mem_sdiff.mp hpSurviving.2
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨hpShell.1, hpTarget.2⟩, hpShell.2⟩

/-- If no surviving actual shell zero is farther right than `beta`, then the
surviving source pairs are exactly the target pairs. -/
theorem actualSRelativeDyadicBucketPairs_eq_target_of_re_le
    {S : Finset ℂ} {sigma beta : ℝ} {k : ℕ}
    (hre : ∀ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
      rho.re ≤ beta) :
    actualSRelativeDyadicBucketPairs S sigma k =
      actualTargetDyadicBucketPairsExcluding S sigma beta k := by
  ext p
  constructor
  · intro hp
    exact mem_actualTargetDyadicBucketPairsExcluding.mpr
      ⟨hp, hre p.2 (mem_actualSRelativeDyadicBucketPairs.mp hp).2⟩
  · intro hp
    exact (mem_actualTargetDyadicBucketPairsExcluding.mp hp).1

/-- Maximum cardinality of an actual target fibre in one dyadic block. -/
noncomputable def actualTargetDyadicOccupancy
    (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) : ℕ :=
  ((actualTargetDyadicBucketPairsExcluding S sigma beta k).image Prod.fst).sup
    (fun n =>
      ((actualTargetDyadicBucketPairsExcluding S sigma beta k).filter
        (fun p => p.1 = n)).card)

/-- Every actual target unit-bucket fibre is bounded by the exact block
occupancy, including labels absent from the block. -/
theorem actualTargetDyadicBucket_fibre_card_le_occupancy
    (S : Finset ℂ) (sigma beta : ℝ) (k n : ℕ) :
    ((actualTargetDyadicBucketPairsExcluding S sigma beta k).filter
      (fun p => p.1 = n)).card ≤
        actualTargetDyadicOccupancy S sigma beta k := by
  classical
  let P := actualTargetDyadicBucketPairsExcluding S sigma beta k
  by_cases hn : n ∈ P.image Prod.fst
  · change
      (P.filter (fun p => p.1 = n)).card ≤
        (P.image Prod.fst).sup
          (fun j => (P.filter (fun p => p.1 = j)).card)
    exact Finset.le_sup
      (α := ℕ)
      (f := fun j : ℕ => (P.filter (fun p => p.1 = j)).card)
      hn
  · have hempty : P.filter (fun p => p.1 = n) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp hpn
      apply hn
      exact Finset.mem_image.mpr ⟨p, hp, hpn⟩
    simp [actualTargetDyadicOccupancy, P, hempty]

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
