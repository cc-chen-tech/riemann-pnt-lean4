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

/-- Target-normalized reciprocal-multiplicity mass at forward-window origin
`a`. -/
noncomputable def actualTargetDyadicBaseMass
    (beta a : ℝ) (p : ℕ × ℂ) : ℝ :=
  zeroReciprocalMultiplicityCoefficient p.2 *
    Real.exp ((p.2.re - beta) * a)

/-- Forward motion from the origin has nonpositive drift on the target side. -/
def actualTargetDyadicForwardDrift
    (beta : ℝ) (p : ℕ × ℂ) : ℝ :=
  p.2.re - beta

/-- Whole Gaussian Gram energy of the surviving actual dyadic source block. -/
noncomputable def actualSRelativeTargetDyadicGaussianGram
    (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) (t m : ℝ) : ℝ :=
  MathlibAux.dyadicDriftingGaussianGram
    (actualSRelativeDyadicBucketPairs S sigma k)
    (actualTargetDyadicBaseMass beta a)
    (actualTargetDyadicForwardDrift beta)
    (fun p => p.2.im) t m

private theorem actualTargetDyadicBaseMass_nonneg
    (beta a : ℝ) (p : ℕ × ℂ) :
    0 ≤ actualTargetDyadicBaseMass beta a p := by
  unfold actualTargetDyadicBaseMass zeroReciprocalMultiplicityCoefficient
  exact mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (Real.exp_pos _).le

private theorem actualTargetDyadic_frequency_gap
    {S : Finset ℂ} {sigma beta : ℝ} {k : ℕ} {p q : ℕ × ℂ}
    (hp : p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k)
    (hq : q ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k) :
    (((p.1).dist q.1 - 1 : ℕ) : ℝ) ≤ |p.2.im - q.2.im| := by
  have hpZeta := (mem_actualSRelativeDyadicBucketPairs.mp
    (mem_actualTargetDyadicBucketPairsExcluding.mp hp).1).1
  have hqZeta := (mem_actualSRelativeDyadicBucketPairs.mp
    (mem_actualTargetDyadicBucketPairsExcluding.mp hq).1).1
  have hpBucket := (mem_zetaDyadicBucketPairs.mp hpZeta).2
  have hqBucket := (mem_zetaDyadicBucketPairs.mp hqZeta).2
  have hpBounds := (Finset.mem_filter.mp hpBucket).2
  have hqBounds := (Finset.mem_filter.mp hqBucket).2
  exact (MathlibAux.natDist_sub_one_le_abs_sub_of_mem_unit
    hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2).trans
      (abs_abs_sub_abs_le_abs_sub p.2.im q.2.im)

/-- The squared target masses inject into the full S-relative actual Carlson
reciprocal-square capacity. -/
theorem sum_actualTargetDyadicBaseMass_sq_le_capacity
    (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) (ha : 0 ≤ a) :
    (∑ p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k,
      actualTargetDyadicBaseMass beta a p ^ 2) ≤
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
          sigma beta k S := by
  classical
  let P := actualTargetDyadicBucketPairsExcluding S sigma beta k
  let c : ℂ → ℝ := zeroReciprocalMultiplicityCoefficient
  have hmass : ∀ p ∈ P,
      actualTargetDyadicBaseMass beta a p ^ 2 ≤ c p.2 ^ 2 := by
    intro p hp
    have htarget := (mem_actualTargetDyadicBucketPairsExcluding.mp hp).2
    have hcoeff : 0 ≤ c p.2 := by
      dsimp only [c]
      unfold zeroReciprocalMultiplicityCoefficient
      exact div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    have hexp : Real.exp ((p.2.re - beta) * a) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htarget) ha)
    have hbase : actualTargetDyadicBaseMass beta a p ≤ c p.2 := by
      unfold actualTargetDyadicBaseMass
      exact mul_le_of_le_one_right hcoeff hexp
    exact (sq_le_sq₀ (actualTargetDyadicBaseMass_nonneg beta a p) hcoeff).2 hbase
  have hinj : ∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → p = q := by
    intro p hp q hq hpq
    exact actualTargetDyadicBucketPairsExcluding_snd_inj S sigma beta k hp hq hpq
  have himage : P.image Prod.snd ⊆
      actualCarlsonDyadicZeroStrip sigma beta k \ S := by
    exact image_snd_actualTargetDyadicBucketPairsExcluding_subset
      S sigma beta k
  change (∑ p ∈ P, actualTargetDyadicBaseMass beta a p ^ 2) ≤ _
  calc
    (∑ p ∈ P, actualTargetDyadicBaseMass beta a p ^ 2) ≤
        ∑ p ∈ P, c p.2 ^ 2 := Finset.sum_le_sum hmass
    _ = ∑ rho ∈ P.image Prod.snd, c rho ^ 2 := by
      exact (Finset.sum_image
        (f := fun rho : ℂ => c rho ^ 2) hinj).symm
    _ ≤ ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma beta k \ S,
        c rho ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro rho _hrho _himage
        exact sq_nonneg (c rho))
    _ = actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
          sigma beta k S := by
      simp only [actualCarlsonDyadicStripSquareReciprocalCapacityExcluding,
        c, zeroReciprocalMultiplicityCoefficient, div_pow]

/-- A surviving actual shell zero is strictly farther right than `beta`, or
the whole source Gram is controlled by target occupancy and actual capacity. -/
theorem actualSRelativeDyadic_fartherRight_or_gram_le_capacity
    (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) {t m : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hm : 1 ≤ m) :
    (∃ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
      beta < rho.re) ∨
      actualSRelativeTargetDyadicGaussianGram S sigma beta a k t m ≤
        MathlibAux.gaussianBucketSchurConstant *
          (1 + (actualTargetDyadicOccupancy S sigma beta k : ℝ)) *
            actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
              sigma beta k S := by
  by_cases hfar : ∃ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
      beta < rho.re
  · exact Or.inl hfar
  · right
    have hre : ∀ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
        rho.re ≤ beta := by
      intro rho hrho
      exact le_of_not_gt fun hright => hfar ⟨rho, hrho, hright⟩
    have hsets := actualSRelativeDyadicBucketPairs_eq_target_of_re_le hre
    unfold actualSRelativeTargetDyadicGaussianGram
    rw [hsets]
    calc
      MathlibAux.dyadicDriftingGaussianGram
          (actualTargetDyadicBucketPairsExcluding S sigma beta k)
          (actualTargetDyadicBaseMass beta a)
          (actualTargetDyadicForwardDrift beta)
          (fun p => p.2.im) t m ≤
          MathlibAux.gaussianBucketSchurConstant *
            (((actualTargetDyadicOccupancy S sigma beta k + 1 : ℕ) : ℝ)) *
              ∑ p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k,
                actualTargetDyadicBaseMass beta a p ^ 2 := by
        apply MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq
          (bucket := Prod.fst)
          (occupancy := actualTargetDyadicOccupancy S sigma beta k)
        · exact ht
        · exact hm
        · intro p _hp
          exact actualTargetDyadicBaseMass_nonneg beta a p
        · intro p hp
          exact sub_nonpos.mpr
            (mem_actualTargetDyadicBucketPairsExcluding.mp hp).2
        · intro p hp q hq
          exact actualTargetDyadic_frequency_gap hp hq
        · intro n hn
          exact (actualTargetDyadicBucket_fibre_card_le_occupancy
            S sigma beta k n).trans (by omega)
      _ = MathlibAux.gaussianBucketSchurConstant *
            (1 + (actualTargetDyadicOccupancy S sigma beta k : ℝ)) *
              ∑ p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k,
                actualTargetDyadicBaseMass beta a p ^ 2 := by
        have hcast :
            (((actualTargetDyadicOccupancy S sigma beta k + 1 : ℕ) : ℝ)) =
              1 + (actualTargetDyadicOccupancy S sigma beta k : ℝ) := by
          norm_num
          ring
        rw [hcast]
      _ ≤ MathlibAux.gaussianBucketSchurConstant *
            (1 + (actualTargetDyadicOccupancy S sigma beta k : ℝ)) *
              actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
                sigma beta k S := by
        exact mul_le_mul_of_nonneg_left
          (sum_actualTargetDyadicBaseMass_sq_le_capacity
            S sigma beta a k ha)
          (mul_nonneg MathlibAux.gaussianBucketSchurConstant_pos.le
            (by positivity))

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
