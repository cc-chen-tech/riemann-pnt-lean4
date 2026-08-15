import PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge
import PrimeNumberTheorem.HalfIsolatedZetaDyadicAdapter

/-!
# Excluded dyadic zeta Gram to full square mass

This module instantiates the existing drifting Gaussian Schur theorem directly
on the actual right dyadic zeta block after deleting a finite zero set `S`.
The Gram index set and the square-mass index set are therefore identical.
-/

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

open Complex
open scoped BigOperators

noncomputable section

/-- The actual drifting Gaussian Gram on one right dyadic block after deleting `S`. -/
def zetaRightDyadicGaussianGramExcluding
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) (t m : ℝ) : ℝ :=
  MathlibAux.dyadicDriftingGaussianGram
    (zetaRightDyadicPairsExcluding beta k S)
    (zetaDyadicBaseMass x beta)
    (zetaDyadicBackwardDrift beta)
    (fun p => p.2.im) t m

private theorem zetaDyadicBaseMass_nonneg_excluding
    {x beta : ℝ} (hx : 0 < x) (p : ℕ × ℂ) :
    0 ≤ zetaDyadicBaseMass x beta p := by
  exact mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (norm_nonneg p.2))
    (Real.rpow_nonneg hx.le _)

private theorem zetaRightDyadic_frequency_gap_excluding
    {beta : ℝ} {k : ℕ} {S : Finset ℂ} {p q : ℕ × ℂ}
    (hp : p ∈ zetaRightDyadicPairsExcluding beta k S)
    (hq : q ∈ zetaRightDyadicPairsExcluding beta k S) :
    (((p.1).dist q.1 - 1 : ℕ) : ℝ) ≤ |p.2.im - q.2.im| := by
  have hpRight := (Finset.mem_filter.mp hp).1
  have hqRight := (Finset.mem_filter.mp hq).1
  have hpBucket := (mem_zetaDyadicBucketPairs.mp
    (mem_zetaRightDyadicBucketPairs.mp hpRight).1).2
  have hqBucket := (mem_zetaDyadicBucketPairs.mp
    (mem_zetaRightDyadicBucketPairs.mp hqRight).1).2
  have hpBounds := (Finset.mem_filter.mp hpBucket).2
  have hqBounds := (Finset.mem_filter.mp hqBucket).2
  exact (MathlibAux.natDist_sub_one_le_abs_sub_of_mem_unit
    hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2).trans
      (abs_abs_sub_abs_le_abs_sub p.2.im q.2.im)

/--
The excluded actual-zeta Gram is controlled by the square mass on the same
excluded finite set under a unit-bucket occupancy cap.
-/
theorem zetaRightDyadicGaussianGramExcluding_le_occupancy_mul_fullMass
    {x beta t m : ℝ} (k occupancy : ℕ) (S : Finset ℂ)
    (hx : 0 < x) (ht : 0 ≤ t) (hm : 1 ≤ m)
    (hoccupancy : ∀ n ∈
      (zetaRightDyadicPairsExcluding beta k S).image Prod.fst,
      ((zetaRightDyadicPairsExcluding beta k S).filter
        fun p => p.1 = n).card ≤ occupancy + 1) :
    zetaRightDyadicGaussianGramExcluding x beta k S t m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ((occupancy + 1 : ℕ) : ℝ) *
          zetaRightDyadicFullMassSquareExcluding x beta k S := by
  unfold zetaRightDyadicGaussianGramExcluding
    zetaRightDyadicFullMassSquareExcluding
  apply MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq
    (bucket := Prod.fst) (occupancy := occupancy)
  · exact ht
  · exact hm
  · intro p _hp
    exact zetaDyadicBaseMass_nonneg_excluding hx p
  · intro p hp
    exact sub_nonpos.mpr
      (mem_zetaRightDyadicBucketPairs.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq
    exact zetaRightDyadic_frequency_gap_excluding hp hq
  · exact hoccupancy

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
