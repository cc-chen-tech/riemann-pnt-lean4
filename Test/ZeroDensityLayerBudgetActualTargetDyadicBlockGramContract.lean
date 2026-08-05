import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetDyadicBlockGram

open Complex

namespace PrimeNumberTheorem.VKEdgePiOverTwo

example (S : Finset ℂ) (sigma : ℝ) (k : ℕ) :
    actualSRelativeDyadicBucketPairs S sigma k =
      (zetaDyadicBucketPairs k).filter
        (fun p => p.2 ∈ actualCarlsonDyadicZeroShell sigma k \ S) := rfl

example (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    actualTargetDyadicBucketPairsExcluding S sigma beta k =
      (actualSRelativeDyadicBucketPairs S sigma k).filter
        (fun p => p.2.re ≤ beta) := rfl

example {S : Finset ℂ} {sigma : ℝ} {k : ℕ} {p : ℕ × ℂ} :
    p ∈ actualSRelativeDyadicBucketPairs S sigma k ↔
      p ∈ zetaDyadicBucketPairs k ∧
        p.2 ∈ actualCarlsonDyadicZeroShell sigma k \ S :=
  mem_actualSRelativeDyadicBucketPairs

example {S : Finset ℂ} {sigma beta : ℝ} {k : ℕ} {p : ℕ × ℂ} :
    p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k ↔
      p ∈ actualSRelativeDyadicBucketPairs S sigma k ∧ p.2.re ≤ beta :=
  mem_actualTargetDyadicBucketPairsExcluding

example (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    (actualTargetDyadicBucketPairsExcluding S sigma beta k).image Prod.snd ⊆
      actualCarlsonDyadicZeroStrip sigma beta k \ S :=
  image_snd_actualTargetDyadicBucketPairsExcluding_subset S sigma beta k

example {S : Finset ℂ} {sigma beta : ℝ} {k : ℕ}
    (hre : ∀ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
      rho.re ≤ beta) :
    actualSRelativeDyadicBucketPairs S sigma k =
      actualTargetDyadicBucketPairsExcluding S sigma beta k :=
  actualSRelativeDyadicBucketPairs_eq_target_of_re_le hre

example (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    actualTargetDyadicOccupancy S sigma beta k =
      ((actualTargetDyadicBucketPairsExcluding S sigma beta k).image
          Prod.fst).sup
        (fun n =>
          ((actualTargetDyadicBucketPairsExcluding S sigma beta k).filter
            (fun p => p.1 = n)).card) := rfl

example {S : Finset ℂ} {sigma beta : ℝ} {k n : ℕ} :
    ((actualTargetDyadicBucketPairsExcluding S sigma beta k).filter
      (fun p => p.1 = n)).card ≤
        actualTargetDyadicOccupancy S sigma beta k :=
  actualTargetDyadicBucket_fibre_card_le_occupancy S sigma beta k n

example (beta a : ℝ) (p : ℕ × ℂ) :
    actualTargetDyadicBaseMass beta a p =
      zeroReciprocalMultiplicityCoefficient p.2 *
        Real.exp ((p.2.re - beta) * a) := rfl

example (beta : ℝ) (p : ℕ × ℂ) :
    actualTargetDyadicForwardDrift beta p = p.2.re - beta := rfl

example (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) (t m : ℝ) :
    actualSRelativeTargetDyadicGaussianGram S sigma beta a k t m =
      MathlibAux.dyadicDriftingGaussianGram
        (actualSRelativeDyadicBucketPairs S sigma k)
        (actualTargetDyadicBaseMass beta a)
        (actualTargetDyadicForwardDrift beta)
        (fun p => p.2.im) t m := rfl

example (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) (ha : 0 ≤ a) :
    (∑ p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k,
      actualTargetDyadicBaseMass beta a p ^ 2) ≤
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
          sigma beta k S :=
  sum_actualTargetDyadicBaseMass_sq_le_capacity S sigma beta a k ha

example (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) {t m : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hm : 1 ≤ m) :
    (∃ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
      beta < rho.re) ∨
      actualSRelativeTargetDyadicGaussianGram S sigma beta a k t m ≤
        MathlibAux.gaussianBucketSchurConstant *
          (1 + (actualTargetDyadicOccupancy S sigma beta k : ℝ)) *
            actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
              sigma beta k S :=
  actualSRelativeDyadic_fartherRight_or_gram_le_capacity
    S sigma beta a k ha ht hm

end PrimeNumberTheorem.VKEdgePiOverTwo
