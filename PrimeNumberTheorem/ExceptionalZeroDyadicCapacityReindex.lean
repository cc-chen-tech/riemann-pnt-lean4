import PrimeNumberTheorem.ExceptionalZeroTargetDyadicGramSchur

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

noncomputable section

/-- Linear reciprocal capacity of complementary dynamic packets in one dyadic block. -/
noncomputable def dynamicComplementDyadicLinearReciprocalCapacity
    (S : Finset ℂ) (T : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ dyadicUnitBucketIndexSet k,
    ∑ rho ∈ dynamicComplementZeroPacket S T n,
      (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2

theorem dynamicComplementZeroPacket_eq_zeroOrdinateUnitBucket_sdiff_of_dyadic
    (S : Finset ℂ) {T : ℝ} {k n : ℕ}
    (hn : n ∈ dyadicUnitBucketIndexSet k)
    (hT : (2 : ℝ) ^ (k + 1) ≤ T) :
    dynamicComplementZeroPacket S T n = zeroOrdinateUnitBucket n \ S := by
  ext rho
  constructor
  · intro hrho
    rcases Finset.mem_inter.mp hrho with ⟨hrhoBucket, hrhoRest⟩
    exact Finset.mem_sdiff.mpr ⟨hrhoBucket, (Finset.mem_sdiff.mp hrhoRest).2⟩
  · intro hrho
    rcases Finset.mem_sdiff.mp hrho with ⟨hrhoBucket, hrhoNotS⟩
    refine Finset.mem_inter.mpr ⟨hrhoBucket, Finset.mem_sdiff.mpr ⟨?_, hrhoNotS⟩⟩
    rcases Finset.mem_filter.mp hrhoBucket with ⟨hrhoFinite, hrhoLower, hrhoUpper⟩
    have hnUpper : n + 1 ≤ 2 ^ (k + 1) := by
      rcases Finset.mem_Icc.mp hn with ⟨_, hnUpper⟩
      have hpowPos : 0 < 2 ^ (k + 1) := by positivity
      omega
    have hnUpperReal : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast hnUpper
    apply mem_nontrivialZerosFinset.mpr
    refine ⟨(mem_nontrivialZerosFinset.mp hrhoFinite).1, ?_⟩
    exact hrhoUpper.le.trans (hnUpperReal.trans hT)

private theorem dyadicZeroBuckets_sdiff_pairwiseDisjoint
    (S : Finset ℂ) (k : ℕ) :
    (dyadicUnitBucketIndexSet k : Set ℕ).PairwiseDisjoint
      fun n => zeroOrdinateUnitBucket n \ S := by
  intro i hi j hj hij
  change Disjoint (zeroOrdinateUnitBucket i \ S) (zeroOrdinateUnitBucket j \ S)
  rw [Finset.disjoint_left]
  intro rho hri hrj
  rcases Finset.mem_sdiff.mp hri with ⟨hriBucket, _⟩
  rcases Finset.mem_sdiff.mp hrj with ⟨hrjBucket, _⟩
  rcases Finset.mem_filter.mp hriBucket with ⟨_, hriLower, hriUpper⟩
  rcases Finset.mem_filter.mp hrjBucket with ⟨_, hrjLower, hrjUpper⟩
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hijReal : (i : ℝ) + 1 ≤ j := by
      exact_mod_cast Nat.succ_le_iff.mpr hij
    linarith
  · have hjiReal : (j : ℝ) + 1 ≤ i := by
      exact_mod_cast Nat.succ_le_iff.mpr hji
    linarith

private theorem dyadicZeroBuckets_sdiff_biUnion_eq_actual
    (S : Finset ℂ) (k : ℕ) :
    (dyadicUnitBucketIndexSet k).biUnion
        (fun n => zeroOrdinateUnitBucket n \ S) =
      actualZetaDyadicZeroBlock k \ S := by
  rw [dyadicUnitBucketIndexSet]
  calc
    (Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)).biUnion
        (fun n => zeroOrdinateUnitBucket n \ S) =
        ((Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)).biUnion
          zeroOrdinateUnitBucket) \ S := by
      ext rho
      simp only [Finset.mem_biUnion, Finset.mem_sdiff]
      constructor
      · rintro ⟨n, hn, hrho, hrhoNotS⟩
        exact ⟨⟨n, hn, hrho⟩, hrhoNotS⟩
      · rintro ⟨⟨n, hn, hrho⟩, hrhoNotS⟩
        exact ⟨n, hn, hrho, hrhoNotS⟩
    _ = actualZetaDyadicZeroBlock k \ S := by
      rw [← actualZetaDyadicZeroBlock_eq_biUnion_zeroOrdinateUnitBucket]

private theorem dynamicComplementDyadicCapacity_reindex
    (S : Finset ℂ) {T : ℝ} (k : ℕ)
    (hT : (2 : ℝ) ^ (k + 1) ≤ T) (f : ℂ → ℝ) :
    (∑ n ∈ dyadicUnitBucketIndexSet k,
        ∑ rho ∈ dynamicComplementZeroPacket S T n, f rho) =
      ∑ rho ∈ actualZetaDyadicZeroBlock k \ S, f rho := by
  calc
    (∑ n ∈ dyadicUnitBucketIndexSet k,
        ∑ rho ∈ dynamicComplementZeroPacket S T n, f rho) =
        ∑ n ∈ dyadicUnitBucketIndexSet k,
          ∑ rho ∈ zeroOrdinateUnitBucket n \ S, f rho := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [dynamicComplementZeroPacket_eq_zeroOrdinateUnitBucket_sdiff_of_dyadic S hn hT]
    _ = ∑ rho ∈ (dyadicUnitBucketIndexSet k).biUnion
          (fun n => zeroOrdinateUnitBucket n \ S), f rho := by
      rw [Finset.sum_biUnion (dyadicZeroBuckets_sdiff_pairwiseDisjoint S k)]
    _ = ∑ rho ∈ actualZetaDyadicZeroBlock k \ S, f rho := by
      rw [dyadicZeroBuckets_sdiff_biUnion_eq_actual]

theorem dynamicComplementDyadicSquareReciprocalCapacity_eq_actual
    (S : Finset ℂ) {T : ℝ} (k : ℕ)
    (hT : (2 : ℝ) ^ (k + 1) ≤ T) :
    dynamicComplementDyadicSquareReciprocalCapacity S T k =
      actualZetaDyadicSquareReciprocalCapacityExcluding k S := by
  unfold dynamicComplementDyadicSquareReciprocalCapacity
    actualZetaDyadicSquareReciprocalCapacityExcluding
  exact dynamicComplementDyadicCapacity_reindex S k hT fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2

theorem dynamicComplementDyadicLinearReciprocalCapacity_eq_actual
    (S : Finset ℂ) {T : ℝ} (k : ℕ)
    (hT : (2 : ℝ) ^ (k + 1) ≤ T) :
    dynamicComplementDyadicLinearReciprocalCapacity S T k =
      actualZetaDyadicLinearReciprocalCapacityExcluding k S := by
  unfold dynamicComplementDyadicLinearReciprocalCapacity
    actualZetaDyadicLinearReciprocalCapacityExcluding
  exact dynamicComplementDyadicCapacity_reindex S k hT fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2

end

end PrimeNumberTheorem.VKEdgePiOverTwo
