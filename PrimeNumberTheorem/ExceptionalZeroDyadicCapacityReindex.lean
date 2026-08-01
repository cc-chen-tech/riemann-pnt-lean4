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

/-- The largest complementary packet occupancy in a dyadic block is bounded
by the same uniform logarithmic constant as a full unit bucket. -/
theorem exists_dynamicComplementDyadicOccupancy_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℂ) (T : ℝ) (k : ℕ),
      2 ≤ k →
      (dynamicComplementDyadicOccupancy S T k : ℝ) ≤
        C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) := by
  classical
  rcases exists_zeroOrdinateUnitBucketMultiplicity_le_log with
    ⟨C, hC, hbucket⟩
  refine ⟨C, hC, ?_⟩
  intro S T k hk
  have hindexNonempty : (dyadicUnitBucketIndexSet k).Nonempty := by
    refine ⟨2 ^ k, Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
    rw [pow_succ]
    have hpowPos : 0 < 2 ^ k := by positivity
    omega
  rcases (dyadicUnitBucketIndexSet k).exists_mem_eq_sup hindexNonempty
      (fun n => (dynamicComplementZeroPacket S T n).card) with
    ⟨n, hn, hsup⟩
  rw [dynamicComplementDyadicOccupancy, hsup]
  rcases Finset.mem_Icc.mp hn with ⟨hnLower, hnUpper⟩
  have hfourPow : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ k :=
        pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk
  have hnLowerReal : (2 : ℝ) ^ k ≤ (n : ℝ) := by
    exact_mod_cast hnLower
  have hnFour : 4 ≤ n := by
    exact_mod_cast hfourPow.trans hnLowerReal
  have hnUpperPow : n ≤ 2 ^ (k + 1) := by omega
  have hnUpperReal : (n : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast hnUpperPow
  have hpacketSubset :
      dynamicComplementZeroPacket S T n ⊆ zeroOrdinateUnitBucket n := by
    intro rho hrho
    exact (Finset.mem_inter.mp hrho).1
  have hmultOne : ∀ rho ∈ dynamicComplementZeroPacket S T n,
      1 ≤ analyticOrderNatAt riemannZeta rho := by
    intro rho hrho
    have hrhoBucket := hpacketSubset hrho
    have hrhoFinite := (Finset.mem_filter.mp hrhoBucket).1
    have hzero := (mem_nontrivialZerosFinset.mp hrhoFinite).1
    have hrhoOne : rho ≠ 1 := by
      intro hrhoEq
      have hre := congrArg Complex.re hrhoEq
      simp at hre
      linarith [hzero.2.2]
    exact
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrhoOne hzero.1
  have hcardNat :
      (dynamicComplementZeroPacket S T n).card ≤
        ∑ rho ∈ dynamicComplementZeroPacket S T n,
          analyticOrderNatAt riemannZeta rho := by
    simpa using
      (dynamicComplementZeroPacket S T n).card_nsmul_le_sum
        (fun rho => analyticOrderNatAt riemannZeta rho) 1 hmultOne
  have hcardReal :
      ((dynamicComplementZeroPacket S T n).card : ℝ) ≤
        ∑ rho ∈ dynamicComplementZeroPacket S T n,
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
    exact_mod_cast hcardNat
  have hlog :
      Real.log ((n : ℝ) + 7) ≤
        Real.log ((2 : ℝ) ^ (k + 1) + 7) := by
    exact Real.log_le_log (by positivity) (by linarith)
  calc
    ((dynamicComplementZeroPacket S T n).card : ℝ) ≤
        ∑ rho ∈ dynamicComplementZeroPacket S T n,
          (analyticOrderNatAt riemannZeta rho : ℝ) := hcardReal
    _ ≤ zeroOrdinateUnitBucketMultiplicity n := by
      unfold zeroOrdinateUnitBucketMultiplicity
      exact Finset.sum_le_sum_of_subset_of_nonneg hpacketSubset
        (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ C * (1 + Real.log ((n : ℝ) + 7)) := hbucket n hnFour
    _ ≤ C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC

/-- Every actual dyadic zero below ordinate four is absorbed by the low-height
side of the right-higher exclusion set once the old cutoff is at least four. -/
theorem low_actualZetaDyadicZero_mem_rightHigherExclusionSet
    (S : Finset ℂ) {Told sigma T : ℝ} {k : ℕ} {rho : ℂ}
    (hrho : rho ∈ actualZetaDyadicZeroBlock k)
    (hlow : |rho.im| < 4) (hTold : 4 ≤ Told)
    (hheight : (2 : ℝ) ^ (k + 1) ≤ T) :
    rho ∈ rightHigherExclusionSet S Told sigma T := by
  rcases Finset.mem_filter.mp hrho with ⟨hrhoBlock, hbounds⟩
  have hrhoT : rho ∈ nontrivialZerosFinset T := by
    apply mem_nontrivialZerosFinset.mpr
    rcases mem_nontrivialZerosFinset.mp hrhoBlock with ⟨hzero, _⟩
    exact ⟨hzero, hbounds.2.le.trans hheight⟩
  apply Finset.mem_union_right
  apply Finset.mem_filter.mpr
  exact ⟨hrhoT, Or.inl ((le_abs_self rho.im).trans (hlow.le.trans hTold))⟩

/-- The existing uniform pointwise multiplicity constant controls the
right-higher deleted square capacity by its linear capacity. -/
theorem exists_rightHigherDyadicSquareCapacity_le_log_linear :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (S : Finset ℂ) (Told sigma T : ℝ) (k : ℕ),
        4 ≤ Told → (2 : ℝ) ^ (k + 1) ≤ T →
        actualZetaDyadicSquareReciprocalCapacityExcluding k
            (rightHigherExclusionSet S Told sigma T) ≤
          (B * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 6))) *
            actualZetaDyadicLinearReciprocalCapacityExcluding k
              (rightHigherExclusionSet S Told sigma T) := by
  rcases exists_actualZetaDyadicSquareReciprocalCapacityExcluding_le_log_linear with
    ⟨B, hB, hcapacity⟩
  refine ⟨B, hB, ?_⟩
  intro S Told sigma T k hTold hheight
  exact hcapacity k (rightHigherExclusionSet S Told sigma T)
    (fun rho hrho hlow =>
      low_actualZetaDyadicZero_mem_rightHigherExclusionSet
        S hrho hlow hTold hheight)

/-- Surviving right-higher linear capacity in one actual dyadic block is
bounded by the actual Carlson zero-density multiplicity count at the block's
upper height. -/
theorem rightHigherActualZetaDyadicLinearCapacity_le_zeroDensityCount
    (S : Finset ℂ) {Told sigma T : ℝ} (k : ℕ)
    (hTold : 0 ≤ Told) (hheight : (2 : ℝ) ^ (k + 1) ≤ T) :
    actualZetaDyadicLinearReciprocalCapacityExcluding k
        (rightHigherExclusionSet S Told sigma T) ≤
      (((2 : ℝ) ^ k) ^ 2)⁻¹ *
        (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ (k + 1)) : ℝ) := by
  classical
  let R := actualZetaDyadicZeroBlock k \
    rightHigherExclusionSet S Told sigma T
  have hsubset : R ⊆
      ZeroDensity.zeroDensityZerosFinset sigma ((2 : ℝ) ^ (k + 1)) := by
    intro rho hrho
    rcases Finset.mem_sdiff.mp hrho with ⟨hrhoBlock, hrhoNotExcluded⟩
    rcases Finset.mem_filter.mp hrhoBlock with ⟨hrhoUpper, hbounds⟩
    have hrhoT : rho ∈ nontrivialZerosFinset T := by
      apply mem_nontrivialZerosFinset.mpr
      rcases mem_nontrivialZerosFinset.mp hrhoUpper with ⟨hzero, _⟩
      exact ⟨hzero, hbounds.2.le.trans hheight⟩
    rcases directedWitness_of_not_mem_rightHigherExclusionSet
        hTold hrhoT hrhoNotExcluded with ⟨hrhoDensity, _, _⟩
    rcases ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoDensity with
      ⟨hzero, himPos, _, hre⟩
    exact ZeroDensity.mem_zeroDensityZerosFinset.mpr
      ⟨hzero, himPos, (le_abs_self rho.im).trans hbounds.2.le, hre⟩
  have hweight : ∀ rho ∈ R,
      (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2 ≤
        (((2 : ℝ) ^ k) ^ 2)⁻¹ *
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
    intro rho hrho
    have hrhoBlock := (Finset.mem_sdiff.mp hrho).1
    have hbounds := (Finset.mem_filter.mp hrhoBlock).2
    have hnorm : (2 : ℝ) ^ k ≤ ‖rho‖ :=
      hbounds.1.trans (Complex.abs_im_le_norm rho)
    have hsquare : ((2 : ℝ) ^ k) ^ 2 ≤ ‖rho‖ ^ 2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg rho)).2 hnorm
    have hbaseSquarePos : 0 < ((2 : ℝ) ^ k) ^ 2 := by positivity
    have hnormSquarePos : 0 < ‖rho‖ ^ 2 :=
      hbaseSquarePos.trans_le hsquare
    have hinv : (‖rho‖ ^ 2)⁻¹ ≤ (((2 : ℝ) ^ k) ^ 2)⁻¹ :=
      (inv_le_inv₀ hnormSquarePos hbaseSquarePos).2 hsquare
    rw [div_eq_mul_inv,
      mul_comm (((2 : ℝ) ^ k) ^ 2)⁻¹
        (analyticOrderNatAt riemannZeta rho : ℝ)]
    exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
  unfold actualZetaDyadicLinearReciprocalCapacityExcluding
  change (∑ rho ∈ R,
      (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2) ≤ _
  calc
    (∑ rho ∈ R,
        (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2) ≤
        ∑ rho ∈ R, (((2 : ℝ) ^ k) ^ 2)⁻¹ *
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
      exact Finset.sum_le_sum fun rho hrho => hweight rho hrho
    _ = (((2 : ℝ) ^ k) ^ 2)⁻¹ *
        ∑ rho ∈ R, (analyticOrderNatAt riemannZeta rho : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (((2 : ℝ) ^ k) ^ 2)⁻¹ *
        ∑ rho ∈ ZeroDensity.zeroDensityZerosFinset sigma ((2 : ℝ) ^ (k + 1)),
          (analyticOrderNatAt riemannZeta rho : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ => Nat.cast_nonneg _)
      · positivity
    _ = (((2 : ℝ) ^ k) ^ 2)⁻¹ *
        (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ (k + 1)) : ℝ) := by
      simp [ZeroDensity.zeroDensityCount]

end

end PrimeNumberTheorem.VKEdgePiOverTwo
