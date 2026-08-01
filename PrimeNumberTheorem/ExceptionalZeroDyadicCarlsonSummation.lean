import PrimeNumberTheorem.ExceptionalZeroDyadicCapacityReindex

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Whole-Gram summation across a finite dyadic range

The generic dynamic-packet Schur estimate is applied once to the entire
bucket range, so every cross-block Gram entry remains present.  Only the
resulting diagonal packet-mass-square sum is partitioned into dyadic blocks.
-/

/-- Natural unit-bucket indices in the finite dyadic range `[2^K, 2^L)`. -/
def dyadicUnitBucketRange (K L : ℕ) : Finset ℕ :=
  Finset.Icc (2 ^ K) (2 ^ L - 1)

/-- The finite dyadic bucket range is the disjoint union of its constituent
half-open dyadic blocks. -/
theorem dyadicUnitBucketRange_eq_biUnion {K L : ℕ} (hKL : K ≤ L) :
    dyadicUnitBucketRange K L =
      (Finset.Ico K L).biUnion dyadicUnitBucketIndexSet := by
  induction L with
  | zero =>
      have hK : K = 0 := Nat.eq_zero_of_le_zero hKL
      subst K
      simp [dyadicUnitBucketRange, dyadicUnitBucketIndexSet]
  | succ L ih =>
      by_cases hKprev : K ≤ L
      · have hpow : 2 ^ K ≤ 2 ^ L :=
          Nat.pow_le_pow_right (by norm_num) hKprev
        calc
          dyadicUnitBucketRange K (L + 1) =
              dyadicUnitBucketRange K L ∪ dyadicUnitBucketIndexSet L := by
            ext n
            simp only [dyadicUnitBucketRange, dyadicUnitBucketIndexSet,
              Finset.mem_Icc, Finset.mem_union]
            omega
          _ = (Finset.Ico K L).biUnion dyadicUnitBucketIndexSet ∪
                dyadicUnitBucketIndexSet L := by rw [ih hKprev]
          _ = (Finset.Ico K (L + 1)).biUnion dyadicUnitBucketIndexSet := by
            have hIco : Finset.Ico K (L + 1) = insert L (Finset.Ico K L) := by
              ext k
              simp
              omega
            rw [hIco, Finset.biUnion_insert]
            exact Finset.union_comm _ _
      · have hK : K = L + 1 := by omega
        subst K
        simp [dyadicUnitBucketRange, dyadicUnitBucketIndexSet]

private theorem dyadicUnitBucketIndexSet_pairwiseDisjoint (K L : ℕ) :
    (Finset.Ico K L : Set ℕ).PairwiseDisjoint dyadicUnitBucketIndexSet := by
  intro i hi j hj hij
  change Disjoint (dyadicUnitBucketIndexSet i) (dyadicUnitBucketIndexSet j)
  rw [Finset.disjoint_left]
  intro n hni hnj
  rcases Finset.mem_Icc.mp hni with ⟨hniLower, hniUpper⟩
  rcases Finset.mem_Icc.mp hnj with ⟨hnjLower, hnjUpper⟩
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hpow : 2 ^ (i + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpowPos : 0 < 2 ^ (i + 1) := by positivity
    have hnlt : n < 2 ^ (i + 1) := by omega
    exact (Nat.not_lt_of_ge hnjLower) (hnlt.trans_le hpow)
  · have hpow : 2 ^ (j + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpowPos : 0 < 2 ^ (j + 1) := by positivity
    have hnlt : n < 2 ^ (j + 1) := by omega
    exact (Nat.not_lt_of_ge hniLower) (hnlt.trans_le hpow)

/-- Sum of the block-local occupancy-weighted target square capacities over
the finite dyadic range. -/
noncomputable def dynamicComplementDyadicRangeWeightedSquareCapacity
    (S : Finset ℂ) (T beta a : ℝ) (K L : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico K L,
    (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
      dynamicComplementDyadicTargetSquareCapacity S T beta a k

private theorem rangePacketCoefficientMass_sq_le_blockWeightedCapacity
    (S : Finset ℂ) (T beta a : ℝ) (k : ℕ) :
    (∑ n ∈ dyadicUnitBucketIndexSet k,
        dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
      (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
        dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
  have hpackets :
      (∑ n ∈ dyadicUnitBucketIndexSet k,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
        (dynamicComplementDyadicOccupancy S T k : ℝ) *
          dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
    calc
      (∑ n ∈ dyadicUnitBucketIndexSet k,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
          ∑ n ∈ dyadicUnitBucketIndexSet k,
            (dynamicComplementDyadicOccupancy S T k : ℝ) *
              ∑ rho ∈ dynamicComplementZeroPacket S T n,
                ‖finiteZeroClusterCoefficientAt
                    (analyticOrderNatAt riemannZeta) beta a rho‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        unfold dynamicComplementPacketCoefficientMass
        calc
          (∑ rho ∈ dynamicComplementZeroPacket S T n,
              ‖finiteZeroClusterCoefficientAt
                  (analyticOrderNatAt riemannZeta) beta a rho‖) ^ 2 ≤
              ((dynamicComplementZeroPacket S T n).card : ℝ) *
                ∑ rho ∈ dynamicComplementZeroPacket S T n,
                  ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a rho‖ ^ 2 :=
            sq_sum_le_card_mul_sum_sq
          _ ≤ (dynamicComplementDyadicOccupancy S T k : ℝ) *
                ∑ rho ∈ dynamicComplementZeroPacket S T n,
                  ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a rho‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast
                dynamicComplementZeroPacket_card_le_dyadicOccupancy
                  S T k hn
            · positivity
      _ = (dynamicComplementDyadicOccupancy S T k : ℝ) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
        rw [← Finset.mul_sum]
        unfold dynamicComplementDyadicTargetSquareCapacity
        apply congrArg
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro rho hrho
        exact finiteZeroClusterCoefficientAt_norm_sq_eq beta a rho
  have hcapacityNonneg :
      0 ≤ dynamicComplementDyadicTargetSquareCapacity S T beta a k :=
    dynamicComplementDyadicTargetSquareCapacity_nonneg S T beta a k
  exact hpackets.trans (by
    apply mul_le_mul_of_nonneg_right
    · linarith
    · exact hcapacityNonneg)

/-- One whole-Gram Schur estimate over a finite dyadic range.  The left side
contains all cross-block Gram entries; only its diagonal square-mass upper
bound is reindexed blockwise. -/
theorem dynamicComplementDyadicRangeCenteredFrozenGaussianSecondMoment_le
    (S : Finset ℂ) (T beta a : ℝ) {K L : ℕ} {m : ℝ}
    (hKL : K ≤ L) (hm : 1 ≤ m) :
    dynamicComplementCenteredFrozenGaussianSecondMoment S T beta a
        (dyadicUnitBucketRange K L) m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ∑ k ∈ Finset.Ico K L,
          (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
  have hpacketSquares :
      (∑ n ∈ dyadicUnitBucketRange K L,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
        ∑ k ∈ Finset.Ico K L,
          (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
    rw [dyadicUnitBucketRange_eq_biUnion hKL]
    calc
      (∑ n ∈ (Finset.Ico K L).biUnion dyadicUnitBucketIndexSet,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) =
          ∑ k ∈ Finset.Ico K L,
            ∑ n ∈ dyadicUnitBucketIndexSet k,
              dynamicComplementPacketCoefficientMass S T beta a n ^ 2 := by
        exact Finset.sum_biUnion
          (f := fun n =>
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2)
          (dyadicUnitBucketIndexSet_pairwiseDisjoint K L)
      _ ≤ ∑ k ∈ Finset.Ico K L,
          (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
        exact Finset.sum_le_sum fun k _ =>
          rangePacketCoefficientMass_sq_le_blockWeightedCapacity S T beta a k
  exact (dynamicComplementCenteredFrozenGaussianSecondMoment_le_majorant
    S T beta a (dyadicUnitBucketRange K L)
      (lt_of_lt_of_le zero_lt_one hm)).trans
    ((dynamicComplementGaussianMajorantEnergy_le S T beta a
      (dyadicUnitBucketRange K L) hm).trans
        (mul_le_mul_of_nonneg_left hpacketSquares
          MathlibAux.gaussianBucketSchurConstant_pos.le))

/-- Across a right-higher finite dyadic range, either an actual surviving
zero lies strictly to the right of `beta`, with its directed Carlson-strip
witness data, or the whole centered frozen energy is controlled by the
unweighted block capacities. -/
theorem rightHigherDyadicRange_fartherRight_or_centeredFrozen_le_unweighted
    (S : Finset ℂ) {Told sigma T beta a : ℝ} {K L : ℕ}
    (hTold : 0 ≤ Told) (ha : 0 ≤ a) (hKL : K ≤ L)
    {m : ℝ} (hm : 1 ≤ m) :
    (∃ n ∈ dyadicUnitBucketRange K L, ∃ rho,
      rho ∈ dynamicComplementZeroPacket
          (rightHigherExclusionSet S Told sigma T) T n ∧
        beta < rho.re ∧
        rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
        Told < rho.im ∧ rho ∉ S) ∨
      dynamicComplementCenteredFrozenGaussianSecondMoment
          (rightHigherExclusionSet S Told sigma T) T beta a
          (dyadicUnitBucketRange K L) m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ k ∈ Finset.Ico K L,
            (1 + (dynamicComplementDyadicOccupancy
              (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
              dynamicComplementDyadicSquareReciprocalCapacity
                (rightHigherExclusionSet S Told sigma T) T k := by
  classical
  by_cases hfar : ∃ n ∈ dyadicUnitBucketRange K L, ∃ rho,
      rho ∈ dynamicComplementZeroPacket
          (rightHigherExclusionSet S Told sigma T) T n ∧ beta < rho.re
  · left
    rcases hfar with ⟨n, hn, rho, hrhoPacket, hrhoFar⟩
    have hrhoInter := Finset.mem_inter.mp hrhoPacket
    have hrhoDiff := Finset.mem_sdiff.mp hrhoInter.2
    rcases directedWitness_of_not_mem_rightHigherExclusionSet
        hTold hrhoDiff.1 hrhoDiff.2 with ⟨hrhoStrip, hrhoHigh, hrhoS⟩
    exact ⟨n, hn, rho, hrhoPacket, hrhoFar,
      hrhoStrip, hrhoHigh, hrhoS⟩
  · right
    push Not at hfar
    have hre : ∀ k ∈ Finset.Ico K L, ∀ n ∈ dyadicUnitBucketIndexSet k,
        ∀ rho, rho ∈ dynamicComplementZeroPacket
            (rightHigherExclusionSet S Told sigma T) T n →
          rho.re ≤ beta := by
      intro k hk n hn rho hrho
      apply hfar n
      · rw [dyadicUnitBucketRange_eq_biUnion hKL]
        exact Finset.mem_biUnion.mpr ⟨k, hk, hn⟩
      · exact hrho
    refine (dynamicComplementDyadicRangeCenteredFrozenGaussianSecondMoment_le
      (rightHigherExclusionSet S Told sigma T) T beta a hKL hm).trans ?_
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left
      · exact rightHigherDyadicTargetSquareCapacity_le_unweighted_of_re_le
          S Told sigma T beta k ha (hre k hk)
      · positivity
    · exact MathlibAux.gaussianBucketSchurConstant_pos.le

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
