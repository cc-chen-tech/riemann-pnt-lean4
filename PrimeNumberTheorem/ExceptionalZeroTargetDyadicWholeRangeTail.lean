import PrimeNumberTheorem.ExceptionalZeroTargetDyadicTailBudget

open Complex Filter Set
open scoped BigOperators Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Whole-range target dyadic Gram tails

The Schur estimate in this module is applied once to the full bucket range
`[2^K, 2^L)`.  Cross-block Gram entries therefore remain on the left-hand
side.  Only the resulting diagonal packet-mass-square sum is partitioned
into dyadic blocks and bounded by the local occupancy and square-capacity
estimates.
-/

/-- Natural unit-bucket indices in the finite dyadic range `[2^K, 2^L)`. -/
def targetDyadicUnitBucketRange (K L : ℕ) : Finset ℕ :=
  Finset.Icc (2 ^ K) (2 ^ L - 1)

/-- The finite target bucket range is the disjoint union of its constituent
half-open dyadic blocks. -/
theorem targetDyadicUnitBucketRange_eq_biUnion {K L : ℕ} (hKL : K ≤ L) :
    targetDyadicUnitBucketRange K L =
      (Finset.Ico K L).biUnion dyadicUnitBucketIndexSet := by
  induction L with
  | zero =>
      have hK : K = 0 := Nat.eq_zero_of_le_zero hKL
      subst K
      simp [targetDyadicUnitBucketRange]
  | succ L ih =>
      by_cases hKprev : K ≤ L
      · have hpow : 2 ^ K ≤ 2 ^ L :=
          Nat.pow_le_pow_right (by norm_num) hKprev
        calc
          targetDyadicUnitBucketRange K (L + 1) =
              targetDyadicUnitBucketRange K L ∪ dyadicUnitBucketIndexSet L := by
            ext n
            simp only [targetDyadicUnitBucketRange, dyadicUnitBucketIndexSet,
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
        simp [targetDyadicUnitBucketRange]

private theorem targetDyadicUnitBucketIndexSet_pairwiseDisjoint (K L : ℕ) :
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

private theorem targetRangePacketCoefficientMass_sq_le_blockWeightedCapacity
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
                dynamicComplementZeroPacket_card_le_dyadicOccupancy S T k hn
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

/-- One whole-range Schur estimate.  The left side retains every cross-block
Gram entry; only the diagonal packet square masses are reindexed blockwise. -/
theorem dynamicComplementTargetDyadicRangeCenteredFrozenGaussianSecondMoment_le
    (S : Finset ℂ) (T beta a : ℝ) {K L : ℕ} {m : ℝ}
    (hKL : K ≤ L) (hm : 1 ≤ m) :
    dynamicComplementCenteredFrozenGaussianSecondMoment S T beta a
        (targetDyadicUnitBucketRange K L) m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ∑ k ∈ Finset.Ico K L,
          (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
  have hpacketSquares :
      (∑ n ∈ targetDyadicUnitBucketRange K L,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
        ∑ k ∈ Finset.Ico K L,
          (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
    rw [targetDyadicUnitBucketRange_eq_biUnion hKL]
    calc
      (∑ n ∈ (Finset.Ico K L).biUnion dyadicUnitBucketIndexSet,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) =
          ∑ k ∈ Finset.Ico K L,
            ∑ n ∈ dyadicUnitBucketIndexSet k,
              dynamicComplementPacketCoefficientMass S T beta a n ^ 2 := by
        exact Finset.sum_biUnion
          (f := fun n =>
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2)
          (targetDyadicUnitBucketIndexSet_pairwiseDisjoint K L)
      _ ≤ ∑ k ∈ Finset.Ico K L,
          (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
        exact Finset.sum_le_sum fun k _ =>
          targetRangePacketCoefficientMass_sq_le_blockWeightedCapacity
            S T beta a k
  exact (dynamicComplementCenteredFrozenGaussianSecondMoment_le_majorant
    S T beta a (targetDyadicUnitBucketRange K L)
      (lt_of_lt_of_le zero_lt_one hm)).trans
    ((dynamicComplementGaussianMajorantEnergy_le S T beta a
      (targetDyadicUnitBucketRange K L) hm).trans
        (mul_le_mul_of_nonneg_left hpacketSquares
          MathlibAux.gaussianBucketSchurConstant_pos.le))

/-- The occupancy-weighted reciprocal-square target capacity has a uniform
summable `log^3 H / H` dyadic majorant. -/
theorem exists_dynamicComplementDyadicWeightedSquareCapacity_le_logCubeDiv :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (S : Finset ℂ) (T : ℝ) (k : ℕ), 4 ≤ 2 ^ k →
        (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicSquareReciprocalCapacity S T k ≤
          D * dyadicLogCubeDiv k := by
  rcases exists_dynamicComplementDyadicOccupancy_le_log with
    ⟨Cocc, hCocc, hocc⟩
  rcases exists_dynamicComplementDyadicSquareReciprocalCapacity_le_log_sq_div with
    ⟨Ccap, hCcap, hcap⟩
  let D : ℝ := (1 + Cocc) * Ccap ^ 2
  refine ⟨D, mul_nonneg (by linarith) (sq_nonneg Ccap), ?_⟩
  intro S T k hk
  let L : ℝ := 1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)
  have hL : 1 ≤ L := by
    dsimp [L]
    have hpow : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
    have harg : 1 ≤ (2 : ℝ) ^ (k + 1) + 7 := by linarith
    linarith [Real.log_nonneg harg]
  have hoccBound := hocc S T k hk
  have hcapBound := hcap S T k hk
  have hcapacityNonneg :
      0 ≤ dynamicComplementDyadicSquareReciprocalCapacity S T k := by
    unfold dynamicComplementDyadicSquareReciprocalCapacity
    positivity
  have hfactor :
      1 + (dynamicComplementDyadicOccupancy S T k : ℝ) ≤
        (1 + Cocc) * L := by
    dsimp [L] at hoccBound hL ⊢
    nlinarith
  calc
    (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
        dynamicComplementDyadicSquareReciprocalCapacity S T k ≤
        ((1 + Cocc) * L) * (Ccap ^ 2 * L ^ 2 / (2 : ℝ) ^ k) := by
      exact mul_le_mul hfactor (by simpa [L] using hcapBound)
        hcapacityNonneg (mul_nonneg (by linarith) (zero_le_one.trans hL))
    _ = D * dyadicLogCubeDiv k := by
      dsimp [D, L, dyadicLogCubeDiv]
      ring

private theorem rightHigherTargetDyadicRange_fartherRight_or_centeredFrozen_le_unweighted
    (S : Finset ℂ) {Told sigma T beta a : ℝ} {K L : ℕ}
    (hTold : 0 ≤ Told) (ha : 0 ≤ a) (hKL : K ≤ L)
    {m : ℝ} (hm : 1 ≤ m) :
    (∃ n ∈ targetDyadicUnitBucketRange K L, ∃ rho,
      rho ∈ dynamicComplementZeroPacket
          (rightHigherExclusionSet S Told sigma T) T n ∧
        beta < rho.re ∧
        rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
        Told < rho.im ∧ rho ∉ S) ∨
      dynamicComplementCenteredFrozenGaussianSecondMoment
          (rightHigherExclusionSet S Told sigma T) T beta a
          (targetDyadicUnitBucketRange K L) m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ k ∈ Finset.Ico K L,
            (1 + (dynamicComplementDyadicOccupancy
              (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
              dynamicComplementDyadicSquareReciprocalCapacity
                (rightHigherExclusionSet S Told sigma T) T k := by
  classical
  by_cases hfar : ∃ n ∈ targetDyadicUnitBucketRange K L, ∃ rho,
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
      · rw [targetDyadicUnitBucketRange_eq_biUnion hKL]
        exact Finset.mem_biUnion.mpr ⟨k, hk, hn⟩
      · exact hrho
    refine
      (dynamicComplementTargetDyadicRangeCenteredFrozenGaussianSecondMoment_le
        (rightHigherExclusionSet S Told sigma T) T beta a hKL hm).trans ?_
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left
      · exact rightHigherDyadicTargetSquareCapacity_le_unweighted_of_re_le
          S Told sigma T beta k ha (hre k hk)
      · positivity
    · exact MathlibAux.gaussianBucketSchurConstant_pos.le

/-- Uniformly above one cutoff, every finite right-higher dyadic range either
contains a genuinely farther-right surviving zero or its one whole-range
centered frozen energy is smaller than `eta`.  This remains an upper-budget
statement: it does not provide a Sharp lower bound or repeatable residual
energy after enlarging the exclusion set. -/
theorem eventually_rightHigherTargetDyadicRange_fartherRight_or_energy_lt
    {eta : ℝ} (heta : 0 < eta) :
    ∃ Keta : ℕ, 2 ≤ Keta ∧
      ∀ (S : Finset ℂ) {Told sigma T beta a : ℝ} {K L : ℕ} {m : ℝ},
        0 ≤ Told → 0 ≤ a → 1 ≤ m → Keta ≤ K → K < L →
        (∃ n ∈ targetDyadicUnitBucketRange K L, ∃ rho,
          rho ∈ dynamicComplementZeroPacket
              (rightHigherExclusionSet S Told sigma T) T n ∧
            beta < rho.re ∧
            rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
            Told < rho.im ∧ rho ∉ S) ∨
          dynamicComplementCenteredFrozenGaussianSecondMoment
              (rightHigherExclusionSet S Told sigma T) T beta a
              (targetDyadicUnitBucketRange K L) m < eta := by
  classical
  rcases exists_dynamicComplementDyadicWeightedSquareCapacity_le_logCubeDiv with
    ⟨D, hD, hblock⟩
  let C : ℝ := MathlibAux.gaussianBucketSchurConstant
  let E : ℝ := C * (D + 1)
  have hC : 0 < C := MathlibAux.gaussianBucketSchurConstant_pos
  have hE : 0 < E := by
    dsimp [E]
    exact mul_pos hC (by linarith)
  have htail := eventually_sum_Icc_dyadicLogCubeDiv_lt (div_pos heta hE)
  have hready : ∀ᶠ K : ℕ in atTop,
      2 ≤ K ∧ ∀ N : ℕ, K ≤ N →
        (∑ k ∈ Finset.Icc K N, dyadicLogCubeDiv k) < eta / E := by
    filter_upwards [eventually_ge_atTop 2, htail] with K hK htailK
    exact ⟨hK, htailK⟩
  rcases eventually_atTop.1 hready with ⟨Keta, hKeta⟩
  refine ⟨Keta, (hKeta Keta le_rfl).1, ?_⟩
  intro S Told sigma T beta a K L m hTold ha hm hKetaK hKL
  have hreadyK := hKeta K hKetaK
  have hKtwo : 2 ≤ K := hreadyK.1
  have hKLeL : K ≤ L := Nat.le_of_lt hKL
  rcases
      rightHigherTargetDyadicRange_fartherRight_or_centeredFrozen_le_unweighted
        S hTold ha hKLeL hm with hfar | henergy
  · exact Or.inl hfar
  · right
    have hblockSum :
        (∑ k ∈ Finset.Ico K L,
          (1 + (dynamicComplementDyadicOccupancy
            (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
              dynamicComplementDyadicSquareReciprocalCapacity
                (rightHigherExclusionSet S Told sigma T) T k) ≤
          D * ∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hkTwo : 2 ≤ k := hKtwo.trans (Finset.mem_Ico.mp hk).1
      have hkFour : 4 ≤ 2 ^ k := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right' (by norm_num) hkTwo
      exact hblock (rightHigherExclusionSet S Told sigma T) T k hkFour
    have hIcoSubset : Finset.Ico K L ⊆ Finset.Icc K L := by
      intro k hk
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩
    have hmajorantNonneg :
        0 ≤ ∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k :=
      Finset.sum_nonneg fun k _ => dyadicLogCubeDiv_nonneg k
    have hmajorantLe :
        (∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k) ≤
          ∑ k ∈ Finset.Icc K L, dyadicLogCubeDiv k :=
      Finset.sum_le_sum_of_subset_of_nonneg hIcoSubset
        (fun k _ _ => dyadicLogCubeDiv_nonneg k)
    have htailSmall :
        (∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k) < eta / E :=
      hmajorantLe.trans_lt (hreadyK.2 L hKLeL)
    have hscaledSmall :
        C * (D * ∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k) < eta := by
      have hCDle : C * D ≤ E := by
        dsimp [E]
        nlinarith [hC.le]
      have hEsmall :
          E * (∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k) < eta := by
        simpa [mul_comm] using (lt_div_iff₀ hE).mp htailSmall
      calc
        C * (D * ∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k) =
            (C * D) * ∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k := by ring
        _ ≤ E * ∑ k ∈ Finset.Ico K L, dyadicLogCubeDiv k :=
          mul_le_mul_of_nonneg_right hCDle hmajorantNonneg
        _ < eta := hEsmall
    exact henergy.trans_lt
      ((mul_le_mul_of_nonneg_left hblockSum hC.le).trans_lt hscaledSmall)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
