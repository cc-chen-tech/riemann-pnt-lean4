import PrimeNumberTheorem.ExceptionalZeroDyadicCapacityReindex

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-! ## Carlson polynomial--geometric block majorant -/

noncomputable def carlsonDyadicExponent (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

noncomputable def carlsonDyadicEnergyRatio (sigma : ℝ) : ℝ :=
  (2 : ℝ) ^ (carlsonDyadicExponent sigma - 2)

noncomputable def carlsonDyadicEnergyMajorant (sigma : ℝ) (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) ^ 6 * carlsonDyadicEnergyRatio sigma ^ k

theorem carlsonDyadicExponent_lt_one {sigma : ℝ}
    (hσ : 1 / 2 < sigma) (_hσ1 : sigma < 1) :
    carlsonDyadicExponent sigma < 1 := by
  unfold carlsonDyadicExponent
  nlinarith [sq_pos_of_pos (by linarith : 0 < sigma - 1 / 2)]

private theorem carlsonDyadicEnergyRatio_pos_lt_one {sigma : ℝ}
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1) :
    0 < carlsonDyadicEnergyRatio sigma ∧
      carlsonDyadicEnergyRatio sigma < 1 := by
  have hexponent : carlsonDyadicExponent sigma - 2 < 0 := by
    linarith [carlsonDyadicExponent_lt_one hσ hσ1]
  exact ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexponent⟩

theorem summable_carlsonDyadicEnergyMajorant {sigma : ℝ}
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1) :
    Summable (carlsonDyadicEnergyMajorant sigma) := by
  let r := carlsonDyadicEnergyRatio sigma
  have hr := carlsonDyadicEnergyRatio_pos_lt_one hσ hσ1
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr.1]
    exact hr.2
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 6 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 6 hrnorm
  have hshift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 6 * r ^ (n + 1)) := by
    exact (summable_nat_add_iff 1).2 hbase
  have hscaled := hshift.mul_left r⁻¹
  refine hscaled.congr fun n => ?_
  dsimp [carlsonDyadicEnergyMajorant, r]
  rw [pow_succ]
  field_simp [ne_of_gt hr.1]
  rw [pow_succ']

private theorem one_add_log_two_pow_add_le_three_mul
    (c : ℝ) {k : ℕ} (hk : 2 ≤ k) (hc0 : 0 ≤ c) (hc8 : c ≤ 8) :
    1 + Real.log ((2 : ℝ) ^ (k + 1) + c) ≤
      3 * ((k + 1 : ℕ) : ℝ) := by
  have hpowPos : 0 < (2 : ℝ) ^ (k + 1) := by positivity
  have hpowEight : (8 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    calc
      (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ (k + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  have hsumPos : 0 < (2 : ℝ) ^ (k + 1) + c := by linarith
  have hsumLe :
      (2 : ℝ) ^ (k + 1) + c ≤
        2 * (2 : ℝ) ^ (k + 1) := by
    linarith
  have hlogLe := Real.log_le_log hsumPos hsumLe
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogLe
  have hlogTwoLe : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hkCast : 0 ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hkCastOne : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hmul := mul_le_mul_of_nonneg_left hlogTwoLe hkCast
  linarith

private theorem dyadic_carlson_power_identity (sigma : ℝ) (k : ℕ) :
    ((((2 : ℝ) ^ k) ^ 2)⁻¹ *
        ((2 : ℝ) ^ (k + 1)) ^ carlsonDyadicExponent sigma) =
      (2 : ℝ) ^ carlsonDyadicExponent sigma *
        carlsonDyadicEnergyRatio sigma ^ k := by
  have hinv : ((((2 : ℝ) ^ k) ^ 2)⁻¹) =
      (2 : ℝ) ^ (-((k * 2 : ℕ) : ℝ)) := by
    calc
      ((((2 : ℝ) ^ k) ^ 2)⁻¹) = ((2 : ℝ) ^ (k * 2))⁻¹ := by
        rw [pow_mul]
      _ = ((2 : ℝ) ^ ((k * 2 : ℕ) : ℝ))⁻¹ := by
        rw [Real.rpow_natCast]
      _ = (2 : ℝ) ^ (-((k * 2 : ℕ) : ℝ)) := by
        rw [Real.rpow_neg (by norm_num)]
  have hheight :
      ((2 : ℝ) ^ (k + 1)) ^ carlsonDyadicExponent sigma =
        (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) *
          carlsonDyadicExponent sigma) := by
    exact (Real.rpow_natCast_mul (by norm_num) (k + 1)
      (carlsonDyadicExponent sigma)).symm
  rw [hinv, hheight, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hexponent :
      -((k * 2 : ℕ) : ℝ) +
          ((k + 1 : ℕ) : ℝ) * carlsonDyadicExponent sigma =
        carlsonDyadicExponent sigma +
          (carlsonDyadicExponent sigma - 2) * (k : ℝ) := by
    push_cast
    ring
  rw [hexponent, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  unfold carlsonDyadicEnergyRatio
  rw [Real.rpow_mul_natCast (by norm_num)]

/-- After fixing the Carlson strip, one constant and one dyadic cutoff control
every right-higher complementary block, uniformly in the exclusion set and
both height parameters. -/
theorem exists_rightHigherDyadicCapacity_le_carlsonMajorant
    {sigma : ℝ} (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ K0 : ℕ, 2 ≤ K0 ∧
      ∀ (S : Finset ℂ) (Told T : ℝ) (k : ℕ),
        4 ≤ Told → K0 ≤ k → (2 : ℝ) ^ (k + 1) ≤ T →
        (1 + (dynamicComplementDyadicOccupancy
          (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
            dynamicComplementDyadicSquareReciprocalCapacity
              (rightHigherExclusionSet S Told sigma T) T k ≤
          A * carlsonDyadicEnergyMajorant sigma k := by
  rcases exists_dynamicComplementDyadicOccupancy_le_log with
    ⟨C, hC, hoccupancy⟩
  rcases exists_rightHigherDyadicSquareCapacity_le_log_linear with
    ⟨B, hB, hsquare⟩
  rcases (CarlsonZeroDensity.carlson_zeroDensity_isBigO hσ hσ1).exists_nonneg with
    ⟨D, hD, hCarlson⟩
  have hdyadicTendsto :
      Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ (k + 1))
        Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hCarlsonDyadic := (hCarlson.comp_tendsto hdyadicTendsto).bound
  rcases Filter.eventually_atTop.1 hCarlsonDyadic with ⟨Kc, hKc⟩
  let A := 3 * B * (1 + 3 * C) * D *
    (2 : ℝ) ^ carlsonDyadicExponent sigma
  let K0 := max 2 Kc
  refine ⟨A, ?_, K0, le_max_left _ _, ?_⟩
  · dsimp [A]
    positivity
  · intro S Told T k hTold hk hheight
    have hk2 : 2 ≤ k := (le_max_left 2 Kc).trans (show K0 ≤ k from hk)
    have hkCarlson : Kc ≤ k :=
      (le_max_right 2 Kc).trans (show K0 ≤ k from hk)
    let E := rightHigherExclusionSet S Told sigma T
    let N : ℝ := ((k + 1 : ℕ) : ℝ)
    have hNone : 1 ≤ N := by
      dsimp [N]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hNnonneg : 0 ≤ N := zero_le_one.trans hNone
    have hlogSeven :
        1 + Real.log ((2 : ℝ) ^ (k + 1) + 7) ≤ 3 * N := by
      simpa [N] using
        (one_add_log_two_pow_add_le_three_mul 7 hk2 (by norm_num) (by norm_num))
    have hlogSix :
        1 + Real.log ((2 : ℝ) ^ (k + 1) + 6) ≤ 3 * N := by
      simpa [N] using
        (one_add_log_two_pow_add_le_three_mul 6 hk2 (by norm_num) (by norm_num))
    have hoccupancyRaw := hoccupancy E T k hk2
    have hoccupancyWeighted :
        1 + (dynamicComplementDyadicOccupancy E T k : ℝ) ≤
          (1 + 3 * C) * N := by
      calc
        1 + (dynamicComplementDyadicOccupancy E T k : ℝ) ≤
            1 + C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) := by
          linarith
        _ ≤ 1 + C * (3 * N) := by
          gcongr
        _ ≤ (1 + 3 * C) * N := by
          nlinarith
    have hactualSquareNonneg :
        0 ≤ actualZetaDyadicSquareReciprocalCapacityExcluding k E := by
      unfold actualZetaDyadicSquareReciprocalCapacityExcluding
      positivity
    have hactualLinearNonneg :
        0 ≤ actualZetaDyadicLinearReciprocalCapacityExcluding k E := by
      unfold actualZetaDyadicLinearReciprocalCapacityExcluding
      positivity
    have hweightNonneg : 0 ≤ (1 + 3 * C) * N := by positivity
    have hBLog :
        B * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 6)) ≤
          (3 * B) * N := by
      calc
        B * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 6)) ≤
            B * (3 * N) := mul_le_mul_of_nonneg_left hlogSix hB
        _ = (3 * B) * N := by ring
    have hsquareRaw := hsquare S Told sigma T k hTold hheight
    have hlinearRaw :=
      rightHigherActualZetaDyadicLinearCapacity_le_zeroDensityCount
        S (Told := Told) (sigma := sigma) (T := T) k (by linarith) hheight
    have hcountRaw := hKc k hkCarlson
    have hheightPos : 0 < (2 : ℝ) ^ (k + 1) := by positivity
    have hheightOne : 1 < (2 : ℝ) ^ (k + 1) :=
      one_lt_pow₀ (by norm_num) (by omega)
    have hlogHeightPos : 0 < Real.log ((2 : ℝ) ^ (k + 1)) :=
      Real.log_pos hheightOne
    have hmodelNonneg :
        0 ≤ ((2 : ℝ) ^ (k + 1)) ^ carlsonDyadicExponent sigma *
          Real.log ((2 : ℝ) ^ (k + 1)) ^ 4 := by
      exact mul_nonneg (Real.rpow_nonneg hheightPos.le _) (by positivity)
    have hcount :
        (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ (k + 1)) : ℝ) ≤
          D * (((2 : ℝ) ^ (k + 1)) ^ carlsonDyadicExponent sigma *
            Real.log ((2 : ℝ) ^ (k + 1)) ^ 4) := by
      change
        ‖(ZeroDensity.zeroDensityCount sigma
            ((2 : ℝ) ^ (k + 1)) : ℝ)‖ ≤
          D * ‖((2 : ℝ) ^ (k + 1)) ^ carlsonDyadicExponent sigma *
            Real.log ((2 : ℝ) ^ (k + 1)) ^ 4‖ at hcountRaw
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg
          (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ (k + 1)))),
        Real.norm_eq_abs, abs_of_nonneg hmodelNonneg] at hcountRaw
      exact hcountRaw
    have hlogTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogTwoLe : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlogHeightLe : Real.log ((2 : ℝ) ^ (k + 1)) ≤ N := by
      rw [Real.log_pow]
      dsimp [N]
      simpa using mul_le_mul_of_nonneg_left hlogTwoLe
        (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity)
    have hlogFourth :
        Real.log ((2 : ℝ) ^ (k + 1)) ^ 4 ≤ N ^ 4 :=
      pow_le_pow_left₀ hlogHeightPos.le hlogHeightLe 4
    have houterNonneg : 0 ≤ (3 * B) * N := by positivity
    have hinvNonneg : 0 ≤ ((((2 : ℝ) ^ k) ^ 2)⁻¹) := by positivity
    calc
      (1 + (dynamicComplementDyadicOccupancy E T k : ℝ)) *
          dynamicComplementDyadicSquareReciprocalCapacity E T k =
          (1 + (dynamicComplementDyadicOccupancy E T k : ℝ)) *
            actualZetaDyadicSquareReciprocalCapacityExcluding k E := by
        rw [dynamicComplementDyadicSquareReciprocalCapacity_eq_actual
          E k hheight]
      _ ≤ ((1 + 3 * C) * N) *
            actualZetaDyadicSquareReciprocalCapacityExcluding k E :=
        mul_le_mul_of_nonneg_right hoccupancyWeighted hactualSquareNonneg
      _ ≤ ((1 + 3 * C) * N) *
            ((B * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 6))) *
              actualZetaDyadicLinearReciprocalCapacityExcluding k E) :=
        mul_le_mul_of_nonneg_left hsquareRaw hweightNonneg
      _ ≤ ((1 + 3 * C) * N) *
            (((3 * B) * N) *
              actualZetaDyadicLinearReciprocalCapacityExcluding k E) := by
        gcongr
      _ ≤ ((1 + 3 * C) * N) *
            (((3 * B) * N) *
              (((((2 : ℝ) ^ k) ^ 2)⁻¹) *
                (ZeroDensity.zeroDensityCount sigma
                  ((2 : ℝ) ^ (k + 1)) : ℝ))) := by
        gcongr
      _ ≤ ((1 + 3 * C) * N) *
            (((3 * B) * N) *
              (((((2 : ℝ) ^ k) ^ 2)⁻¹) *
                (D * (((2 : ℝ) ^ (k + 1)) ^
                    carlsonDyadicExponent sigma *
                  Real.log ((2 : ℝ) ^ (k + 1)) ^ 4)))) := by
        gcongr
      _ ≤ ((1 + 3 * C) * N) *
            (((3 * B) * N) *
              (((((2 : ℝ) ^ k) ^ 2)⁻¹) *
                (D * (((2 : ℝ) ^ (k + 1)) ^
                    carlsonDyadicExponent sigma * N ^ 4)))) := by
        gcongr
      _ = (3 * B * (1 + 3 * C) * D) * N ^ 6 *
            (((((2 : ℝ) ^ k) ^ 2)⁻¹) *
              ((2 : ℝ) ^ (k + 1)) ^ carlsonDyadicExponent sigma) := by
        ring
      _ = A * carlsonDyadicEnergyMajorant sigma k := by
        rw [dyadic_carlson_power_identity]
        dsimp [A, carlsonDyadicEnergyMajorant, N]
        ring

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
      simp [dyadicUnitBucketRange]
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
        simp [dyadicUnitBucketRange]

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
