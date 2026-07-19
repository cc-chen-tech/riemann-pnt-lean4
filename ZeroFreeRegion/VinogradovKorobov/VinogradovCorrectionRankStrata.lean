import ZeroFreeRegion.VinogradovKorobov.VinogradovLowDiversityPrimePower

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Rank of the pair correction Jacobian attached to a prime-power base
solution. -/
def vinogradovPrimePowerPairJacobianRank
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n) : ℕ :=
  Module.finrank (ZMod p)
    (vinogradovPairCorrectionLinearMap p d s
      (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
      (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))).range

/-- Base solutions in one collision branch whose pair Jacobian has at least
the prescribed rank. -/
noncomputable def vinogradovPrimePowerFixedCollisionHighRankSolutionSet
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) :=
  (vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w).filter
    fun xy ↦ rankLower ≤
      vinogradovPrimePowerPairJacobianRank p k (b * k + r) n xy

/-- Complementary low-rank base solutions in the same collision branch. -/
noncomputable def vinogradovPrimePowerFixedCollisionLowRankSolutionSet
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) :=
  (vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w).filter
    fun xy ↦
      vinogradovPrimePowerPairJacobianRank p k (b * k + r) n xy < rankLower

theorem mem_vinogradovPrimePowerFixedCollisionHighRankSolutionSet_iff
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k)
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n rankLower w ↔
      xy ∈ vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w ∧
        rankLower ≤
          vinogradovPrimePowerPairJacobianRank p k (b * k + r) n xy := by
  simp [vinogradovPrimePowerFixedCollisionHighRankSolutionSet]

theorem mem_vinogradovPrimePowerFixedCollisionLowRankSolutionSet_iff
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k)
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerFixedCollisionLowRankSolutionSet
        p k r b n rankLower w ↔
      xy ∈ vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w ∧
        vinogradovPrimePowerPairJacobianRank p k (b * k + r) n xy <
          rankLower := by
  simp [vinogradovPrimePowerFixedCollisionLowRankSolutionSet]

/-- The high- and low-rank strata cover the fixed collision branch. -/
theorem vinogradovPrimePowerFixedCollision_rank_partition
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n rankLower w ∪
      vinogradovPrimePowerFixedCollisionLowRankSolutionSet
        p k r b n rankLower w =
      vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w := by
  ext xy
  by_cases hrank : rankLower ≤
      vinogradovPrimePowerPairJacobianRank p k (b * k + r) n xy
  · simp [vinogradovPrimePowerFixedCollisionHighRankSolutionSet,
      vinogradovPrimePowerFixedCollisionLowRankSolutionSet, hrank]
  · have hlow :
        vinogradovPrimePowerPairJacobianRank p k (b * k + r) n xy <
          rankLower := Nat.lt_of_not_ge hrank
    simp [vinogradovPrimePowerFixedCollisionHighRankSolutionSet,
      vinogradovPrimePowerFixedCollisionLowRankSolutionSet, hrank, hlow]

/-- The high- and low-rank base strata are disjoint. -/
theorem vinogradovPrimePowerFixedCollision_rank_disjoint
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Disjoint
      (vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n rankLower w)
      (vinogradovPrimePowerFixedCollisionLowRankSolutionSet
        p k r b n rankLower w) := by
  rw [Finset.disjoint_left]
  intro xy hhigh hlow
  have hrankHigh :=
    (mem_vinogradovPrimePowerFixedCollisionHighRankSolutionSet_iff
      p k r b n rankLower w xy).mp hhigh |>.2
  have hrankLow :=
    (mem_vinogradovPrimePowerFixedCollisionLowRankSolutionSet_iff
      p k r b n rankLower w xy).mp hlow |>.2
  exact (Nat.not_lt_of_ge hrankHigh) hrankLow

/-- One-step correction lifts whose base solution lies in the high-rank
stratum. -/
noncomputable def vinogradovPrimePowerFixedCollisionHighRankLiftSet
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Finset
      (Σ _ : vinogradovPrimePowerBasePair p 0 (b * k + r) n,
        vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :=
  (vinogradovPrimePowerFixedCollisionHighRankSolutionSet
    p k r b n rankLower w).sigma fun xy ↦
      vinogradovPrimePowerCorrectionSolutionSet p k (b * k + r) n xy

/-- The corresponding low-rank correction lifts, retained for the next
conditioning step. -/
noncomputable def vinogradovPrimePowerFixedCollisionLowRankLiftSet
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Finset
      (Σ _ : vinogradovPrimePowerBasePair p 0 (b * k + r) n,
        vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :=
  (vinogradovPrimePowerFixedCollisionLowRankSolutionSet
    p k r b n rankLower w).sigma fun xy ↦
      vinogradovPrimePowerCorrectionSolutionSet p k (b * k + r) n xy

/-- The lift-level high/low partition is exactly the existing full fixed
collision lift space. -/
theorem vinogradovPrimePowerFixedCollision_rank_lift_partition
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    vinogradovPrimePowerFixedCollisionHighRankLiftSet
        p k r b n rankLower w ∪
      vinogradovPrimePowerFixedCollisionLowRankLiftSet
        p k r b n rankLower w =
      vinogradovPrimePowerFixedCollisionSolutionLiftSet p k r b n w := by
  ext u
  rcases u with ⟨xy, z⟩
  by_cases hrank : rankLower ≤
      vinogradovPrimePowerPairJacobianRank p k (b * k + r) n xy
  · simp [vinogradovPrimePowerFixedCollisionHighRankLiftSet,
      vinogradovPrimePowerFixedCollisionLowRankLiftSet,
      vinogradovPrimePowerFixedCollisionHighRankSolutionSet,
      vinogradovPrimePowerFixedCollisionLowRankSolutionSet,
      vinogradovPrimePowerFixedCollisionSolutionLiftSet,
      vinogradovPrimePowerCorrectionSolutionSet, hrank]
  · have hlow :
        vinogradovPrimePowerPairJacobianRank p k (b * k + r) n xy <
          rankLower := Nat.lt_of_not_ge hrank
    simp [vinogradovPrimePowerFixedCollisionHighRankLiftSet,
      vinogradovPrimePowerFixedCollisionLowRankLiftSet,
      vinogradovPrimePowerFixedCollisionHighRankSolutionSet,
      vinogradovPrimePowerFixedCollisionLowRankSolutionSet,
      vinogradovPrimePowerFixedCollisionSolutionLiftSet,
      vinogradovPrimePowerCorrectionSolutionSet, hrank, hlow]

/-- The high- and low-rank correction-lift strata are disjoint. -/
theorem vinogradovPrimePowerFixedCollision_rank_lift_disjoint
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    Disjoint
      (vinogradovPrimePowerFixedCollisionHighRankLiftSet
        p k r b n rankLower w)
      (vinogradovPrimePowerFixedCollisionLowRankLiftSet
        p k r b n rankLower w) := by
  rw [Finset.disjoint_left]
  intro u hhigh hlow
  rcases u with ⟨xy, z⟩
  have hhighBase :
      xy ∈ vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n rankLower w := by
    have hz :
        xy ∈ vinogradovPrimePowerFixedCollisionHighRankSolutionSet
            p k r b n rankLower w ∧
          z ∈ vinogradovPrimePowerCorrectionSolutionSet
            p k (b * k + r) n xy := by
      simpa [vinogradovPrimePowerFixedCollisionHighRankLiftSet] using hhigh
    exact hz.1
  have hlowBase :
      xy ∈ vinogradovPrimePowerFixedCollisionLowRankSolutionSet
        p k r b n rankLower w := by
    have hz :
        xy ∈ vinogradovPrimePowerFixedCollisionLowRankSolutionSet
            p k r b n rankLower w ∧
          z ∈ vinogradovPrimePowerCorrectionSolutionSet
            p k (b * k + r) n xy := by
      simpa [vinogradovPrimePowerFixedCollisionLowRankLiftSet] using hlow
    exact hz.1
  exact (Finset.disjoint_left.mp
    (vinogradovPrimePowerFixedCollision_rank_disjoint
      p k r b n rankLower w)) hhighBase hlowBase

/-- The full fixed-collision lift count is the exact sum of its rank strata. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionLiftSet_eq_rank_add
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionLiftSet p k r b n w).card =
      (vinogradovPrimePowerFixedCollisionHighRankLiftSet
        p k r b n rankLower w).card +
      (vinogradovPrimePowerFixedCollisionLowRankLiftSet
        p k r b n rankLower w).card := by
  rw [← vinogradovPrimePowerFixedCollision_rank_lift_partition
    p k r b n rankLower w]
  exact Finset.card_union_of_disjoint
    (vinogradovPrimePowerFixedCollision_rank_lift_disjoint
      p k r b n rankLower w)

/-- High-rank lifts have the expected `p^(2s-rankLower)` loss. -/
theorem card_vinogradovPrimePowerFixedCollisionHighRankLiftSet_le
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionHighRankLiftSet
      p k r b n rankLower w).card ≤
      (vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n rankLower w).card *
        p ^ (2 * (b * k + r) - rankLower) := by
  rw [vinogradovPrimePowerFixedCollisionHighRankLiftSet,
    Finset.card_sigma]
  calc
    (∑ xy ∈ vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n rankLower w,
        (vinogradovPrimePowerCorrectionSolutionSet
          p k (b * k + r) n xy).card) ≤
      ∑ _xy ∈ vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n rankLower w,
        p ^ (2 * (b * k + r) - rankLower) := by
      apply Finset.sum_le_sum
      intro xy hxy
      have hrank :=
        (mem_vinogradovPrimePowerFixedCollisionHighRankSolutionSet_iff
          p k r b n rankLower w xy).mp hxy |>.2
      calc
        (vinogradovPrimePowerCorrectionSolutionSet
            p k (b * k + r) n xy).card ≤
          p ^ (2 * (b * k + r) -
            vinogradovPrimePowerPairJacobianRank
              p k (b * k + r) n xy) := by
            exact card_vinogradovPrimePowerCorrectionSolutionSet_le_pow_rankDefect
              p k (b * k + r) n xy
        _ ≤ p ^ (2 * (b * k + r) - rankLower) := by
          exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
            (Nat.sub_le_sub_left hrank _)
    _ = (vinogradovPrimePowerFixedCollisionHighRankSolutionSet
          p k r b n rankLower w).card *
        p ^ (2 * (b * k + r) - rankLower) := by
      simp

/-- One prime-power step splits into a controlled high-rank contribution and
an explicit low-rank remainder. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionSet_succ_le_rank_split
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionSet
      p k r b (n + 1) w).card ≤
      (vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n rankLower w).card *
          p ^ (2 * (b * k + r) - rankLower) +
        (vinogradovPrimePowerFixedCollisionLowRankLiftSet
          p k r b n rankLower w).card := by
  rw [card_vinogradovPrimePowerFixedCollisionSolutionSet_succ]
  calc
    (vinogradovPrimePowerFixedCollisionSolutionLiftSet
        p k r b n w).card =
      (vinogradovPrimePowerFixedCollisionHighRankLiftSet
          p k r b n rankLower w ∪
        vinogradovPrimePowerFixedCollisionLowRankLiftSet
          p k r b n rankLower w).card := by
        rw [vinogradovPrimePowerFixedCollision_rank_lift_partition]
    _ ≤ (vinogradovPrimePowerFixedCollisionHighRankLiftSet
          p k r b n rankLower w).card +
        (vinogradovPrimePowerFixedCollisionLowRankLiftSet
          p k r b n rankLower w).card :=
      Finset.card_union_le _ _
    _ ≤ (vinogradovPrimePowerFixedCollisionHighRankSolutionSet
          p k r b n rankLower w).card *
          p ^ (2 * (b * k + r) - rankLower) +
        (vinogradovPrimePowerFixedCollisionLowRankLiftSet
          p k r b n rankLower w).card := by
      exact Nat.add_le_add_right
        (card_vinogradovPrimePowerFixedCollisionHighRankLiftSet_le
          p k r b n rankLower w) _

/-- For a square system below the characteristic, a low-rank base pair must
have collisions on both sides. -/
theorem vinogradovPrimePowerPairJacobianRank_lt_both_not_injective
    (p d n : ℕ) [Fact p.Prime] (hdp : d < p)
    (xy : vinogradovPrimePowerBasePair p 0 d n)
    (hrank : vinogradovPrimePowerPairJacobianRank p d d n xy < d) :
    (¬Function.Injective fun i ↦
        (vinogradovPrimePowerBaseLeftInt xy i : ZMod p)) ∧
      ¬Function.Injective fun i ↦
        (vinogradovPrimePowerBaseRightInt xy i : ZMod p) := by
  exact ⟨
    not_injective_left_of_finrank_vinogradovPairCorrectionLinearMap_range_lt
      p d hdp _ _ hrank,
    not_injective_right_of_finrank_vinogradovPairCorrectionLinearMap_range_lt
      p d hdp _ _ hrank⟩

/-- In an arbitrary-length system below the characteristic, rank deficiency
rules out selecting `d` pairwise distinct residues on either side. -/
theorem vinogradovPrimePowerPairJacobianRank_lt_no_injective_selection
    (p d s n : ℕ) [Fact p.Prime] (hdp : d < p)
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (hrank : vinogradovPrimePowerPairJacobianRank p d s n xy < d) :
    (¬∃ ι : Fin d ↪ Fin s,
        Function.Injective fun i ↦
          (vinogradovPrimePowerBaseLeftInt xy (ι i) : ZMod p)) ∧
      ¬∃ ι : Fin d ↪ Fin s,
        Function.Injective fun i ↦
          (vinogradovPrimePowerBaseRightInt xy (ι i) : ZMod p) := by
  exact ⟨
    not_exists_left_selection_of_finrank_vinogradovPairCorrectionLinearMap_range_lt
      p d s hdp _ _ hrank,
    not_exists_right_selection_of_finrank_vinogradovPairCorrectionLinearMap_range_lt
      p d s hdp _ _ hrank⟩

/-- At the full-rank threshold `k`, every low-rank base solution lies in the
ambient set where both residue tuples use fewer than `k` values. -/
theorem vinogradovPrimePowerFixedCollisionLowRankSolutionSet_subset_lowDiversity
    (p k r b n : ℕ) [Fact p.Prime] (hkp : k < p)
    (w : Fin b → VinogradovCollisionWitness k) :
    vinogradovPrimePowerFixedCollisionLowRankSolutionSet
        p k r b n k w ⊆
      vinogradovPrimePowerLowDiversityAmbientSet
        p (b * k + r) k n := by
  intro xy hxy
  have hrank :=
    (mem_vinogradovPrimePowerFixedCollisionLowRankSolutionSet_iff
      p k r b n k w xy).mp hxy |>.2
  have hno :=
    vinogradovPrimePowerPairJacobianRank_lt_no_injective_selection
      p k (b * k + r) n hkp xy hrank
  rw [mem_vinogradovPrimePowerLowDiversityAmbientSet_iff]
  constructor
  · apply
      (no_injective_selection_iff_mem_vinogradovLowDiversityTupleSet
        p (b * k + r) k
          (vinogradovPrimePowerBaseLeftResidue
            p (b * k + r) n xy)).mp
    simpa [vinogradovPrimePowerBaseLeftResidue] using hno.1
  · apply
      (no_injective_selection_iff_mem_vinogradovLowDiversityTupleSet
        p (b * k + r) k
          (vinogradovPrimePowerBaseRightResidue
            p (b * k + r) n xy)).mp
    simpa [vinogradovPrimePowerBaseRightResidue] using hno.2

/-- The low-rank correction lifts form a subset of the unrestricted
low-diversity ambient lift space. -/
theorem vinogradovPrimePowerFixedCollisionLowRankLiftSet_subset_lowDiversity
    (p k r b n : ℕ) [Fact p.Prime] (hkp : k < p)
    (w : Fin b → VinogradovCollisionWitness k) :
    vinogradovPrimePowerFixedCollisionLowRankLiftSet
        p k r b n k w ⊆
      vinogradovPrimePowerLowDiversityAmbientLiftSet
        p (b * k + r) k n := by
  intro u hu
  rcases u with ⟨xy, z⟩
  have hu' :
      xy ∈ vinogradovPrimePowerFixedCollisionLowRankSolutionSet
          p k r b n k w ∧
        z ∈ vinogradovPrimePowerCorrectionSolutionSet
          p k (b * k + r) n xy := by
    simpa [vinogradovPrimePowerFixedCollisionLowRankLiftSet] using hu
  simp only [vinogradovPrimePowerLowDiversityAmbientLiftSet,
    Finset.mem_sigma, Finset.mem_univ, and_true]
  exact vinogradovPrimePowerFixedCollisionLowRankSolutionSet_subset_lowDiversity
    p k r b n hkp w hu'.1

/-- Explicit uniform bound for the formerly uncontrolled low-rank lift
remainder. -/
theorem card_vinogradovPrimePowerFixedCollisionLowRankLiftSet_le_lowDiversity
    (p k r b n : ℕ) [Fact p.Prime] (hkp : k < p)
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionLowRankLiftSet
      p k r b n k w).card ≤
      (p ^ (k - 1) * (k - 1) ^ (b * k + r)) ^ 2 *
        (p ^ (2 * (b * k + r))) ^ (n + 1) := by
  let q := p ^ (2 * (b * k + r))
  let B := (p ^ (k - 1) * (k - 1) ^ (b * k + r)) ^ 2
  calc
    (vinogradovPrimePowerFixedCollisionLowRankLiftSet
        p k r b n k w).card ≤
        (vinogradovPrimePowerLowDiversityAmbientLiftSet
          p (b * k + r) k n).card :=
      Finset.card_le_card
        (vinogradovPrimePowerFixedCollisionLowRankLiftSet_subset_lowDiversity
          p k r b n hkp w)
    _ = (vinogradovPrimePowerLowDiversityAmbientSet
          p (b * k + r) k n).card * q := by
      exact card_vinogradovPrimePowerLowDiversityAmbientLiftSet
        p (b * k + r) k n
    _ ≤ B * q ^ n * q := by
      exact Nat.mul_le_mul_right q
        (card_vinogradovPrimePowerLowDiversityAmbientSet_le
          p (b * k + r) k n)
    _ = B * q ^ (n + 1) := by
      rw [pow_succ, mul_assoc]

/-- A closed one-step recurrence: the full-rank stratum gains `k` powers of
`p`, while the low-rank stratum is bounded by the low-diversity count. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionSet_succ_le_fullRank_lowDiversity
    (p k r b n : ℕ) [Fact p.Prime] (hkp : k < p)
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionSet
      p k r b (n + 1) w).card ≤
      (vinogradovPrimePowerFixedCollisionSolutionSet
        p k r b n w).card *
          p ^ (2 * (b * k + r) - k) +
        (p ^ (k - 1) * (k - 1) ^ (b * k + r)) ^ 2 *
          (p ^ (2 * (b * k + r))) ^ (n + 1) := by
  calc
    (vinogradovPrimePowerFixedCollisionSolutionSet
        p k r b (n + 1) w).card ≤
      (vinogradovPrimePowerFixedCollisionHighRankSolutionSet
        p k r b n k w).card *
          p ^ (2 * (b * k + r) - k) +
        (vinogradovPrimePowerFixedCollisionLowRankLiftSet
          p k r b n k w).card :=
      card_vinogradovPrimePowerFixedCollisionSolutionSet_succ_le_rank_split
        p k r b n k w
    _ ≤ (vinogradovPrimePowerFixedCollisionSolutionSet
          p k r b n w).card *
            p ^ (2 * (b * k + r) - k) +
          (p ^ (k - 1) * (k - 1) ^ (b * k + r)) ^ 2 *
            (p ^ (2 * (b * k + r))) ^ (n + 1) := by
      apply Nat.add_le_add
      · apply Nat.mul_le_mul_right
        exact Finset.card_le_card (Finset.filter_subset _ _)
      · exact
          card_vinogradovPrimePowerFixedCollisionLowRankLiftSet_le_lowDiversity
            p k r b n hkp w

end

end ZeroFreeRegion.VinogradovKorobov
