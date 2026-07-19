import ZeroFreeRegion.VinogradovKorobov.VinogradovCorrectionFiber

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

end

end ZeroFreeRegion.VinogradovKorobov
