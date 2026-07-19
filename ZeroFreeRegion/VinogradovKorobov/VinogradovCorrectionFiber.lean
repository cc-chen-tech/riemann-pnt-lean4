import ZeroFreeRegion.VinogradovKorobov.VinogradovRectangularJacobian
import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerCollisionFiber

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Repackage the split digit representation at tuple length `0+s` as an
ordinary pair of `s`-tuples over `ZMod p`. -/
def vinogradovPrimePowerCorrectionPairEquiv
    (p s : ℕ) [Fact p.Prime] :
    vinogradovPrimePowerSplitCorrection p 0 s ≃
      ((Fin s → ZMod p) × (Fin s → ZMod p)) :=
  (vinogradovSplitCorrectionEquiv p 0 s).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (finCongr (Nat.zero_add s)) (Equiv.refl _))
      (Equiv.arrowCongr (finCongr (Nat.zero_add s)) (Equiv.refl _)))

theorem vinogradovPrimePowerCorrectionPairEquiv_apply_fst
    (p s : ℕ) [Fact p.Prime]
    (z : vinogradovPrimePowerSplitCorrection p 0 s) (i : Fin s) :
    (vinogradovPrimePowerCorrectionPairEquiv p s z).1 i =
      (vinogradovSplitCorrectionEquiv p 0 s z).1 (Fin.natAdd 0 i) := by
  simp [vinogradovPrimePowerCorrectionPairEquiv]

theorem vinogradovPrimePowerCorrectionPairEquiv_apply_snd
    (p s : ℕ) [Fact p.Prime]
    (z : vinogradovPrimePowerSplitCorrection p 0 s) (i : Fin s) :
    (vinogradovPrimePowerCorrectionPairEquiv p s z).2 i =
      (vinogradovSplitCorrectionEquiv p 0 s z).2 (Fin.natAdd 0 i) := by
  simp [vinogradovPrimePowerCorrectionPairEquiv]

/-- All one-digit corrections above one fixed base pair which satisfy the
degree-`d` Vinogradov system at the next prime-power level. -/
noncomputable def vinogradovPrimePowerCorrectionSolutionSet
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n) :
    Finset (vinogradovPrimePowerSplitCorrection p 0 s) :=
  Finset.univ.filter fun z ↦
    IsVinogradovSolutionMod (p ^ (n + 2)) d s (p ^ (n + 2))
      (fun i ↦
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).1
          (Fin.natAdd 0 i))
      (fun i ↦
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).2
          (Fin.natAdd 0 i))

theorem mem_vinogradovPrimePowerCorrectionSolutionSet_iff
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s) :
    z ∈ vinogradovPrimePowerCorrectionSolutionSet p d s n xy ↔
      IsVinogradovSolutionMod (p ^ (n + 2)) d s (p ^ (n + 2))
        (fun i ↦
          (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).1
            (Fin.natAdd 0 i))
        (fun i ↦
          (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).2
            (Fin.natAdd 0 i)) := by
  simp [vinogradovPrimePowerCorrectionSolutionSet]

/-- One-based integer representatives of the left base tuple. -/
def vinogradovPrimePowerBaseLeftInt
    {p s n : ℕ} (xy : vinogradovPrimePowerBasePair p 0 s n) :
    Fin s → ℤ :=
  fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ℤ)

/-- One-based integer representatives of the right base tuple. -/
def vinogradovPrimePowerBaseRightInt
    {p s n : ℕ} (xy : vinogradovPrimePowerBasePair p 0 s n) :
    Fin s → ℤ :=
  fun i ↦ (((xy.2 (Fin.natAdd 0 i)).val + 1 : ℕ) : ℤ)

theorem vinogradovPrimePowerLiftAmbientEquiv_fst_val_add_one
    (p s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s) (i : Fin s) :
    (((((vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).1
          (Fin.natAdd 0 i)).val + 1 : ℕ)) : ℤ) =
      vinogradovPrimePowerBaseLeftInt xy i +
        (p : ℤ) ^ (n + 1) *
          ((vinogradovPrimePowerCorrectionPairEquiv p s z).1 i).val := by
  rw [vinogradovPrimePowerLiftAmbientEquiv_apply_fst_val]
  rw [vinogradovPrimePowerCorrectionPairEquiv_apply_fst]
  simp [vinogradovPrimePowerBaseLeftInt]
  ring

theorem vinogradovPrimePowerLiftAmbientEquiv_snd_val_add_one
    (p s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s) (i : Fin s) :
    (((((vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).2
          (Fin.natAdd 0 i)).val + 1 : ℕ)) : ℤ) =
      vinogradovPrimePowerBaseRightInt xy i +
        (p : ℤ) ^ (n + 1) *
          ((vinogradovPrimePowerCorrectionPairEquiv p s z).2 i).val := by
  rw [vinogradovPrimePowerLiftAmbientEquiv_apply_snd_val]
  rw [vinogradovPrimePowerCorrectionPairEquiv_apply_snd]
  simp [vinogradovPrimePowerBaseRightInt]
  ring

/-- Membership in a correction solution set supplies the affine integer
power-sum congruences needed by the finite-field linearization theorem. -/
theorem vinogradovPrimePowerCorrectionSolutionSet_powerSum_modEq
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s)
    (hz : z ∈ vinogradovPrimePowerCorrectionSolutionSet p d s n xy) :
    ∀ j : Fin d,
      vinogradovPowerSumInt
          (fun i ↦ vinogradovPrimePowerBaseLeftInt xy i +
            (p : ℤ) ^ (n + 1) *
              ((vinogradovPrimePowerCorrectionPairEquiv p s z).1 i).val) j ≡
        vinogradovPowerSumInt
          (fun i ↦ vinogradovPrimePowerBaseRightInt xy i +
            (p : ℤ) ^ (n + 1) *
              ((vinogradovPrimePowerCorrectionPairEquiv p s z).2 i).val) j
        [ZMOD (p : ℤ) ^ (n + 2)] := by
  intro j
  have hj :=
    (isVinogradovSolutionMod_iff_powerSumInt_modEq
      (p ^ (n + 2)) d s (p ^ (n + 2))
      (fun i ↦
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).1
          (Fin.natAdd 0 i))
      (fun i ↦
        (vinogradovPrimePowerLiftAmbientEquiv p 0 s n ⟨xy, z⟩).2
          (Fin.natAdd 0 i))).mp
      ((mem_vinogradovPrimePowerCorrectionSolutionSet_iff
        p d s n xy z).mp hz) j
  simpa only [vinogradovPrimePowerLiftAmbientEquiv_fst_val_add_one,
    vinogradovPrimePowerLiftAmbientEquiv_snd_val_add_one] using hj

/-- Any two admissible one-step corrections above the same base pair have
the same image under the pair Jacobian. -/
theorem vinogradovPairCorrectionLinearMap_eq_of_mem_correctionSolutionSet
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z z' : vinogradovPrimePowerSplitCorrection p 0 s)
    (hz : z ∈ vinogradovPrimePowerCorrectionSolutionSet p d s n xy)
    (hz' : z' ∈ vinogradovPrimePowerCorrectionSolutionSet p d s n xy) :
    vinogradovPairCorrectionLinearMap p d s
        (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
        (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))
        (vinogradovPrimePowerCorrectionPairEquiv p s z) =
      vinogradovPairCorrectionLinearMap p d s
        (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
        (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))
        (vinogradovPrimePowerCorrectionPairEquiv p s z') := by
  have h := vinogradovPairCorrectionLinearMap_eq_of_affine_solutions
    p d s n
    (vinogradovPrimePowerBaseLeftInt xy)
    (vinogradovPrimePowerBaseRightInt xy)
    (fun i ↦ ((vinogradovPrimePowerCorrectionPairEquiv p s z).1 i).val)
    (fun i ↦ ((vinogradovPrimePowerCorrectionPairEquiv p s z).2 i).val)
    (fun i ↦ ((vinogradovPrimePowerCorrectionPairEquiv p s z').1 i).val)
    (fun i ↦ ((vinogradovPrimePowerCorrectionPairEquiv p s z').2 i).val)
    (vinogradovPrimePowerCorrectionSolutionSet_powerSum_modEq
      p d s n xy z hz)
    (vinogradovPrimePowerCorrectionSolutionSet_powerSum_modEq
      p d s n xy z' hz')
  simpa using h

/-- A nonempty one-step correction solution set injects into the Jacobian
fiber through any one of its members. -/
theorem card_vinogradovPrimePowerCorrectionSolutionSet_le_fiber
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s)
    (hz : z ∈ vinogradovPrimePowerCorrectionSolutionSet p d s n xy) :
    (vinogradovPrimePowerCorrectionSolutionSet p d s n xy).card ≤
      (vinogradovPairCorrectionFiberSet p d s
        (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
        (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))
        (vinogradovPrimePowerCorrectionPairEquiv p s z)).card := by
  rw [← Finset.card_map
    (vinogradovPrimePowerCorrectionPairEquiv p s).toEmbedding]
  apply Finset.card_le_card
  intro uv huv
  obtain ⟨z', hz', rfl⟩ := Finset.mem_map.mp huv
  rw [mem_vinogradovPairCorrectionFiberSet_iff]
  exact vinogradovPairCorrectionLinearMap_eq_of_mem_correctionSolutionSet
    p d s n xy z' z hz' hz

/-- Consequently, every nonempty one-step correction solution set is bounded
by the kernel cardinality of the pair Jacobian at its base pair. -/
theorem card_vinogradovPrimePowerCorrectionSolutionSet_le_card_ker
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n)
    (z : vinogradovPrimePowerSplitCorrection p 0 s)
    (hz : z ∈ vinogradovPrimePowerCorrectionSolutionSet p d s n xy) :
    (vinogradovPrimePowerCorrectionSolutionSet p d s n xy).card ≤
      Nat.card
        (vinogradovPairCorrectionLinearMap p d s
          (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
          (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))).ker := by
  rw [← card_vinogradovPairCorrectionFiberSet_eq_card_ker p d s
    (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
    (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))
    (vinogradovPrimePowerCorrectionPairEquiv p s z)]
  exact card_vinogradovPrimePowerCorrectionSolutionSet_le_fiber
    p d s n xy z hz

/-- The correction count above every base pair, including the empty case, is
bounded by the exact finite-field rank defect. -/
theorem card_vinogradovPrimePowerCorrectionSolutionSet_le_pow_rankDefect
    (p d s n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 s n) :
    (vinogradovPrimePowerCorrectionSolutionSet p d s n xy).card ≤
      p ^ (2 * s - Module.finrank (ZMod p)
        (vinogradovPairCorrectionLinearMap p d s
          (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
          (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))).range) := by
  by_cases hnonempty :
      (vinogradovPrimePowerCorrectionSolutionSet p d s n xy).Nonempty
  · obtain ⟨z, hz⟩ := hnonempty
    calc
      (vinogradovPrimePowerCorrectionSolutionSet p d s n xy).card ≤
          (vinogradovPairCorrectionFiberSet p d s
            (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
            (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))
            (vinogradovPrimePowerCorrectionPairEquiv p s z)).card :=
        card_vinogradovPrimePowerCorrectionSolutionSet_le_fiber
          p d s n xy z hz
      _ = p ^ (2 * s - Module.finrank (ZMod p)
          (vinogradovPairCorrectionLinearMap p d s
            (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
            (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))).range) :=
        card_vinogradovPairCorrectionFiberSet_eq_pow_rankDefect
          p d s _ _ _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    simp

/-- With at least one equation and one variable, the first power-sum row
already saves one factor of `p` over the unrestricted correction count. -/
theorem card_vinogradovPrimePowerCorrectionSolutionSet_le_pow_pred
    (p d s n : ℕ) [Fact p.Prime] (hd : 0 < d) (hs : 0 < s)
    (xy : vinogradovPrimePowerBasePair p 0 s n) :
    (vinogradovPrimePowerCorrectionSolutionSet p d s n xy).card ≤
      p ^ (2 * s - 1) := by
  calc
    (vinogradovPrimePowerCorrectionSolutionSet p d s n xy).card ≤
      p ^ (2 * s - Module.finrank (ZMod p)
        (vinogradovPairCorrectionLinearMap p d s
          (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
          (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))).range) :=
      card_vinogradovPrimePowerCorrectionSolutionSet_le_pow_rankDefect
        p d s n xy
    _ ≤ p ^ (2 * s - 1) := by
      apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      exact Nat.sub_le_sub_left
        (one_le_finrank_vinogradovPairCorrectionLinearMap_range
          p d s hd hs _ _) _

/-- The exact fixed-collision lift recurrence is bounded by the sum of the
Jacobian rank-defect factors over its base solutions. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionLiftSet_le_rankDefects
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionLiftSet p k r b n w).card ≤
      ∑ xy ∈ vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w,
        p ^ (2 * (b * k + r) - Module.finrank (ZMod p)
          (vinogradovPairCorrectionLinearMap p k (b * k + r)
            (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
            (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))).range) := by
  rw [vinogradovPrimePowerFixedCollisionSolutionLiftSet,
    Finset.card_sigma]
  apply Finset.sum_le_sum
  intro xy hxy
  change (vinogradovPrimePowerCorrectionSolutionSet
    p k (b * k + r) n xy).card ≤ _
  exact card_vinogradovPrimePowerCorrectionSolutionSet_le_pow_rankDefect
    p k (b * k + r) n xy

/-- A uniform lower bound on pair-Jacobian rank gives the corresponding
uniform one-step lift bound on a fixed collision branch. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionLiftSet_le_of_rank
    (p k r b n rankLower : ℕ) [Fact p.Prime]
    (w : Fin b → VinogradovCollisionWitness k)
    (hrank : ∀ xy ∈
      vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w,
      rankLower ≤ Module.finrank (ZMod p)
        (vinogradovPairCorrectionLinearMap p k (b * k + r)
          (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
          (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))).range) :
    (vinogradovPrimePowerFixedCollisionSolutionLiftSet p k r b n w).card ≤
      (vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w).card *
        p ^ (2 * (b * k + r) - rankLower) := by
  calc
    (vinogradovPrimePowerFixedCollisionSolutionLiftSet
        p k r b n w).card ≤
      ∑ xy ∈ vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w,
        p ^ (2 * (b * k + r) - Module.finrank (ZMod p)
          (vinogradovPairCorrectionLinearMap p k (b * k + r)
            (fun i ↦ (vinogradovPrimePowerBaseLeftInt xy i : ZMod p))
            (fun i ↦ (vinogradovPrimePowerBaseRightInt xy i : ZMod p))).range) :=
      card_vinogradovPrimePowerFixedCollisionSolutionLiftSet_le_rankDefects
        p k r b n w
    _ ≤ ∑ _xy ∈
        vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w,
        p ^ (2 * (b * k + r) - rankLower) := by
      apply Finset.sum_le_sum
      intro xy hxy
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
        (Nat.sub_le_sub_left (hrank xy hxy) _)
    _ = (vinogradovPrimePowerFixedCollisionSolutionSet
          p k r b n w).card *
        p ^ (2 * (b * k + r) - rankLower) := by
      simp

/-- Unconditionally, every nontrivial fixed collision branch saves at least
one residue digit in each prime-power lifting step. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionLiftSet_le_pow_pred
    (p k r b n : ℕ) [Fact p.Prime]
    (hk : 0 < k) (hs : 0 < b * k + r)
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionLiftSet p k r b n w).card ≤
      (vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w).card *
        p ^ (2 * (b * k + r) - 1) := by
  apply card_vinogradovPrimePowerFixedCollisionSolutionLiftSet_le_of_rank
    p k r b n 1 w
  intro xy _hxy
  exact one_le_finrank_vinogradovPairCorrectionLinearMap_range
    p k (b * k + r) hk hs _ _

/-- The same one-factor saving stated directly as a recurrence for a fixed
collision solution branch. -/
theorem card_vinogradovPrimePowerFixedCollisionSolutionSet_succ_le_pow_pred
    (p k r b n : ℕ) [Fact p.Prime]
    (hk : 0 < k) (hs : 0 < b * k + r)
    (w : Fin b → VinogradovCollisionWitness k) :
    (vinogradovPrimePowerFixedCollisionSolutionSet
      p k r b (n + 1) w).card ≤
      (vinogradovPrimePowerFixedCollisionSolutionSet p k r b n w).card *
        p ^ (2 * (b * k + r) - 1) := by
  rw [card_vinogradovPrimePowerFixedCollisionSolutionSet_succ]
  exact card_vinogradovPrimePowerFixedCollisionSolutionLiftSet_le_pow_pred
    p k r b n hk hs w

end

end ZeroFreeRegion.VinogradovKorobov
