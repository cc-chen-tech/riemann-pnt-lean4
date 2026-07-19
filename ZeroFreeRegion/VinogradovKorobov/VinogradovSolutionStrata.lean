import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerFiber

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The finite set of all ordered pairs solving the modular Vinogradov
system.  Its coordinates agree with `vinogradovSolutionCountMod`. -/
noncomputable def vinogradovSolutionPairSetMod
    (Q d s X : ℕ) :
    Finset ((Fin s → Fin X) × (Fin s → Fin X)) := by
  classical
  exact
    (Finset.univ.sigma fun x : Fin s → Fin X ↦
      Finset.univ.filter fun y : Fin s → Fin X ↦
        IsVinogradovSolutionMod Q d s X x y).map
      (Equiv.sigmaEquivProd (Fin s → Fin X) (Fin s → Fin X)).toEmbedding

/-- Membership in the pair set is precisely the modular Vinogradov system. -/
theorem mem_vinogradovSolutionPairSetMod_iff
    (Q d s X : ℕ) (x y : Fin s → Fin X) :
    (x, y) ∈ vinogradovSolutionPairSetMod Q d s X ↔
      IsVinogradovSolutionMod Q d s X x y := by
  classical
  simp [vinogradovSolutionPairSetMod]

/-- The pair-set cardinality recovers the modular solution count used by the
finite-moment identity. -/
theorem card_vinogradovSolutionPairSetMod
    (Q d s X : ℕ) :
    (vinogradovSolutionPairSetMod Q d s X).card =
      vinogradovSolutionCountMod Q d s X := by
  classical
  rw [vinogradovSolutionPairSetMod, Finset.card_map, Finset.card_sigma]
  rfl

/-- Complete modular solutions whose first `k` left coordinates are pairwise
distinct. -/
noncomputable def vinogradovBlockNonsingularSolutionSetMod
    (p d k r : ℕ) [Fact p.Prime] :
    Finset ((Fin (k + r) → Fin p) × (Fin (k + r) → Fin p)) := by
  classical
  exact (vinogradovSolutionPairSetMod p d (k + r) p).filter fun xy ↦
    Function.Injective (fun i : Fin k ↦ xy.1 (Fin.castAdd r i))

/-- Membership in the nonsingular stratum consists of the original modular
equations together with injectivity of the selected left block. -/
theorem mem_vinogradovBlockNonsingularSolutionSetMod_iff
    (p d k r : ℕ) [Fact p.Prime]
    (x y : Fin (k + r) → Fin p) :
    (x, y) ∈ vinogradovBlockNonsingularSolutionSetMod p d k r ↔
      Function.Injective (fun i : Fin k ↦ x (Fin.castAdd r i)) ∧
        IsVinogradovSolutionMod p d (k + r) p x y := by
  classical
  simp [vinogradovBlockNonsingularSolutionSetMod,
    mem_vinogradovSolutionPairSetMod_iff, and_comm]

/-- The complete modular solution count splits exactly into its singular and
nonsingular left-block strata. -/
theorem card_singular_add_card_nonsingular_eq_vinogradovSolutionCountMod
    (p d k r : ℕ) [Fact p.Prime] :
    (vinogradovBlockSingularSolutionSetMod p d k r).card +
        (vinogradovBlockNonsingularSolutionSetMod p d k r).card =
      vinogradovSolutionCountMod p d (k + r) p := by
  classical
  let all := vinogradovSolutionPairSetMod p d (k + r) p
  let good : ((Fin (k + r) → Fin p) × (Fin (k + r) → Fin p)) → Prop :=
    fun xy ↦ Function.Injective
      (fun i : Fin k ↦ xy.1 (Fin.castAdd r i))
  have hsing :
      vinogradovBlockSingularSolutionSetMod p d k r =
        all.filter fun xy ↦ ¬good xy := by
    ext xy
    rcases xy with ⟨x, y⟩
    simp [all, good, mem_vinogradovBlockSingularSolutionSetMod_iff,
      mem_vinogradovSolutionPairSetMod_iff, and_comm]
  have hgood :
      vinogradovBlockNonsingularSolutionSetMod p d k r =
        all.filter good := by
    rfl
  rw [hsing, hgood, ← card_vinogradovSolutionPairSetMod p d (k + r) p]
  simpa [add_comm] using
    (Finset.card_filter_add_card_filter_not (s := all) good)

/-- The exact split and the one-power estimate isolate the remaining
nonsingular contribution to the complete modular moment. -/
theorem vinogradovSolutionCountMod_le_nonsingular_add_error
    (p d k r : ℕ) [Fact p.Prime] :
    vinogradovSolutionCountMod p d (k + r) p ≤
      (vinogradovBlockNonsingularSolutionSetMod p d k r).card +
        k ^ 2 * p ^ (2 * (k + r) - 1) := by
  have hsplit :=
    card_singular_add_card_nonsingular_eq_vinogradovSolutionCountMod
      p d k r
  rw [← hsplit]
  calc
    (vinogradovBlockSingularSolutionSetMod p d k r).card +
          (vinogradovBlockNonsingularSolutionSetMod p d k r).card ≤
        k ^ 2 * p ^ (2 * (k + r) - 1) +
          (vinogradovBlockNonsingularSolutionSetMod p d k r).card :=
      Nat.add_le_add_right
        (card_vinogradovBlockSingularSolutionSetMod_le p d k r) _
    _ = (vinogradovBlockNonsingularSolutionSetMod p d k r).card +
        k ^ 2 * p ^ (2 * (k + r) - 1) := by omega

end

end ZeroFreeRegion.VinogradovKorobov
