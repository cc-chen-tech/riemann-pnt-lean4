import ZeroFreeRegion.VinogradovKorobov.VinogradovMultiBlock

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance vinogradovSingularWitnessPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- An ordered pair of distinct coordinates, stored in increasing order. -/
abbrev VinogradovCollisionWitness (k : ℕ) :=
  {ij : Fin k × Fin k // ij.1 < ij.2}

/-- All coordinate pairs witnessing that a tuple is not injective. -/
noncomputable def vinogradovCollisionWitnessSet
    {α : Type*} [DecidableEq α] {k : ℕ} (x : Fin k → α) :
    Finset (VinogradovCollisionWitness k) :=
  Finset.univ.filter fun w ↦ x w.1.1 = x w.1.2

theorem mem_vinogradovCollisionWitnessSet_iff
    {α : Type*} [DecidableEq α] {k : ℕ} (x : Fin k → α)
    (w : VinogradovCollisionWitness k) :
    w ∈ vinogradovCollisionWitnessSet x ↔ x w.1.1 = x w.1.2 := by
  simp [vinogradovCollisionWitnessSet]

/-- A finite tuple has a collision witness exactly when it is not injective. -/
theorem vinogradovCollisionWitnessSet_nonempty_iff
    {α : Type*} [DecidableEq α] {k : ℕ} (x : Fin k → α) :
    (vinogradovCollisionWitnessSet x).Nonempty ↔
      ¬Function.Injective x := by
  constructor
  · rintro ⟨w, hw⟩ hinjective
    have heq := (mem_vinogradovCollisionWitnessSet_iff x w).mp hw
    exact (ne_of_lt w.2) (hinjective heq)
  · intro hnot
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnot
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let w : VinogradovCollisionWitness k := ⟨(i, j), hlt⟩
      exact ⟨w,
        (mem_vinogradovCollisionWitnessSet_iff x w).mpr hij⟩
    · let w : VinogradovCollisionWitness k := ⟨(j, i), hgt⟩
      exact ⟨w,
        (mem_vinogradovCollisionWitnessSet_iff x w).mpr hij.symm⟩

/-- One collision witness in each selected block of a flattened tuple. -/
noncomputable def vinogradovMultiBlockCollisionWitnessSet
    (p k r b : ℕ) (x : Fin (b * k + r) → ZMod p) :
    Finset (Fin b → VinogradovCollisionWitness k) :=
  Finset.univ.filter fun w ↦
    ∀ q : Fin b,
      x (vinogradovSelectedBlockIndex k r b q (w q).1.1) =
        x (vinogradovSelectedBlockIndex k r b q (w q).1.2)

theorem mem_vinogradovMultiBlockCollisionWitnessSet_iff
    (p k r b : ℕ) (x : Fin (b * k + r) → ZMod p)
    (w : Fin b → VinogradovCollisionWitness k) :
    w ∈ vinogradovMultiBlockCollisionWitnessSet p k r b x ↔
      ∀ q : Fin b,
        x (vinogradovSelectedBlockIndex k r b q (w q).1.1) =
          x (vinogradovSelectedBlockIndex k r b q (w q).1.2) := by
  simp [vinogradovMultiBlockCollisionWitnessSet]

/-- A tuple admits a simultaneous collision choice exactly when every
selected block is singular. -/
theorem vinogradovMultiBlockCollisionWitnessSet_nonempty_iff
    (p k r b : ℕ) (x : Fin (b * k + r) → ZMod p) :
    (vinogradovMultiBlockCollisionWitnessSet p k r b x).Nonempty ↔
      VinogradovAllBlocksSingular p k r b x := by
  rw [allBlocksSingular_iff_forall_selectedBlock]
  constructor
  · rintro ⟨w, hw⟩ q
    have hcollision :=
      (mem_vinogradovMultiBlockCollisionWitnessSet_iff
        p k r b x w).mp hw q
    apply Function.not_injective_iff.mpr
    exact ⟨(w q).1.1, (w q).1.2, hcollision,
      ne_of_lt (w q).2⟩
  · intro hall
    have hwitness : ∀ q : Fin b,
        (vinogradovCollisionWitnessSet
          (fun i : Fin k ↦
            x (vinogradovSelectedBlockIndex k r b q i))).Nonempty := by
      intro q
      exact (vinogradovCollisionWitnessSet_nonempty_iff _).mpr (hall q)
    let w : Fin b → VinogradovCollisionWitness k := fun q ↦
      Classical.choose (hwitness q)
    refine ⟨w,
      (mem_vinogradovMultiBlockCollisionWitnessSet_iff
        p k r b x w).mpr ?_⟩
    intro q
    exact (mem_vinogradovCollisionWitnessSet_iff _ (w q)).mp
      (Classical.choose_spec (hwitness q))

end

end ZeroFreeRegion.VinogradovKorobov
