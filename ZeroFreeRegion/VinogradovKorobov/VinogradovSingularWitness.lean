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

/-- The coordinate type remaining after deleting the larger coordinate in a
collision witness. -/
abbrev VinogradovCollisionReducedIndex {k : ℕ}
    (w : VinogradovCollisionWitness k) :=
  {i : Fin k // i ≠ w.1.2}

/-- A tuple satisfying one fixed collision is equivalent to a tuple indexed
by all coordinates except the duplicated larger coordinate. -/
def vinogradovCollisionFiberEquiv
    {α : Type*} {k : ℕ} (w : VinogradovCollisionWitness k) :
    {x : Fin k → α // x w.1.1 = x w.1.2} ≃
      (VinogradovCollisionReducedIndex w → α) where
  toFun x i := x.1 i.1
  invFun f :=
    ⟨fun i ↦ if h : i = w.1.2 then
        f ⟨w.1.1, ne_of_lt w.2⟩
      else f ⟨i, h⟩, by
      simp [ne_of_lt w.2]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = w.1.2
    · subst i
      simp [x.2]
    · simp [hi]
  right_inv f := by
    funext i
    simp [i.2]

theorem vinogradovCollisionFiberEquiv_apply
    {α : Type*} {k : ℕ} (w : VinogradovCollisionWitness k)
    (x : {x : Fin k → α // x w.1.1 = x w.1.2})
    (i : VinogradovCollisionReducedIndex w) :
    vinogradovCollisionFiberEquiv w x i = x.1 i.1 :=
  rfl

theorem vinogradovCollisionFiberEquiv_symm_apply
    {α : Type*} {k : ℕ} (w : VinogradovCollisionWitness k)
    (f : VinogradovCollisionReducedIndex w → α) (i : Fin k) :
    ((vinogradovCollisionFiberEquiv w).symm f).1 i =
      if h : i = w.1.2 then f ⟨w.1.1, ne_of_lt w.2⟩
      else f ⟨i, h⟩ :=
  rfl

/-- Deleting the duplicated larger coordinate leaves exactly `k - 1`
indices. -/
theorem card_vinogradovCollisionReducedIndex
    {k : ℕ} (w : VinogradovCollisionWitness k) :
    Fintype.card (VinogradovCollisionReducedIndex w) = k - 1 := by
  simpa [VinogradovCollisionReducedIndex] using
    (Fintype.card_subtype_compl
      (fun i : Fin k ↦ i = w.1.2))

/-- The type of tuples satisfying a fixed collision has the expected exact
cardinality. -/
theorem card_vinogradovCollisionFiber
    {α : Type*} [Fintype α] {k : ℕ}
    (w : VinogradovCollisionWitness k) :
    Fintype.card {x : Fin k → α // x w.1.1 = x w.1.2} =
      (Fintype.card α) ^ (k - 1) := by
  rw [Fintype.card_congr (vinogradovCollisionFiberEquiv w)]
  simp

/-- Reconstruct a complete tuple from its coordinates away from the duplicate
and forget the proof of the fixed collision. -/
def vinogradovCollisionFiberEmbedding
    {α : Type*} {k : ℕ} (w : VinogradovCollisionWitness k) :
    (VinogradovCollisionReducedIndex w → α) ↪ (Fin k → α) where
  toFun f := ((vinogradovCollisionFiberEquiv w).symm f).1
  inj' f g h := by
    apply (vinogradovCollisionFiberEquiv w).symm.injective
    apply Subtype.ext
    exact h

/-- Residue tuples satisfying one prescribed coordinate collision. -/
noncomputable def vinogradovFixedCollisionTupleSet
    (p : ℕ) [NeZero p] {k : ℕ} (w : VinogradovCollisionWitness k) :
    Finset (Fin k → ZMod p) :=
  (Finset.univ : Finset
    (VinogradovCollisionReducedIndex w → ZMod p)).map
      (vinogradovCollisionFiberEmbedding w)

theorem mem_vinogradovFixedCollisionTupleSet_iff
    (p : ℕ) [NeZero p] {k : ℕ} (w : VinogradovCollisionWitness k)
    (x : Fin k → ZMod p) :
    x ∈ vinogradovFixedCollisionTupleSet p w ↔
      x w.1.1 = x w.1.2 := by
  constructor
  · intro hx
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_map.mp hx
    exact ((vinogradovCollisionFiberEquiv w).symm f).2
  · intro hx
    let z : {x : Fin k → ZMod p // x w.1.1 = x w.1.2} := ⟨x, hx⟩
    let f := vinogradovCollisionFiberEquiv w z
    apply Finset.mem_map.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val
      ((vinogradovCollisionFiberEquiv w).symm_apply_apply z)

/-- A fixed collision removes exactly one free residue coordinate. -/
theorem card_vinogradovFixedCollisionTupleSet
    (p : ℕ) [NeZero p] {k : ℕ} (w : VinogradovCollisionWitness k) :
    (vinogradovFixedCollisionTupleSet p w).card = p ^ (k - 1) := by
  rw [vinogradovFixedCollisionTupleSet, Finset.card_map]
  simp

/-- The union of all fixed-collision residue fibers. -/
noncomputable def vinogradovFixedCollisionUnionSet
    (p k : ℕ) [NeZero p] : Finset (Fin k → ZMod p) :=
  (Finset.univ : Finset (VinogradovCollisionWitness k)).biUnion
    (vinogradovFixedCollisionTupleSet p)

theorem mem_vinogradovFixedCollisionUnionSet_iff
    (p k : ℕ) [NeZero p] (x : Fin k → ZMod p) :
    x ∈ vinogradovFixedCollisionUnionSet p k ↔
      ¬Function.Injective x := by
  constructor
  · intro hx
    obtain ⟨w, _hwuniv, hwx⟩ := Finset.mem_biUnion.mp hx
    apply (vinogradovCollisionWitnessSet_nonempty_iff x).mp
    refine ⟨w, ?_⟩
    exact (mem_vinogradovCollisionWitnessSet_iff x w).mpr
      ((mem_vinogradovFixedCollisionTupleSet_iff p w x).mp hwx)
  · intro hnot
    obtain ⟨w, hw⟩ :=
      (vinogradovCollisionWitnessSet_nonempty_iff x).mpr hnot
    apply Finset.mem_biUnion.mpr
    exact ⟨w, Finset.mem_univ w,
      (mem_vinogradovFixedCollisionTupleSet_iff p w x).mpr
        ((mem_vinogradovCollisionWitnessSet_iff x w).mp hw)⟩

/-- The collision-fiber union is exactly the existing singular residue set. -/
theorem vinogradovFixedCollisionUnionSet_eq_singular
    (p k : ℕ) [Fact p.Prime] :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    vinogradovFixedCollisionUnionSet p k =
      vinogradovSingularResidueSet p k := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ext x
  rw [mem_vinogradovFixedCollisionUnionSet_iff]
  simp [vinogradovSingularResidueSet]

/-- Summing the exact fixed-collision fiber sizes gives the explicit witness
cover bound. -/
theorem card_vinogradovFixedCollisionUnionSet_le
    (p k : ℕ) [NeZero p] :
    (vinogradovFixedCollisionUnionSet p k).card ≤
      Fintype.card (VinogradovCollisionWitness k) * p ^ (k - 1) := by
  calc
    (vinogradovFixedCollisionUnionSet p k).card ≤
        ∑ w : VinogradovCollisionWitness k,
          (vinogradovFixedCollisionTupleSet p w).card :=
      Finset.card_biUnion_le
    _ = ∑ _w : VinogradovCollisionWitness k, p ^ (k - 1) := by
      apply Finset.sum_congr rfl
      intro w _hw
      exact card_vinogradovFixedCollisionTupleSet p w
    _ = Fintype.card (VinogradovCollisionWitness k) * p ^ (k - 1) := by
      simp

end

end ZeroFreeRegion.VinogradovKorobov
