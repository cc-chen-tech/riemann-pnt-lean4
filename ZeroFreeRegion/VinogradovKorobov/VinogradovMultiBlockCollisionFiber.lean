import ZeroFreeRegion.VinogradovKorobov.VinogradovSingularWitness

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance vinogradovMultiBlockCollisionFiberPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- The larger coordinate selected for deletion in block `q`. -/
def vinogradovCollisionDeletedIndex
    (k r b : ℕ) (w : Fin b → VinogradovCollisionWitness k) (q : Fin b) :
    Fin (b * k + r) :=
  vinogradovSelectedBlockIndex k r b q (w q).1.2

/-- The smaller coordinate retained as the value of the deleted coordinate in
block `q`. -/
def vinogradovCollisionKeptIndex
    (k r b : ℕ) (w : Fin b → VinogradovCollisionWitness k) (q : Fin b) :
    Fin (b * k + r) :=
  vinogradovSelectedBlockIndex k r b q (w q).1.1

/-- Coordinates left after deleting the chosen larger coordinate in every
selected block. -/
abbrev VinogradovMultiBlockCollisionReducedIndex
    (k r b : ℕ) (w : Fin b → VinogradovCollisionWitness k) :=
  {i : Fin (b * k + r) //
    ¬ ∃ q : Fin b, vinogradovCollisionDeletedIndex k r b w q = i}

/-- A retained smaller collision coordinate, viewed in the globally reduced
index type. -/
def vinogradovCollisionKeptReducedIndex
    (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) (q : Fin b) :
    VinogradovMultiBlockCollisionReducedIndex k r b w :=
  ⟨vinogradovCollisionKeptIndex k r b w q, by
    rintro ⟨q', hq'⟩
    exact
      (vinogradovCollisionWitness_selected_left_ne_selected_right
        k r b hk w q q') hq'.symm⟩

/-- Reconstruct a complete tuple by copying each retained collision coordinate
into the corresponding deleted coordinate. -/
def vinogradovMultiBlockCollisionReconstruct
    {α : Type*} (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k)
    (f : VinogradovMultiBlockCollisionReducedIndex k r b w → α) :
    Fin (b * k + r) → α := fun i ↦
  if h : ∃ q : Fin b, vinogradovCollisionDeletedIndex k r b w q = i then
    f (vinogradovCollisionKeptReducedIndex k r b hk w (Classical.choose h))
  else
    f ⟨i, h⟩

theorem vinogradovMultiBlockCollisionReconstruct_deleted
    {α : Type*} (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k)
    (f : VinogradovMultiBlockCollisionReducedIndex k r b w → α)
    (q : Fin b) :
    vinogradovMultiBlockCollisionReconstruct k r b hk w f
        (vinogradovCollisionDeletedIndex k r b w q) =
      f (vinogradovCollisionKeptReducedIndex k r b hk w q) := by
  let h : ∃ q' : Fin b,
      vinogradovCollisionDeletedIndex k r b w q' =
        vinogradovCollisionDeletedIndex k r b w q := ⟨q, rfl⟩
  rw [vinogradovMultiBlockCollisionReconstruct]
  split
  next h' =>
    have hchoose := Classical.choose_spec h'
    have hq : Classical.choose h' = q := by
      apply vinogradovCollisionWitness_selected_right_injective k r b hk w
      exact hchoose
    rw [hq]
  next h' => exact (h' h).elim

theorem vinogradovMultiBlockCollisionReconstruct_kept
    {α : Type*} (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k)
    (f : VinogradovMultiBlockCollisionReducedIndex k r b w → α)
    (q : Fin b) :
    vinogradovMultiBlockCollisionReconstruct k r b hk w f
        (vinogradovCollisionKeptIndex k r b w q) =
      f (vinogradovCollisionKeptReducedIndex k r b hk w q) := by
  have hnot : ¬ ∃ q' : Fin b,
      vinogradovCollisionDeletedIndex k r b w q' =
        vinogradovCollisionKeptIndex k r b w q := by
    rintro ⟨q', hq'⟩
    exact
      (vinogradovCollisionWitness_selected_left_ne_selected_right
        k r b hk w q q') hq'.symm
  simp [vinogradovMultiBlockCollisionReconstruct, hnot,
    vinogradovCollisionKeptReducedIndex]

/-- Tuples satisfying all collisions prescribed by `w`. -/
abbrev VinogradovMultiBlockCollisionFiber
    (α : Type*) (k r b : ℕ)
    (w : Fin b → VinogradovCollisionWitness k) :=
  {x : Fin (b * k + r) → α //
    ∀ q : Fin b,
      x (vinogradovCollisionKeptIndex k r b w q) =
        x (vinogradovCollisionDeletedIndex k r b w q)}

/-- Fixing one collision in each block is exactly equivalent to deleting one
coordinate from each block. -/
def vinogradovMultiBlockCollisionFiberEquiv
    {α : Type*} (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) :
    VinogradovMultiBlockCollisionFiber α k r b w ≃
      (VinogradovMultiBlockCollisionReducedIndex k r b w → α) where
  toFun x i := x.1 i.1
  invFun f :=
    ⟨vinogradovMultiBlockCollisionReconstruct k r b hk w f, by
      intro q
      rw [vinogradovMultiBlockCollisionReconstruct_deleted]
      rw [vinogradovMultiBlockCollisionReconstruct_kept]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : ∃ q : Fin b,
        vinogradovCollisionDeletedIndex k r b w q = i
    · let q := Classical.choose hi
      have hqi : vinogradovCollisionDeletedIndex k r b w q = i :=
        Classical.choose_spec hi
      rw [← hqi]
      change vinogradovMultiBlockCollisionReconstruct k r b hk w
          (fun j ↦ x.1 j.1)
          (vinogradovCollisionDeletedIndex k r b w q) =
        x.1 (vinogradovCollisionDeletedIndex k r b w q)
      rw [vinogradovMultiBlockCollisionReconstruct_deleted]
      exact x.2 q
    · simp [vinogradovMultiBlockCollisionReconstruct, hi]
  right_inv f := by
    funext i
    simp [vinogradovMultiBlockCollisionReconstruct, i.2]

/-- The set of deleted coordinates has one element for every selected block. -/
theorem card_vinogradovMultiBlockCollisionDeletedIndex
    (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) :
    Fintype.card {i : Fin (b * k + r) //
        ∃ q : Fin b, vinogradovCollisionDeletedIndex k r b w q = i} = b := by
  let d : Fin b → Fin (b * k + r) :=
    vinogradovCollisionDeletedIndex k r b w
  have hd : Function.Injective d := by
    exact vinogradovCollisionWitness_selected_right_injective k r b hk w
  let e : {i : Fin (b * k + r) //
      ∃ q : Fin b, vinogradovCollisionDeletedIndex k r b w q = i} ≃
      Set.range d :=
    { toFun := fun i ↦ ⟨i.1, by
      obtain ⟨q, hq⟩ := i.2
      exact ⟨q, hq⟩⟩
      invFun := fun i ↦ ⟨i.1, by
      obtain ⟨q, hq⟩ := i.2
      exact ⟨q, hq⟩⟩
      left_inv := fun i ↦ rfl
      right_inv := fun i ↦ rfl }
  calc
    Fintype.card {i : Fin (b * k + r) //
        ∃ q : Fin b, vinogradovCollisionDeletedIndex k r b w q = i} =
        Fintype.card (Set.range d) := Fintype.card_congr e
    _ = Fintype.card (Fin b) := Set.card_range_of_injective hd
    _ = b := Fintype.card_fin b

/-- Deleting one chosen collision coordinate in every block leaves
`b * k + r - b` coordinates. -/
theorem card_vinogradovMultiBlockCollisionReducedIndex
    (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) :
    Fintype.card (VinogradovMultiBlockCollisionReducedIndex k r b w) =
      b * k + r - b := by
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin]
  rw [card_vinogradovMultiBlockCollisionDeletedIndex k r b hk w]

/-- The same reduced cardinality in block-normal form. -/
theorem card_vinogradovMultiBlockCollisionReducedIndex_block
    (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) :
    Fintype.card (VinogradovMultiBlockCollisionReducedIndex k r b w) =
      b * (k - 1) + r := by
  rw [card_vinogradovMultiBlockCollisionReducedIndex k r b hk w]
  have hk' : k = (k - 1) + 1 := by omega
  conv_lhs =>
    lhs
    rw [hk']
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- A fixed simultaneous collision fiber has exactly one fewer free
coordinate per selected block. -/
theorem card_vinogradovMultiBlockCollisionFiber
    {α : Type*} [Fintype α]
    (k r b : ℕ) (hk : 0 < k)
    (w : Fin b → VinogradovCollisionWitness k) :
    Fintype.card (VinogradovMultiBlockCollisionFiber α k r b w) =
      (Fintype.card α) ^ (b * (k - 1) + r) := by
  rw [Fintype.card_congr
    (vinogradovMultiBlockCollisionFiberEquiv k r b hk w)]
  simp [card_vinogradovMultiBlockCollisionReducedIndex_block k r b hk w]

end

end ZeroFreeRegion.VinogradovKorobov
