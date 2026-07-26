import ZeroFreeRegion.VinogradovKorobov.VinogradovRectangularJacobian
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance vinogradovLowDiversityPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- Residue tuples taking fewer than `d` distinct values. -/
noncomputable def vinogradovLowDiversityTupleSet
    (p s d : ℕ) [Fact p.Prime] : Finset (Fin s → ZMod p) :=
  Finset.univ.filter fun x ↦ (Finset.univ.image x).card < d

theorem mem_vinogradovLowDiversityTupleSet_iff
    (p s d : ℕ) [Fact p.Prime] (x : Fin s → ZMod p) :
    x ∈ vinogradovLowDiversityTupleSet p s d ↔
      (Finset.univ.image x).card < d := by
  simp [vinogradovLowDiversityTupleSet]

/-- Codes for a tuple with fewer than `d` values: `d-1` possible centers and
one center label for every coordinate. -/
def vinogradovLowDiversityTupleEncoder
    (p s d : ℕ) [Fact p.Prime]
    (code : (Fin (d - 1) → ZMod p) × (Fin s → Fin (d - 1))) :
    Fin s → ZMod p :=
  fun i ↦ code.1 (code.2 i)

/-- Every tuple using fewer than `d` residues has a center-label encoding. -/
theorem exists_vinogradovLowDiversityTupleCode
    (p s d : ℕ) [Fact p.Prime]
    {x : Fin s → ZMod p}
    (hx : x ∈ vinogradovLowDiversityTupleSet p s d) :
    ∃ code : (Fin (d - 1) → ZMod p) × (Fin s → Fin (d - 1)),
      vinogradovLowDiversityTupleEncoder p s d code = x := by
  classical
  let S : Finset (ZMod p) := Finset.univ.image x
  let m := S.card
  have hm : m < d := by
    exact (mem_vinogradovLowDiversityTupleSet_iff p s d x).mp hx
  have hmd : m ≤ d - 1 := Nat.le_pred_of_lt hm
  let e : S ≃ Fin m := S.equivFin
  let ι : Fin m ↪ Fin (d - 1) := Fin.castLEEmb hmd
  let centers : Fin (d - 1) → ZMod p :=
    Function.extend ι (fun j ↦ ((e.symm j : S) : ZMod p)) 0
  let labels : Fin s → Fin (d - 1) := fun i ↦
    ι (e ⟨x i, by
      change x i ∈ Finset.univ.image x
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  refine ⟨(centers, labels), ?_⟩
  funext i
  change centers (labels i) = x i
  rw [show centers (labels i) =
      ((e.symm (e ⟨x i, by
        change x i ∈ Finset.univ.image x
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) : S) : ZMod p) by
    exact ι.injective.extend_apply _ _ _]
  simp

/-- The center-label model gives a crude explicit count for all low-diversity
tuples. -/
theorem card_vinogradovLowDiversityTupleSet_le
    (p s d : ℕ) [Fact p.Prime] :
    (vinogradovLowDiversityTupleSet p s d).card ≤
      p ^ (d - 1) * (d - 1) ^ s := by
  classical
  let encode := vinogradovLowDiversityTupleEncoder p s d
  have hsubset : vinogradovLowDiversityTupleSet p s d ⊆
      Finset.univ.image encode := by
    intro x hx
    obtain ⟨code, hcode⟩ := exists_vinogradovLowDiversityTupleCode p s d hx
    exact Finset.mem_image.mpr ⟨code, Finset.mem_univ _, hcode⟩
  calc
    (vinogradovLowDiversityTupleSet p s d).card ≤
        (Finset.univ.image encode).card := Finset.card_le_card hsubset
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = p ^ (d - 1) * (d - 1) ^ s := by
      simp [Fintype.card_prod]

/-- If the value set has at least `d` elements, one can select `d` source
coordinates on which the tuple is injective. -/
theorem exists_injective_selection_of_le_card_image
    (p s d : ℕ) [Fact p.Prime] (x : Fin s → ZMod p)
    (hcard : d ≤ (Finset.univ.image x).card) :
    ∃ ι : Fin d ↪ Fin s, Function.Injective fun i ↦ x (ι i) := by
  classical
  let S : Finset (ZMod p) := Finset.univ.image x
  let toImage : Fin s → S := fun i ↦ ⟨x i, by
    change x i ∈ Finset.univ.image x
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hsurj : Function.Surjective toImage := by
    intro z
    rcases z with ⟨z, hz⟩
    change z ∈ Finset.univ.image x at hz
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i, rfl⟩
  have hcard' : Fintype.card (Fin d) ≤ Fintype.card S := by
    rw [Fintype.card_fin, Fintype.card_coe]
    simpa [S] using hcard
  obtain ⟨selected : Fin d ↪ S⟩ :=
    Function.Embedding.nonempty_of_card_le hcard'
  let sectionEmb : S ↪ Fin s :=
    ⟨Function.surjInv hsurj, Function.injective_surjInv hsurj⟩
  let ι : Fin d ↪ Fin s := selected.trans sectionEmb
  refine ⟨ι, ?_⟩
  intro a b hab
  apply selected.injective
  apply Subtype.ext
  have ha := congrArg Subtype.val (Function.surjInv_eq hsurj (selected a))
  have hb := congrArg Subtype.val (Function.surjInv_eq hsurj (selected b))
  exact ha.symm.trans (hab.trans hb)

/-- Having no injective `d`-coordinate selection is equivalent to taking
fewer than `d` distinct values. -/
theorem no_injective_selection_iff_mem_vinogradovLowDiversityTupleSet
    (p s d : ℕ) [Fact p.Prime] (x : Fin s → ZMod p) :
    (¬∃ ι : Fin d ↪ Fin s, Function.Injective fun i ↦ x (ι i)) ↔
      x ∈ vinogradovLowDiversityTupleSet p s d := by
  rw [mem_vinogradovLowDiversityTupleSet_iff]
  constructor
  · intro hnone
    exact Nat.lt_of_not_ge fun hcard ↦
      hnone (exists_injective_selection_of_le_card_image p s d x hcard)
  · intro hcard
    rintro ⟨ι, hι⟩
    have hle : d ≤ (Finset.univ.image x).card := by
      calc
        d = (Finset.univ.image fun i ↦ x (ι i)).card := by
          rw [Finset.card_image_of_injective _ hι]
          simp
        _ ≤ (Finset.univ.image x).card := by
          apply Finset.card_le_card
          intro z hz
          obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
          exact Finset.mem_image.mpr ⟨ι i, Finset.mem_univ _, rfl⟩
    exact (Nat.not_le_of_lt hcard) hle

end

end ZeroFreeRegion.VinogradovKorobov
