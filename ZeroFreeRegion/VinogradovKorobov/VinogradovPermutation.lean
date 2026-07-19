import ZeroFreeRegion.VinogradovKorobov.VinogradovMultiBlock
import Mathlib.Logic.Equiv.Fin.Rotate

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Reindexing the coordinates by a permutation preserves every integer power
sum. -/
theorem vinogradovPowerSumInt_comp_perm {k s : ℕ}
    (e : Equiv.Perm (Fin s)) (x : Fin s → ℤ) (j : Fin k) :
    vinogradovPowerSumInt (fun i ↦ x (e i)) j =
      vinogradovPowerSumInt x j := by
  unfold vinogradovPowerSumInt
  exact _root_.Equiv.sum_comp e (fun i ↦ x i ^ (j.val + 1))

/-- Simultaneously permuting both tuples preserves the integer Vinogradov
system. -/
theorem IsVinogradovSolutionInt.comp_perm {k s : ℕ}
    {x y : Fin s → ℤ} (h : IsVinogradovSolutionInt k s x y)
    (e : Equiv.Perm (Fin s)) :
    IsVinogradovSolutionInt k s (fun i ↦ x (e i)) (fun i ↦ y (e i)) := by
  intro j
  rw [vinogradovPowerSumInt_comp_perm,
    vinogradovPowerSumInt_comp_perm, h j]

theorem isVinogradovSolutionInt_comp_perm_iff {k s : ℕ}
    (e : Equiv.Perm (Fin s)) (x y : Fin s → ℤ) :
    IsVinogradovSolutionInt k s (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovSolutionInt k s x y := by
  constructor
  · intro h
    simpa using h.comp_perm e.symm
  · intro h
    exact h.comp_perm e

/-- Integer power sums are invariant under an arbitrary finite coordinate
equivalence. -/
theorem vinogradovPowerSumInt_comp_equiv {k s t : ℕ}
    (e : Fin s ≃ Fin t) (x : Fin t → ℤ) (j : Fin k) :
    vinogradovPowerSumInt (fun i ↦ x (e i)) j =
      vinogradovPowerSumInt x j := by
  unfold vinogradovPowerSumInt
  exact _root_.Equiv.sum_comp e (fun i ↦ x i ^ (j.val + 1))

theorem isVinogradovSolutionInt_comp_equiv_iff {k s t : ℕ}
    (e : Fin s ≃ Fin t) (x y : Fin t → ℤ) :
    IsVinogradovSolutionInt k s
        (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovSolutionInt k t x y := by
  constructor <;> intro h j
  · simpa only [vinogradovPowerSumInt_comp_equiv] using h j
  · simpa only [vinogradovPowerSumInt_comp_equiv] using h j

/-- Reindexing residue coordinates by a permutation preserves every residue
power sum. -/
theorem vinogradovResiduePowerSum_comp_perm {p d s : ℕ}
    (e : Equiv.Perm (Fin s)) (x : Fin s → ZMod p) (j : Fin d) :
    vinogradovResiduePowerSum p (fun i ↦ x (e i)) j =
      vinogradovResiduePowerSum p x j := by
  unfold vinogradovResiduePowerSum
  exact _root_.Equiv.sum_comp e (fun i ↦ x i ^ (j.val + 1))

/-- Simultaneously permuting both residue tuples preserves the residue-field
Vinogradov system. -/
theorem IsVinogradovResidueSolution.comp_perm {p d s : ℕ}
    {x y : Fin s → ZMod p} (h : IsVinogradovResidueSolution p d s x y)
    (e : Equiv.Perm (Fin s)) :
    IsVinogradovResidueSolution p d s
      (fun i ↦ x (e i)) (fun i ↦ y (e i)) := by
  intro j
  rw [vinogradovResiduePowerSum_comp_perm,
    vinogradovResiduePowerSum_comp_perm, h j]

theorem isVinogradovResidueSolution_comp_perm_iff {p d s : ℕ}
    (e : Equiv.Perm (Fin s)) (x y : Fin s → ZMod p) :
    IsVinogradovResidueSolution p d s
        (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovResidueSolution p d s x y := by
  constructor
  · intro h
    simpa using h.comp_perm e.symm
  · intro h
    exact h.comp_perm e

/-- Residue power sums are unchanged when the coordinate type is replaced by
an equivalent finite type. -/
theorem vinogradovResiduePowerSum_comp_equiv {p d s t : ℕ}
    (e : Fin s ≃ Fin t) (x : Fin t → ZMod p) (j : Fin d) :
    vinogradovResiduePowerSum p (fun i ↦ x (e i)) j =
      vinogradovResiduePowerSum p x j := by
  unfold vinogradovResiduePowerSum
  exact _root_.Equiv.sum_comp e (fun i ↦ x i ^ (j.val + 1))

/-- The residue Vinogradov system is invariant under an arbitrary finite
coordinate equivalence, including arithmetic reassociations of `Fin` sizes. -/
theorem isVinogradovResidueSolution_comp_equiv_iff {p d s t : ℕ}
    (e : Fin s ≃ Fin t) (x y : Fin t → ZMod p) :
    IsVinogradovResidueSolution p d s
        (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovResidueSolution p d t x y := by
  constructor <;> intro h j
  · simpa only [vinogradovResiduePowerSum_comp_equiv] using h j
  · simpa only [vinogradovResiduePowerSum_comp_equiv] using h j

/-- The bounded modular power sums are also invariant under coordinate
permutation. -/
theorem vinogradovPowerSumMod_comp_perm {Q k s X : ℕ}
    (e : Equiv.Perm (Fin s)) (x : Fin s → Fin X) (j : Fin k) :
    vinogradovPowerSumMod Q (fun i ↦ x (e i)) j =
      vinogradovPowerSumMod Q x j := by
  unfold vinogradovPowerSumMod
  exact _root_.Equiv.sum_comp e
    (fun i ↦ ((x i).val + 1 : ZMod Q) ^ (j.val + 1))

theorem IsVinogradovSolutionMod.comp_perm {Q k s X : ℕ}
    {x y : Fin s → Fin X} (h : IsVinogradovSolutionMod Q k s X x y)
    (e : Equiv.Perm (Fin s)) :
    IsVinogradovSolutionMod Q k s X
      (fun i ↦ x (e i)) (fun i ↦ y (e i)) := by
  intro j
  rw [vinogradovPowerSumMod_comp_perm,
    vinogradovPowerSumMod_comp_perm, h j]

theorem isVinogradovSolutionMod_comp_perm_iff {Q k s X : ℕ}
    (e : Equiv.Perm (Fin s)) (x y : Fin s → Fin X) :
    IsVinogradovSolutionMod Q k s X
        (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovSolutionMod Q k s X x y := by
  constructor
  · intro h
    simpa using h.comp_perm e.symm
  · intro h
    exact h.comp_perm e

/-- Bounded modular power sums are invariant under an arbitrary finite
coordinate equivalence. -/
theorem vinogradovPowerSumMod_comp_equiv {Q k s t X : ℕ}
    (e : Fin s ≃ Fin t) (x : Fin t → Fin X) (j : Fin k) :
    vinogradovPowerSumMod Q (fun i ↦ x (e i)) j =
      vinogradovPowerSumMod Q x j := by
  unfold vinogradovPowerSumMod
  exact _root_.Equiv.sum_comp e
    (fun i ↦ ((x i).val + 1 : ZMod Q) ^ (j.val + 1))

theorem isVinogradovSolutionMod_comp_equiv_iff {Q k s t X : ℕ}
    (e : Fin s ≃ Fin t) (x y : Fin t → Fin X) :
    IsVinogradovSolutionMod Q k s X
        (fun i ↦ x (e i)) (fun i ↦ y (e i)) ↔
      IsVinogradovSolutionMod Q k t X x y := by
  constructor <;> intro h j
  · simpa only [vinogradovPowerSumMod_comp_equiv] using h j
  · simpa only [vinogradovPowerSumMod_comp_equiv] using h j

/-- The cyclic coordinate permutation that moves block `q` to the front of a
tuple consisting of `q + 1 + a` length-`k` blocks and an `r`-coordinate tail. -/
def vinogradovBlockCycle (k r q a : ℕ) (hk : 0 < k) :
    Equiv.Perm (Fin ((q + 1 + a) * k + r)) :=
  finCycle ⟨q * k, by
    simp only [Nat.add_mul, one_mul]
    omega⟩

/-- The `i`-th coordinate of the first block in the full tuple. -/
def vinogradovHeadIndex (k r q a : ℕ) (hk : 0 < k) (i : Fin k) :
    Fin ((q + 1 + a) * k + r) :=
  ⟨i.val, by
    simp only [Nat.add_mul, one_mul]
    omega⟩

/-- The `i`-th coordinate of block `q` in the full tuple. -/
def vinogradovBlockIndex (k r q a : ℕ) (hk : 0 < k) (i : Fin k) :
    Fin ((q + 1 + a) * k + r) :=
  ⟨q * k + i.val, by
    simp only [Nat.add_mul, one_mul]
    omega⟩

/-- Cycling by `q*k` sends the new head coordinate to the corresponding old
coordinate in block `q`. -/
theorem vinogradovBlockCycle_headIndex
    (k r q a : ℕ) (hk : 0 < k) (i : Fin k) :
    vinogradovBlockCycle k r q a hk
        (vinogradovHeadIndex k r q a hk i) =
      vinogradovBlockIndex k r q a hk i := by
  apply Fin.ext
  simp only [vinogradovBlockCycle, vinogradovHeadIndex,
    vinogradovBlockIndex, finCycle_apply, Fin.add_def]
  rw [Nat.mod_eq_of_lt]
  · omega
  · simp only [Nat.add_mul, one_mul]
    omega

/-- Consequently, the moved tuple's head block is exactly its old block `q`. -/
theorem vinogradovBlockCycle_head_value
    {α : Type*} (k r q a : ℕ) (hk : 0 < k)
    (x : Fin ((q + 1 + a) * k + r) → α) (i : Fin k) :
    x (vinogradovBlockCycle k r q a hk
        (vinogradovHeadIndex k r q a hk i)) =
      x (vinogradovBlockIndex k r q a hk i) := by
  rw [vinogradovBlockCycle_headIndex]

/-- Moving any selected block to the head preserves the residue Vinogradov
system. -/
theorem isVinogradovResidueSolution_blockCycle_iff
    {p d : ℕ} (k r q a : ℕ) (hk : 0 < k)
    (x y : Fin ((q + 1 + a) * k + r) → ZMod p) :
    IsVinogradovResidueSolution p d ((q + 1 + a) * k + r)
        (fun i ↦ x (vinogradovBlockCycle k r q a hk i))
        (fun i ↦ y (vinogradovBlockCycle k r q a hk i)) ↔
      IsVinogradovResidueSolution p d ((q + 1 + a) * k + r) x y :=
  isVinogradovResidueSolution_comp_perm_iff
    (vinogradovBlockCycle k r q a hk) x y

/-- The distinguished component of the three-part first-nonsingular split is
the direct coordinate block beginning at `q*k`. -/
theorem vinogradovFirstNonsingularEquiv_selectedBlock
    {p : ℕ} (k r q a : ℕ) (hk : 0 < k)
    (x : Fin ((q + 1 + a) * k + r) → ZMod p) (i : Fin k) :
    ((vinogradovFirstNonsingularEquiv p k r q a).symm x).2.1 i =
      x (vinogradovBlockIndex k r q a hk i) := by
  let hsize : q * k + (k + (a * k + r)) =
      (q + 1 + a) * k + r := by
    simp only [Nat.add_mul, one_mul]
    omega
  let oldIndex : Fin ((q + 1 + a) * k + r) :=
    Fin.cast hsize
      (Fin.natAdd (q * k) (Fin.castAdd (a * k + r) i))
  have h := congrFun
    ((vinogradovFirstNonsingularEquiv p k r q a).apply_symm_apply x)
    oldIndex
  have hindex : oldIndex = vinogradovBlockIndex k r q a hk i := by
    apply Fin.ext
    rfl
  rw [← hindex]
  simpa [vinogradovFirstNonsingularEquiv, oldIndex, hsize] using h

/-- A tuple in the `q`-th first-nonsingular stratum has an injective direct
coordinate block at `q`. -/
theorem VinogradovFirstNonsingularBlock.selectedBlock_injective
    {p k r q a : ℕ}
    {x : Fin ((q + 1 + a) * k + r) → ZMod p}
    (h : VinogradovFirstNonsingularBlock p k r q a x)
    (hk : 0 < k) :
    Function.Injective fun i : Fin k ↦
      x (vinogradovBlockIndex k r q a hk i) := by
  let e := vinogradovFirstNonsingularEquiv p k r q a
  let split := e.symm x
  have hsplit : Function.Injective split.2.1 := by
    have hfull :
        VinogradovAllBlocksSingular p k 0 q split.1 ∧
          Function.Injective split.2.1 := by
      simpa [VinogradovFirstNonsingularBlock, e, split] using h
    exact hfull.2
  intro i j hij
  apply hsplit
  simpa [e, split, vinogradovFirstNonsingularEquiv_selectedBlock] using hij

/-- A first-nonsingular stratum is contained in the recursive stratum having
at least one nonsingular selected block. -/
theorem VinogradovFirstNonsingularBlock.hasNonsingularBlock
    {p k r q a : ℕ}
    {x : Fin ((q + 1 + a) * k + r) → ZMod p}
    (h : VinogradovFirstNonsingularBlock p k r q a x)
    (hk : 0 < k) :
    VinogradovHasNonsingularBlock p k r (q + 1 + a) x := by
  apply (hasNonsingularBlock_iff_exists_selectedBlock
    p k r (q + 1 + a) x).mpr
  let block : Fin (q + 1 + a) := ⟨q, by omega⟩
  refine ⟨block, ?_⟩
  have hinj := h.selectedBlock_injective hk
  intro i j hij
  apply hinj
  simpa [block, vinogradovSelectedBlockIndex,
    vinogradovBlockIndex] using hij

/-- After cycling block `q` to the front, the new head block is injective. -/
theorem VinogradovFirstNonsingularBlock.cycledHead_injective
    {p k r q a : ℕ}
    {x : Fin ((q + 1 + a) * k + r) → ZMod p}
    (h : VinogradovFirstNonsingularBlock p k r q a x)
    (hk : 0 < k) :
    Function.Injective fun i : Fin k ↦
      x (vinogradovBlockCycle k r q a hk
        (vinogradovHeadIndex k r q a hk i)) := by
  intro i j hij
  apply h.selectedBlock_injective hk
  simpa [vinogradovBlockCycle_head_value] using hij

/-- The selected-block cycle, with the tuple size reassociated as one
length-`k` head followed by all remaining coordinates. -/
def vinogradovCycledHeadTailEquiv
    (k r q a : ℕ) (hk : 0 < k) :
    Fin (k + (q * k + a * k + r)) ≃
      Fin ((q + 1 + a) * k + r) :=
  (finCongr (by
    simp only [Nat.add_mul, one_mul]
    omega)).trans (vinogradovBlockCycle k r q a hk)

/-- The head of the reassociated tuple is sent to the selected block by the
cycle. -/
theorem vinogradovCycledHeadTailEquiv_castAdd
    (k r q a : ℕ) (hk : 0 < k) (i : Fin k) :
    vinogradovCycledHeadTailEquiv k r q a hk
        (Fin.castAdd (q * k + a * k + r) i) =
      vinogradovBlockCycle k r q a hk
        (vinogradovHeadIndex k r q a hk i) := by
  unfold vinogradovCycledHeadTailEquiv
  apply congrArg (vinogradovBlockCycle k r q a hk)
  apply Fin.ext
  rfl

/-- A tuple after moving block `q` to the front and exposing the exact
`Fin (k + tail)` shape used by the Hensel lifting API. -/
def vinogradovCycledHeadTailTuple
    {α : Type*} (k r q a : ℕ) (hk : 0 < k)
    (x : Fin ((q + 1 + a) * k + r) → α) :
    Fin (k + (q * k + a * k + r)) → α :=
  fun i ↦ x (vinogradovCycledHeadTailEquiv k r q a hk i)

/-- The reassociated tuple's Hensel head is exactly the cycled selected
block. -/
theorem vinogradovCycledHeadTailTuple_castAdd
    {α : Type*} (k r q a : ℕ) (hk : 0 < k)
    (x : Fin ((q + 1 + a) * k + r) → α) (i : Fin k) :
    vinogradovCycledHeadTailTuple k r q a hk x
        (Fin.castAdd (q * k + a * k + r) i) =
      x (vinogradovBlockCycle k r q a hk
        (vinogradovHeadIndex k r q a hk i)) := by
  rw [vinogradovCycledHeadTailTuple,
    vinogradovCycledHeadTailEquiv_castAdd]

/-- Cycling and reassociating coordinates preserves the full residue
Vinogradov system. -/
theorem isVinogradovResidueSolution_cycledHeadTail_iff
    {p d : ℕ} (k r q a : ℕ) (hk : 0 < k)
    (x y : Fin ((q + 1 + a) * k + r) → ZMod p) :
    IsVinogradovResidueSolution p d (k + (q * k + a * k + r))
        (vinogradovCycledHeadTailTuple k r q a hk x)
        (vinogradovCycledHeadTailTuple k r q a hk y) ↔
      IsVinogradovResidueSolution p d ((q + 1 + a) * k + r) x y := by
  exact isVinogradovResidueSolution_comp_equiv_iff
    (vinogradovCycledHeadTailEquiv k r q a hk) x y

/-- The same selected-block cycle and reassociation preserves each bounded
modular Vinogradov system. -/
theorem isVinogradovSolutionMod_cycledHeadTail_iff
    (Q d X k r q a : ℕ) (hk : 0 < k)
    (x y : Fin ((q + 1 + a) * k + r) → Fin X) :
    IsVinogradovSolutionMod Q d (k + (q * k + a * k + r)) X
        (vinogradovCycledHeadTailTuple k r q a hk x)
        (vinogradovCycledHeadTailTuple k r q a hk y) ↔
      IsVinogradovSolutionMod Q d ((q + 1 + a) * k + r) X x y := by
  exact isVinogradovSolutionMod_comp_equiv_iff
    (vinogradovCycledHeadTailEquiv k r q a hk) x y

/-- A first-nonsingular stratum becomes an injective Hensel head after the
selected block is cycled and the tuple size is reassociated. -/
theorem VinogradovFirstNonsingularBlock.cycledHeadTail_injective
    {p k r q a : ℕ}
    {x : Fin ((q + 1 + a) * k + r) → ZMod p}
    (h : VinogradovFirstNonsingularBlock p k r q a x)
    (hk : 0 < k) :
    Function.Injective fun i : Fin k ↦
      vinogradovCycledHeadTailTuple k r q a hk x
        (Fin.castAdd (q * k + a * k + r) i) := by
  intro i j hij
  apply h.cycledHead_injective hk
  simpa only [vinogradovCycledHeadTailTuple_castAdd] using hij

end

end ZeroFreeRegion.VinogradovKorobov
