import ZeroFreeRegion.VinogradovKorobov.VinogradovPermutation
import ZeroFreeRegion.VinogradovKorobov.VinogradovSolutionLifting

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Precomposition by the selected-block cycle and head-tail reassociation is
an equivalence between tuple spaces. -/
def vinogradovCycledHeadTailFunctionEquiv
    {α : Type*} (k r q a : ℕ) (hk : 0 < k) :
    (Fin ((q + 1 + a) * k + r) → α) ≃
      (Fin (k + (q * k + a * k + r)) → α) :=
  Equiv.arrowCongr
    (vinogradovCycledHeadTailEquiv k r q a hk).symm
    (Equiv.refl α)

@[simp]
theorem vinogradovCycledHeadTailFunctionEquiv_apply
    {α : Type*} (k r q a : ℕ) (hk : 0 < k)
    (x : Fin ((q + 1 + a) * k + r) → α) :
    vinogradovCycledHeadTailFunctionEquiv k r q a hk x =
      vinogradovCycledHeadTailTuple k r q a hk x := by
  rfl

/-- The corresponding equivalence on ordered pairs of Vinogradov tuples. -/
def vinogradovCycledHeadTailPairEquiv
    {α : Type*} (k r q a : ℕ) (hk : 0 < k) :
    ((Fin ((q + 1 + a) * k + r) → α) ×
        (Fin ((q + 1 + a) * k + r) → α)) ≃
      ((Fin (k + (q * k + a * k + r)) → α) ×
        (Fin (k + (q * k + a * k + r)) → α)) :=
  Equiv.prodCongr
    (vinogradovCycledHeadTailFunctionEquiv k r q a hk)
    (vinogradovCycledHeadTailFunctionEquiv k r q a hk)

/-- Prime-power Vinogradov solutions whose left tuple lies in the `q`-th
first-nonsingular residue stratum. -/
noncomputable def vinogradovPrimePowerFirstNonsingularSolutionSet
    (p k r q a n : ℕ) [Fact p.Prime] :
    Finset
      ((Fin ((q + 1 + a) * k + r) → Fin (p ^ (n + 1))) ×
        (Fin ((q + 1 + a) * k + r) → Fin (p ^ (n + 1)))) := by
  classical
  exact
    (vinogradovSolutionPairSetMod
      (p ^ (n + 1)) k ((q + 1 + a) * k + r) (p ^ (n + 1))).filter
        fun xy ↦ VinogradovFirstNonsingularBlock p k r q a
          (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ZMod p))

/-- Membership records both the prime-power equations and the exact first
nonsingular residue stratum. -/
theorem mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff
    (p k r q a n : ℕ) [Fact p.Prime]
    (x y : Fin ((q + 1 + a) * k + r) → Fin (p ^ (n + 1))) :
    (x, y) ∈ vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a n ↔
      VinogradovFirstNonsingularBlock p k r q a
          (fun i ↦ (((x i).val + 1 : ℕ) : ZMod p)) ∧
        IsVinogradovSolutionMod (p ^ (n + 1)) k
          ((q + 1 + a) * k + r) (p ^ (n + 1)) x y := by
  classical
  simp [vinogradovPrimePowerFirstNonsingularSolutionSet,
    mem_vinogradovSolutionPairSetMod_iff, and_comm]

/-- Cycling a first-nonsingular prime-power solution puts it in the standard
Hensel solution set with a nonsingular head. -/
theorem vinogradovCycledHeadTailPairEquiv_mem_nonsingular
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k)
    {xy :
      (Fin ((q + 1 + a) * k + r) → Fin (p ^ (n + 1))) ×
        (Fin ((q + 1 + a) * k + r) → Fin (p ^ (n + 1)))}
    (hxy : xy ∈
      vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a n) :
    vinogradovCycledHeadTailPairEquiv k r q a hk xy ∈
      vinogradovPrimePowerNonsingularSolutionSet p k
        (q * k + a * k + r) n := by
  have hmem :=
    (mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff
      p k r q a n xy.1 xy.2).mp hxy
  rw [mem_vinogradovPrimePowerNonsingularSolutionSet_iff]
  constructor
  · have hinj := hmem.1.cycledHeadTail_injective hk
    simpa [vinogradovCycledHeadTailPairEquiv,
      vinogradovCycledHeadTailFunctionEquiv] using hinj
  · exact (isVinogradovSolutionMod_cycledHeadTail_iff
      (p ^ (n + 1)) k (p ^ (n + 1)) k r q a hk xy.1 xy.2).mpr hmem.2

/-- Every first-nonsingular stratum injects into the standard nonsingular
head-block solution set at the same prime-power level. -/
theorem card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_nonsingular
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a n).card ≤
      (vinogradovPrimePowerNonsingularSolutionSet p k
        (q * k + a * k + r) n).card := by
  classical
  let e := vinogradovCycledHeadTailPairEquiv
    (α := Fin (p ^ (n + 1))) k r q a hk
  let source := vinogradovPrimePowerFirstNonsingularSolutionSet
    p k r q a n
  have hsubset : source.map e.toEmbedding ⊆
      vinogradovPrimePowerNonsingularSolutionSet p k
        (q * k + a * k + r) n := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨xy, hxy, rfl⟩ := hz
    exact vinogradovCycledHeadTailPairEquiv_mem_nonsingular
      p k r q a n hk hxy
  calc
    source.card = (source.map e.toEmbedding).card := by simp
    _ ≤ (vinogradovPrimePowerNonsingularSolutionSet p k
          (q * k + a * k + r) n).card :=
      Finset.card_le_card hsubset

/-- Explicit iterated Hensel bound for each first-nonsingular block stratum. -/
theorem card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_iterated
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a n).card ≤
      p ^ (2 * (k + (q * k + a * k + r)) +
        (k + 2 * (q * k + a * k + r)) * n) := by
  exact (card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_nonsingular
    p k r q a n hk).trans
      (card_vinogradovPrimePowerNonsingularSolutionSet_le_iterated
        p k (q * k + a * k + r) n hkp)

end

end ZeroFreeRegion.VinogradovKorobov
