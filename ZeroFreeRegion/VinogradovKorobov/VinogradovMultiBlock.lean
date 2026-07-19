import ZeroFreeRegion.VinogradovKorobov.VinogradovPrimePowerFiber

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance vinogradovMultiBlockPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Split a tuple into its first block of `k` coordinates and the remaining
`b` blocks together with the unrestricted tail. -/
private def vinogradovPrependBlockEquiv
    (p k r b : ℕ) :
    ((Fin k → ZMod p) × (Fin (b * k + r) → ZMod p)) ≃
      (Fin ((b + 1) * k + r) → ZMod p) :=
  (Fin.appendEquiv k (b * k + r)).trans
    ((finCongr (by
      simp only [Nat.add_mul, one_mul]
      ac_rfl)).piCongrLeft fun _ ↦ ZMod p)

/-- The recursive assertion that every one of `b` consecutive length-`k`
blocks is singular modulo `p`; the final `r` coordinates are unrestricted. -/
def VinogradovAllBlocksSingular
    (p k r : ℕ) : (b : ℕ) → (Fin (b * k + r) → ZMod p) → Prop
  | 0, _ => True
  | b + 1, x =>
      let split := (vinogradovPrependBlockEquiv p k r b).symm x
      ¬Function.Injective split.1 ∧
        VinogradovAllBlocksSingular p k r b split.2

/-- Residue tuples in which all `b` consecutive blocks of length `k` are
singular.  This is the finite combinatorial stratum that accumulates one
power-of-`p` saving for each block. -/
noncomputable def vinogradovMultiBlockSingularResidueSet
    (p k r : ℕ) [Fact p.Prime] :
    (b : ℕ) → Finset (Fin (b * k + r) → ZMod p)
  | 0 => Finset.univ
  | b + 1 =>
      ((vinogradovSingularResidueSet p k).product
          (vinogradovMultiBlockSingularResidueSet p k r b)).map
        (vinogradovPrependBlockEquiv p k r b).toEmbedding

/-- Membership in the recursively constructed finite set is exactly the
assertion that every selected block is singular. -/
theorem mem_vinogradovMultiBlockSingularResidueSet_iff
    (p k r b : ℕ) [Fact p.Prime]
    (x : Fin (b * k + r) → ZMod p) :
    x ∈ vinogradovMultiBlockSingularResidueSet p k r b ↔
      VinogradovAllBlocksSingular p k r b x := by
  induction b with
  | zero => simp [vinogradovMultiBlockSingularResidueSet,
      VinogradovAllBlocksSingular]
  | succ b ih =>
      let e := vinogradovPrependBlockEquiv p k r b
      let split := e.symm x
      have hesplit : e split = x := e.apply_symm_apply x
      constructor
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨z, hz, hzx⟩
        have hz_eq : z = split := by
          apply e.injective
          simpa [e, split] using hzx
        subst z
        have hhead : split.1 ∈ vinogradovSingularResidueSet p k :=
          (Finset.mem_product.mp hz).1
        have htail : split.2 ∈
            vinogradovMultiBlockSingularResidueSet p k r b :=
          (Finset.mem_product.mp hz).2
        simpa [VinogradovAllBlocksSingular, e, split,
          vinogradovSingularResidueSet] using
          And.intro hhead ((ih split.2).mp htail)
      · intro hx
        have hx' :
            ¬Function.Injective split.1 ∧
              VinogradovAllBlocksSingular p k r b split.2 := by
          simpa [VinogradovAllBlocksSingular, e, split] using hx
        apply Finset.mem_map.mpr
        refine ⟨split, ?_, hesplit⟩
        apply Finset.mem_product.mpr
        exact ⟨by simpa [vinogradovSingularResidueSet] using hx'.1,
          (ih split.2).mpr hx'.2⟩

/-- The exact number of tuples with `b` singular blocks is the `b`-th power
of the one-block singular count, times the unrestricted tail count. -/
theorem card_vinogradovMultiBlockSingularResidueSet
    (p k r b : ℕ) [Fact p.Prime] :
    (vinogradovMultiBlockSingularResidueSet p k r b).card =
      (p ^ k - p.descFactorial k) ^ b * p ^ r := by
  induction b with
  | zero =>
      simp [vinogradovMultiBlockSingularResidueSet,
        ZMod.card]
  | succ b ih =>
      rw [vinogradovMultiBlockSingularResidueSet, Finset.card_map]
      change
        ((vinogradovSingularResidueSet p k) ×ˢ
          (vinogradovMultiBlockSingularResidueSet p k r b)).card = _
      rw [Finset.card_product, card_vinogradovSingularResidueSet, ih, pow_succ]
      ac_rfl

/-- Applying the one-block collision bound independently in each block
accumulates one full power-of-`p` saving per singular block. -/
theorem card_vinogradovMultiBlockSingularResidueSet_le
    (p k r b : ℕ) [Fact p.Prime] :
    (vinogradovMultiBlockSingularResidueSet p k r b).card ≤
      (k ^ 2 * p ^ (k - 1)) ^ b * p ^ r := by
  rw [card_vinogradovMultiBlockSingularResidueSet]
  gcongr
  exact pow_sub_descFactorial_le_sq_mul_pow_pred p k
    (Fact.out : p.Prime).pos

/-- Residue-field Vinogradov solutions whose left tuple is singular in every
one of the selected `b` blocks. -/
noncomputable def vinogradovMultiBlockSingularSolutionSet
    (p d k r b : ℕ) [Fact p.Prime] :
    Finset
      ((Fin (b * k + r) → ZMod p) ×
        (Fin (b * k + r) → ZMod p)) := by
  classical
  exact
    ((vinogradovMultiBlockSingularResidueSet p k r b).product
        Finset.univ).filter fun xy ↦
      IsVinogradovResidueSolution p d (b * k + r) xy.1 xy.2

/-- Membership records both the accumulated singular-block condition and all
residue-field Vinogradov equations. -/
theorem mem_vinogradovMultiBlockSingularSolutionSet_iff
    (p d k r b : ℕ) [Fact p.Prime]
    (x y : Fin (b * k + r) → ZMod p) :
    (x, y) ∈ vinogradovMultiBlockSingularSolutionSet p d k r b ↔
      VinogradovAllBlocksSingular p k r b x ∧
        IsVinogradovResidueSolution p d (b * k + r) x y := by
  classical
  simp [vinogradovMultiBlockSingularSolutionSet,
    mem_vinogradovMultiBlockSingularResidueSet_iff]

/-- Imposing the Vinogradov equations can only decrease the number of pairs,
so the `b` independent one-power savings survive in the solution stratum. -/
theorem card_vinogradovMultiBlockSingularSolutionSet_le
    (p d k r b : ℕ) [Fact p.Prime] :
    (vinogradovMultiBlockSingularSolutionSet p d k r b).card ≤
      ((k ^ 2 * p ^ (k - 1)) ^ b * p ^ r) *
        p ^ (b * k + r) := by
  classical
  calc
    (vinogradovMultiBlockSingularSolutionSet p d k r b).card ≤
        ((vinogradovMultiBlockSingularResidueSet p k r b).product
          (Finset.univ :
            Finset (Fin (b * k + r) → ZMod p))).card := by
      unfold vinogradovMultiBlockSingularSolutionSet
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (vinogradovMultiBlockSingularResidueSet p k r b).card *
          p ^ (b * k + r) := by
      change
        ((vinogradovMultiBlockSingularResidueSet p k r b) ×ˢ
          (Finset.univ :
            Finset (Fin (b * k + r) → ZMod p))).card = _
      rw [Finset.card_product]
      congr 1
      simpa [Fintype.card_pi_const, ZMod.card] using
        (Finset.card_univ :
          (Finset.univ :
            Finset (Fin (b * k + r) → ZMod p)).card =
              Fintype.card (Fin (b * k + r) → ZMod p))
    _ ≤ ((k ^ 2 * p ^ (k - 1)) ^ b * p ^ r) *
          p ^ (b * k + r) :=
      Nat.mul_le_mul_right (p ^ (b * k + r))
        (card_vinogradovMultiBlockSingularResidueSet_le p k r b)

end

end ZeroFreeRegion.VinogradovKorobov
