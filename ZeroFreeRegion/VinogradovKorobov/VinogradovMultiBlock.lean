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

/-- The recursive assertion that at least one of the selected length-`k`
blocks is nonsingular modulo `p`. -/
def VinogradovHasNonsingularBlock
    (p k r : ℕ) : (b : ℕ) → (Fin (b * k + r) → ZMod p) → Prop
  | 0, _ => False
  | b + 1, x =>
      let split := (vinogradovPrependBlockEquiv p k r b).symm x
      Function.Injective split.1 ∨
        VinogradovHasNonsingularBlock p k r b split.2

/-- Failing to be singular in every selected block is equivalent to having a
nonsingular selected block. -/
theorem not_allBlocksSingular_iff_hasNonsingularBlock
    (p k r b : ℕ) (x : Fin (b * k + r) → ZMod p) :
    ¬VinogradovAllBlocksSingular p k r b x ↔
      VinogradovHasNonsingularBlock p k r b x := by
  induction b with
  | zero =>
      simp [VinogradovAllBlocksSingular, VinogradovHasNonsingularBlock]
  | succ b ih =>
      simp only [VinogradovAllBlocksSingular,
        VinogradovHasNonsingularBlock, not_and_or]
      rw [ih]
      simp only [not_not]

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

/-- The complementary residue stratum in which at least one selected block is
nonsingular. -/
noncomputable def vinogradovSomeBlockNonsingularResidueSet
    (p k r b : ℕ) [Fact p.Prime] :
    Finset (Fin (b * k + r) → ZMod p) :=
  Finset.univ \ vinogradovMultiBlockSingularResidueSet p k r b

/-- Membership in the complementary finite set is exactly the existence of a
nonsingular selected block. -/
theorem mem_vinogradovSomeBlockNonsingularResidueSet_iff
    (p k r b : ℕ) [Fact p.Prime]
    (x : Fin (b * k + r) → ZMod p) :
    x ∈ vinogradovSomeBlockNonsingularResidueSet p k r b ↔
      VinogradovHasNonsingularBlock p k r b x := by
  simp [vinogradovSomeBlockNonsingularResidueSet,
    mem_vinogradovMultiBlockSingularResidueSet_iff,
    not_allBlocksSingular_iff_hasNonsingularBlock]

/-- The all-singular and some-nonsingular strata partition the full residue
space. -/
theorem card_allSingular_add_card_someNonsingular
    (p k r b : ℕ) [Fact p.Prime] :
    (vinogradovMultiBlockSingularResidueSet p k r b).card +
        (vinogradovSomeBlockNonsingularResidueSet p k r b).card =
      p ^ (b * k + r) := by
  classical
  rw [Nat.add_comm]
  calc
    (vinogradovSomeBlockNonsingularResidueSet p k r b).card +
          (vinogradovMultiBlockSingularResidueSet p k r b).card =
        (Finset.univ : Finset (Fin (b * k + r) → ZMod p)).card := by
      simpa [vinogradovSomeBlockNonsingularResidueSet] using
        Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ
            (vinogradovMultiBlockSingularResidueSet p k r b))
    _ = p ^ (b * k + r) := by
      simp [ZMod.card]

/-- Exact cardinality of the residue tuples having a nonsingular selected
block. -/
theorem card_vinogradovSomeBlockNonsingularResidueSet
    (p k r b : ℕ) [Fact p.Prime] :
    (vinogradovSomeBlockNonsingularResidueSet p k r b).card =
      p ^ (b * k + r) -
        (p ^ k - p.descFactorial k) ^ b * p ^ r := by
  have hpartition := card_allSingular_add_card_someNonsingular p k r b
  rw [card_vinogradovMultiBlockSingularResidueSet] at hpartition
  omega

/-- Reassociate a tuple into `q` initial blocks, one distinguished block, and
`a` later blocks together with the unrestricted tail. -/
private def vinogradovFirstNonsingularEquiv
    (p k r q a : ℕ) :
    ((Fin (q * k) → ZMod p) ×
        ((Fin k → ZMod p) × (Fin (a * k + r) → ZMod p))) ≃
      (Fin ((q + 1 + a) * k + r) → ZMod p) :=
  (Equiv.prodCongr (Equiv.refl _)
      (Fin.appendEquiv k (a * k + r))).trans
    ((Fin.appendEquiv (q * k) (k + (a * k + r))).trans
      ((finCongr (by
        simp only [Nat.add_mul, one_mul]
        omega)).piCongrLeft fun _ ↦ ZMod p))

/-- The distinguished block is the first nonsingular block: the preceding
`q` blocks are singular, while the remaining `a` blocks are unrestricted. -/
def VinogradovFirstNonsingularBlock
    (p k r q a : ℕ)
    (x : Fin ((q + 1 + a) * k + r) → ZMod p) : Prop :=
  let split := (vinogradovFirstNonsingularEquiv p k r q a).symm x
  VinogradovAllBlocksSingular p k 0 q split.1 ∧
    Function.Injective split.2.1

/-- The finite stratum in which the first nonsingular block occurs after
exactly `q` singular blocks, with `a` blocks remaining. -/
noncomputable def vinogradovFirstNonsingularResidueSet
    (p k r q a : ℕ) [Fact p.Prime] :
    Finset (Fin ((q + 1 + a) * k + r) → ZMod p) :=
  (((vinogradovMultiBlockSingularResidueSet p k 0 q).product
      ((vinogradovNonsingularResidueSet p k).product Finset.univ)).map
    (vinogradovFirstNonsingularEquiv p k r q a).toEmbedding)

/-- Membership in the finite first-nonsingular stratum has the intended block
interpretation. -/
theorem mem_vinogradovFirstNonsingularResidueSet_iff
    (p k r q a : ℕ) [Fact p.Prime]
    (x : Fin ((q + 1 + a) * k + r) → ZMod p) :
    x ∈ vinogradovFirstNonsingularResidueSet p k r q a ↔
      VinogradovFirstNonsingularBlock p k r q a x := by
  let e := vinogradovFirstNonsingularEquiv p k r q a
  let split := e.symm x
  have hesplit : e split = x := e.apply_symm_apply x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨z, hz, hzx⟩
    have hz_eq : z = split := by
      apply e.injective
      simpa [e, split] using hzx
    subst z
    have hparts := Finset.mem_product.mp hz
    have htail := Finset.mem_product.mp hparts.2
    exact ⟨(mem_vinogradovMultiBlockSingularResidueSet_iff
        p k 0 q split.1).mp hparts.1,
      by simpa [vinogradovNonsingularResidueSet] using htail.1⟩
  · intro hx
    have hx' :
        VinogradovAllBlocksSingular p k 0 q split.1 ∧
          Function.Injective split.2.1 := by
      simpa [VinogradovFirstNonsingularBlock, e, split] using hx
    apply Finset.mem_map.mpr
    refine ⟨split, ?_, hesplit⟩
    apply Finset.mem_product.mpr
    refine ⟨(mem_vinogradovMultiBlockSingularResidueSet_iff
      p k 0 q split.1).mpr hx'.1, ?_⟩
    apply Finset.mem_product.mpr
    exact ⟨by simpa [vinogradovNonsingularResidueSet] using hx'.2,
      Finset.mem_univ _⟩

/-- Exact size of a first-nonsingular stratum. -/
theorem card_vinogradovFirstNonsingularResidueSet
    (p k r q a : ℕ) [Fact p.Prime] :
    (vinogradovFirstNonsingularResidueSet p k r q a).card =
      (p ^ k - p.descFactorial k) ^ q *
        p.descFactorial k * p ^ (a * k + r) := by
  rw [vinogradovFirstNonsingularResidueSet, Finset.card_map]
  change
    ((vinogradovMultiBlockSingularResidueSet p k 0 q) ×ˢ
      ((vinogradovNonsingularResidueSet p k) ×ˢ
        (Finset.univ : Finset (Fin (a * k + r) → ZMod p)))).card = _
  rw [Finset.card_product, Finset.card_product,
    card_vinogradovMultiBlockSingularResidueSet,
    card_vinogradovNonsingularResidueSet]
  have htail :
      (Finset.univ : Finset (Fin (a * k + r) → ZMod p)).card =
        p ^ (a * k + r) := by
    simp [ZMod.card]
  rw [htail]
  simp only [pow_zero, mul_one]
  ac_rfl

/-- Tuples whose first selected block is already nonsingular. -/
noncomputable def vinogradovHeadNonsingularResidueSet
    (p k r b : ℕ) [Fact p.Prime] :
    Finset (Fin ((b + 1) * k + r) → ZMod p) :=
  ((vinogradovNonsingularResidueSet p k).product Finset.univ).map
    (vinogradovPrependBlockEquiv p k r b).toEmbedding

/-- Membership in the head stratum is exactly nonsingularity of the first
block. -/
theorem mem_vinogradovHeadNonsingularResidueSet_iff
    (p k r b : ℕ) [Fact p.Prime]
    (x : Fin ((b + 1) * k + r) → ZMod p) :
    x ∈ vinogradovHeadNonsingularResidueSet p k r b ↔
      Function.Injective
        ((vinogradovPrependBlockEquiv p k r b).symm x).1 := by
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
    simpa [vinogradovNonsingularResidueSet] using
      (Finset.mem_product.mp hz).1
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨split, ?_, hesplit⟩
    exact Finset.mem_product.mpr
      ⟨by simpa [vinogradovNonsingularResidueSet] using hx,
        Finset.mem_univ _⟩

/-- Tuples whose first block is singular but whose remaining selected blocks
contain a nonsingular block. -/
noncomputable def vinogradovSingularHeadNonsingularTailResidueSet
    (p k r b : ℕ) [Fact p.Prime] :
    Finset (Fin ((b + 1) * k + r) → ZMod p) :=
  ((vinogradovSingularResidueSet p k).product
      (vinogradovSomeBlockNonsingularResidueSet p k r b)).map
    (vinogradovPrependBlockEquiv p k r b).toEmbedding

/-- Membership in the recursive tail stratum records a singular head and a
nonsingular block later in the tuple. -/
theorem mem_vinogradovSingularHeadNonsingularTailResidueSet_iff
    (p k r b : ℕ) [Fact p.Prime]
    (x : Fin ((b + 1) * k + r) → ZMod p) :
    x ∈ vinogradovSingularHeadNonsingularTailResidueSet p k r b ↔
      ¬Function.Injective
          ((vinogradovPrependBlockEquiv p k r b).symm x).1 ∧
        VinogradovHasNonsingularBlock p k r b
          ((vinogradovPrependBlockEquiv p k r b).symm x).2 := by
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
    have hparts := Finset.mem_product.mp hz
    exact ⟨by simpa [vinogradovSingularResidueSet] using hparts.1,
      (mem_vinogradovSomeBlockNonsingularResidueSet_iff
        p k r b split.2).mp hparts.2⟩
  · rintro ⟨hhead, htail⟩
    apply Finset.mem_map.mpr
    refine ⟨split, ?_, hesplit⟩
    exact Finset.mem_product.mpr
      ⟨by simpa [vinogradovSingularResidueSet] using hhead,
        (mem_vinogradovSomeBlockNonsingularResidueSet_iff
          p k r b split.2).mpr htail⟩

/-- The head-nonsingular and singular-head/nonsingular-tail cases cannot
overlap. -/
theorem disjoint_headNonsingular_singularHeadNonsingularTail
    (p k r b : ℕ) [Fact p.Prime] :
    Disjoint (vinogradovHeadNonsingularResidueSet p k r b)
      (vinogradovSingularHeadNonsingularTailResidueSet p k r b) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact
    ((mem_vinogradovSingularHeadNonsingularTailResidueSet_iff
      p k r b x).mp hy).1
      ((mem_vinogradovHeadNonsingularResidueSet_iff p k r b x).mp hx)

/-- The two recursive cases cover exactly all tuples having a nonsingular
selected block. -/
theorem union_headNonsingular_singularHeadNonsingularTail_eq_someBlock
    (p k r b : ℕ) [Fact p.Prime] :
    vinogradovHeadNonsingularResidueSet p k r b ∪
        vinogradovSingularHeadNonsingularTailResidueSet p k r b =
      vinogradovSomeBlockNonsingularResidueSet p k r (b + 1) := by
  ext x
  rw [Finset.mem_union,
    mem_vinogradovHeadNonsingularResidueSet_iff,
    mem_vinogradovSingularHeadNonsingularTailResidueSet_iff,
    mem_vinogradovSomeBlockNonsingularResidueSet_iff]
  simp only [VinogradovHasNonsingularBlock]
  tauto

/-- Exact size of the head-nonsingular case. -/
theorem card_vinogradovHeadNonsingularResidueSet
    (p k r b : ℕ) [Fact p.Prime] :
    (vinogradovHeadNonsingularResidueSet p k r b).card =
      p.descFactorial k * p ^ (b * k + r) := by
  rw [vinogradovHeadNonsingularResidueSet, Finset.card_map]
  change
    ((vinogradovNonsingularResidueSet p k) ×ˢ
      (Finset.univ : Finset (Fin (b * k + r) → ZMod p))).card = _
  rw [Finset.card_product, card_vinogradovNonsingularResidueSet]
  congr 1
  simp [ZMod.card]

/-- Exact size of the singular-head case that still has a nonsingular block
in its tail. -/
theorem card_vinogradovSingularHeadNonsingularTailResidueSet
    (p k r b : ℕ) [Fact p.Prime] :
    (vinogradovSingularHeadNonsingularTailResidueSet p k r b).card =
      (p ^ k - p.descFactorial k) *
        (p ^ (b * k + r) -
          (p ^ k - p.descFactorial k) ^ b * p ^ r) := by
  rw [vinogradovSingularHeadNonsingularTailResidueSet, Finset.card_map]
  change
    ((vinogradovSingularResidueSet p k) ×ˢ
      (vinogradovSomeBlockNonsingularResidueSet p k r b)).card = _
  rw [Finset.card_product, card_vinogradovSingularResidueSet,
    card_vinogradovSomeBlockNonsingularResidueSet]

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
