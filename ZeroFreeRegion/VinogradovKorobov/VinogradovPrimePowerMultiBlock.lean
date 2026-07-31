import ZeroFreeRegion.VinogradovKorobov.VinogradovFirstStratumLifting

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance vinogradovPrimePowerMultiBlockPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Prime-power tuple pairs whose left tuple is singular modulo `p` in every
one of the selected `b` blocks.  No Vinogradov equations are imposed. -/
noncomputable def vinogradovPrimePowerMultiBlockSingularAmbientSet
    (p k r b n : ℕ) [Fact p.Prime] :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) := by
  classical
  exact Finset.univ.filter fun xy ↦
    VinogradovAllBlocksSingular p k r b
      (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p))

/-- Membership in the ambient set is exactly the recursive all-singular
condition on the left tuple reduced modulo `p`. -/
theorem mem_vinogradovPrimePowerMultiBlockSingularAmbientSet_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n ↔
      VinogradovAllBlocksSingular p k r b
        (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) := by
  classical
  simp [vinogradovPrimePowerMultiBlockSingularAmbientSet]

/-- Complete one-based residue encoding for a pair whose tuple length is
written as `0 + (b*k+r)` by the generic prime-power lifting API. -/
noncomputable def vinogradovPrimePowerMultiBlockBaseZeroEquiv
    (p k r b : ℕ) [Fact p.Prime] :
    vinogradovPrimePowerBasePair p 0 (b * k + r) 0 ≃
      ((Fin (b * k + r) → ZMod p) ×
        (Fin (b * k + r) → ZMod p)) :=
  (Equiv.prodCongr
      (Equiv.arrowCongr (finCongr (Nat.zero_add (b * k + r)))
        (Equiv.refl _))
      (Equiv.arrowCongr (finCongr (Nat.zero_add (b * k + r)))
        (Equiv.refl _))).trans
    (vinogradovFirstStratumCompleteResiduePairEquiv p (b * k + r))

/-- At the first prime level, the all-singular ambient set has the exact
product cardinality of the residue-field all-singular left stratum and an
unrestricted right tuple. -/
theorem card_vinogradovPrimePowerMultiBlockSingularAmbientSet_zero
    (p k r b : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b 0).card =
      (p ^ k - p.descFactorial k) ^ b * p ^ r *
        p ^ (b * k + r) := by
  classical
  let e := vinogradovPrimePowerMultiBlockBaseZeroEquiv p k r b
  let target :=
    (vinogradovMultiBlockSingularResidueSet p k r b).product
      (Finset.univ : Finset (Fin (b * k + r) → ZMod p))
  have hcard :
      (vinogradovPrimePowerMultiBlockSingularAmbientSet
        p k r b 0).card = target.card := by
    apply Finset.card_equiv e
    intro xy
    have hxencode : (e xy).1 =
        (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) := by
      funext i
      simpa [e, vinogradovPrimePowerMultiBlockBaseZeroEquiv,
        vinogradovFirstStratumCompleteResiduePairEquiv,
        vinogradovFirstStratumCompleteResidueEquiv_apply]
    rw [mem_vinogradovPrimePowerMultiBlockSingularAmbientSet_iff]
    constructor
    · intro hsing
      apply Finset.mem_product.mpr
      constructor
      · apply
          (mem_vinogradovMultiBlockSingularResidueSet_iff
            p k r b (e xy).1).mpr
        rw [hxencode]
        exact hsing
      · simp
    · intro htarget
      have hsing :=
        (mem_vinogradovMultiBlockSingularResidueSet_iff
          p k r b (e xy).1).mp (Finset.mem_product.mp htarget).1
      rw [hxencode] at hsing
      exact hsing
  calc
    (vinogradovPrimePowerMultiBlockSingularAmbientSet
        p k r b 0).card = target.card := hcard
    _ = (p ^ k - p.descFactorial k) ^ b * p ^ r *
        p ^ (b * k + r) := by
      calc
        ((vinogradovMultiBlockSingularResidueSet p k r b).product
            (Finset.univ : Finset (Fin (b * k + r) → ZMod p))).card =
            (vinogradovMultiBlockSingularResidueSet p k r b).card *
              (Finset.univ :
                Finset (Fin (b * k + r) → ZMod p)).card :=
          Finset.card_product _ _
        _ = (p ^ k - p.descFactorial k) ^ b * p ^ r *
            p ^ (b * k + r) := by
          rw [card_vinogradovMultiBlockSingularResidueSet]
          congr 1
          simp [ZMod.card]

/-- Every left coordinate has the same residue modulo `p` after one
unrestricted digit lift, so the full recursive block-singularity predicate is
unchanged. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_allBlocksSingular_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n)
    (z : vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :
    VinogradovAllBlocksSingular p k r b
        (fun i ↦
          (((((vinogradovPrimePowerLiftAmbientEquiv p 0
            (b * k + r) n ⟨xy, z⟩).1
              (Fin.natAdd 0 i)).val + 1 : ℕ)) : ZMod p)) ↔
      VinogradovAllBlocksSingular p k r b
        (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) := by
  have hfun :
      (fun i ↦
        (((((vinogradovPrimePowerLiftAmbientEquiv p 0
          (b * k + r) n ⟨xy, z⟩).1
            (Fin.natAdd 0 i)).val + 1 : ℕ)) : ZMod p)) =
        (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) := by
    funext i
    exact vinogradovPrimePowerLiftAmbientEquiv_fst_mod
      p 0 (b * k + r) n xy z (Fin.natAdd 0 i)
  rw [hfun]

/-- An all-singular base pair together with arbitrary next residue digits. -/
noncomputable def vinogradovPrimePowerMultiBlockSingularAmbientLiftSet
    (p k r b n : ℕ) [Fact p.Prime] :
    Finset
      (Σ _ : vinogradovPrimePowerBasePair p 0 (b * k + r) n,
        vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) := by
  classical
  exact
    (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n).sigma
      fun _ ↦ Finset.univ

/-- The unrestricted correction space contributes one new residue digit for
each coordinate of both tuples. -/
theorem card_vinogradovPrimePowerMultiBlockSingularAmbientLiftSet
    (p k r b n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerMultiBlockSingularAmbientLiftSet
      p k r b n).card =
      (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n).card *
        p ^ (2 * (b * k + r)) := by
  classical
  rw [vinogradovPrimePowerMultiBlockSingularAmbientLiftSet,
    Finset.card_sigma]
  simp only [Finset.card_univ, Finset.sum_const_nat]
  rw [card_vinogradovPrimePowerSplitCorrection]
  simp only [Nat.zero_add]

/-- Membership in the all-singular lift set is transported exactly to the
all-singular ambient set at the next prime-power level. -/
theorem mem_vinogradovPrimePowerMultiBlockSingularAmbientLiftSet_iff_image_mem
    (p k r b n : ℕ) [Fact p.Prime]
    (w : Σ _ : vinogradovPrimePowerBasePair p 0 (b * k + r) n,
      vinogradovPrimePowerSplitCorrection p 0 (b * k + r)) :
    w ∈ vinogradovPrimePowerMultiBlockSingularAmbientLiftSet
        p k r b n ↔
      vinogradovPrimePowerLiftAmbientEquiv p 0 (b * k + r) n w ∈
        vinogradovPrimePowerMultiBlockSingularAmbientSet
          p k r b (n + 1) := by
  rcases w with ⟨xy, z⟩
  simp only [vinogradovPrimePowerMultiBlockSingularAmbientLiftSet,
    Finset.mem_sigma, Finset.mem_univ, and_true]
  rw [mem_vinogradovPrimePowerMultiBlockSingularAmbientSet_iff,
    mem_vinogradovPrimePowerMultiBlockSingularAmbientSet_iff]
  exact
    (vinogradovPrimePowerLiftAmbientEquiv_allBlocksSingular_iff
      p k r b n xy z).symm

/-- Mapping the complete lift set through the digit equivalence gives exactly
the next-level all-singular ambient set. -/
theorem map_vinogradovPrimePowerMultiBlockSingularAmbientLiftSet_eq
    (p k r b n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerMultiBlockSingularAmbientLiftSet
      p k r b n).map
        (vinogradovPrimePowerLiftAmbientEquiv p 0
          (b * k + r) n).toEmbedding =
      vinogradovPrimePowerMultiBlockSingularAmbientSet
        p k r b (n + 1) := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact
      (mem_vinogradovPrimePowerMultiBlockSingularAmbientLiftSet_iff_image_mem
        p k r b n w).mp hw
  · intro hv
    let e := vinogradovPrimePowerLiftAmbientEquiv p 0 (b * k + r) n
    let w := e.symm v
    have hew : e w = v := e.apply_symm_apply v
    apply Finset.mem_map.mpr
    refine ⟨w, ?_, hew⟩
    apply
      (mem_vinogradovPrimePowerMultiBlockSingularAmbientLiftSet_iff_image_mem
        p k r b n w).mpr
    simpa [e, w] using hv

/-- Exact one-step recurrence for the all-singular ambient count. -/
theorem card_vinogradovPrimePowerMultiBlockSingularAmbientSet_succ
    (p k r b n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerMultiBlockSingularAmbientSet
      p k r b (n + 1)).card =
      (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n).card *
        p ^ (2 * (b * k + r)) := by
  rw [← map_vinogradovPrimePowerMultiBlockSingularAmbientLiftSet_eq
      p k r b n,
    Finset.card_map,
    card_vinogradovPrimePowerMultiBlockSingularAmbientLiftSet]

/-- Iterating the exact recurrence reduces every level to the first prime
level. -/
theorem card_vinogradovPrimePowerMultiBlockSingularAmbientSet_eq_base_mul_pow
    (p k r b n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n).card =
      (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b 0).card *
        (p ^ (2 * (b * k + r))) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [card_vinogradovPrimePowerMultiBlockSingularAmbientSet_succ,
        ih, pow_succ, mul_assoc]

/-- Exact all-singular ambient count at every prime-power level.  The factor
`(p^k-p.descFactorial k)^b` retains one singular-block saving for every
selected block. -/
theorem card_vinogradovPrimePowerMultiBlockSingularAmbientSet
    (p k r b n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n).card =
      ((p ^ k - p.descFactorial k) ^ b * p ^ r *
          p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n := by
  rw [card_vinogradovPrimePowerMultiBlockSingularAmbientSet_eq_base_mul_pow,
    card_vinogradovPrimePowerMultiBlockSingularAmbientSet_zero]

/-- Prime-power Vinogradov solutions in the all-blocks-singular stratum. -/
noncomputable def vinogradovPrimePowerMultiBlockSingularSolutionSet
    (p k r b n : ℕ) [Fact p.Prime] :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) := by
  classical
  exact
    (vinogradovPrimePowerMultiBlockSingularAmbientSet p k r b n).filter
      fun xy ↦
        IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
          (p ^ (n + 1))
          (fun i ↦ xy.1 (Fin.natAdd 0 i))
          (fun i ↦ xy.2 (Fin.natAdd 0 i))

/-- Membership records both all-block singularity and the complete modular
Vinogradov system. -/
theorem mem_vinogradovPrimePowerMultiBlockSingularSolutionSet_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerMultiBlockSingularSolutionSet p k r b n ↔
      VinogradovAllBlocksSingular p k r b
          (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) ∧
        IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
          (p ^ (n + 1))
          (fun i ↦ xy.1 (Fin.natAdd 0 i))
          (fun i ↦ xy.2 (Fin.natAdd 0 i)) := by
  classical
  simp [vinogradovPrimePowerMultiBlockSingularSolutionSet,
    mem_vinogradovPrimePowerMultiBlockSingularAmbientSet_iff]

/-- Imposing the Vinogradov equations only shrinks the exact all-singular
ambient stratum. -/
theorem card_vinogradovPrimePowerMultiBlockSingularSolutionSet_le
    (p k r b n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerMultiBlockSingularSolutionSet p k r b n).card ≤
      ((p ^ k - p.descFactorial k) ^ b * p ^ r *
          p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n := by
  calc
    (vinogradovPrimePowerMultiBlockSingularSolutionSet
        p k r b n).card ≤
        (vinogradovPrimePowerMultiBlockSingularAmbientSet
          p k r b n).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = ((p ^ k - p.descFactorial k) ^ b * p ^ r *
          p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n :=
      card_vinogradovPrimePowerMultiBlockSingularAmbientSet
        p k r b n

/-- Remove the harmless `0 + s` tuple-length presentation introduced by the
generic digit-lifting API. -/
def vinogradovPrimePowerCommonPairEquiv
    (p s n : ℕ) [Fact p.Prime] :
    vinogradovPrimePowerBasePair p 0 s n ≃
      ((Fin s → Fin (p ^ (n + 1))) ×
        (Fin s → Fin (p ^ (n + 1)))) :=
  Equiv.prodCongr
    (Equiv.arrowCongr (finCongr (Nat.zero_add s)) (Equiv.refl _))
    (Equiv.arrowCongr (finCongr (Nat.zero_add s)) (Equiv.refl _))

/-- All degree-`k` Vinogradov solutions modulo `p^(n+1)`, expressed in the
common pair type used by the multiblock digit lift. -/
noncomputable def vinogradovPrimePowerCompleteSolutionSet
    (p k r b n : ℕ) [Fact p.Prime] :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) := by
  classical
  exact Finset.univ.filter fun xy ↦
    IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
      (p ^ (n + 1))
      (fun i ↦ xy.1 (Fin.natAdd 0 i))
      (fun i ↦ xy.2 (Fin.natAdd 0 i))

/-- Membership in the complete set is precisely the modular Vinogradov
system in the ordinary `Fin (b*k+r)` coordinate presentation. -/
theorem mem_vinogradovPrimePowerCompleteSolutionSet_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerCompleteSolutionSet p k r b n ↔
      IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
        (p ^ (n + 1))
        (fun i ↦ xy.1 (Fin.natAdd 0 i))
        (fun i ↦ xy.2 (Fin.natAdd 0 i)) := by
  classical
  simp [vinogradovPrimePowerCompleteSolutionSet]

/-- The complete prime-power solution set has the cardinality used by the
finite Vinogradov moment identity. -/
theorem card_vinogradovPrimePowerCompleteSolutionSet
    (p k r b n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerCompleteSolutionSet p k r b n).card =
      vinogradovSolutionCountMod (p ^ (n + 1)) k (b * k + r)
        (p ^ (n + 1)) := by
  classical
  let e := vinogradovPrimePowerCommonPairEquiv p (b * k + r) n
  have hcard :
      (vinogradovPrimePowerCompleteSolutionSet p k r b n).card =
        (vinogradovSolutionPairSetMod (p ^ (n + 1)) k
          (b * k + r) (p ^ (n + 1))).card := by
    apply Finset.card_equiv e
    intro xy
    rw [mem_vinogradovPrimePowerCompleteSolutionSet_iff,
      mem_vinogradovSolutionPairSetMod_iff]
    have hx : (e xy).1 = fun i ↦ xy.1 (Fin.natAdd 0 i) := by
      funext i
      simpa [e, vinogradovPrimePowerCommonPairEquiv]
    have hy : (e xy).2 = fun i ↦ xy.2 (Fin.natAdd 0 i) := by
      funext i
      simpa [e, vinogradovPrimePowerCommonPairEquiv]
    rw [hx, hy]
  rw [hcard, card_vinogradovSolutionPairSetMod]

/-- Prime-power Vinogradov solutions whose left tuple has at least one
nonsingular selected block modulo `p`. -/
noncomputable def vinogradovPrimePowerSomeBlockNonsingularSolutionSet
    (p k r b n : ℕ) [Fact p.Prime] :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) := by
  classical
  exact (vinogradovPrimePowerCompleteSolutionSet p k r b n).filter fun xy ↦
    VinogradovHasNonsingularBlock p k r b
      (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p))

/-- Membership in the complementary solution stratum records both the
nonsingular-block witness and the Vinogradov equations. -/
theorem mem_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_iff
    (p k r b n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerSomeBlockNonsingularSolutionSet
        p k r b n ↔
      VinogradovHasNonsingularBlock p k r b
          (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) ∧
        IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
          (p ^ (n + 1))
          (fun i ↦ xy.1 (Fin.natAdd 0 i))
          (fun i ↦ xy.2 (Fin.natAdd 0 i)) := by
  classical
  simp [vinogradovPrimePowerSomeBlockNonsingularSolutionSet,
    mem_vinogradovPrimePowerCompleteSolutionSet_iff, and_comm]

/-- The all-singular and some-nonsingular prime-power solution strata are
disjoint. -/
theorem disjoint_primePowerMultiBlockSingular_someNonsingular
    (p k r b n : ℕ) [Fact p.Prime] :
    Disjoint
      (vinogradovPrimePowerMultiBlockSingularSolutionSet p k r b n)
      (vinogradovPrimePowerSomeBlockNonsingularSolutionSet p k r b n) := by
  rw [Finset.disjoint_left]
  intro xy hsing hsome
  have hall :=
    (mem_vinogradovPrimePowerMultiBlockSingularSolutionSet_iff
      p k r b n xy).mp hsing |>.1
  have hhas :=
    (mem_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_iff
      p k r b n xy).mp hsome |>.1
  exact (not_allBlocksSingular_iff_hasNonsingularBlock
    p k r b _).mpr hhas hall

/-- The two block strata partition the complete prime-power solution set. -/
theorem union_primePowerMultiBlockSingular_someNonsingular_eq_complete
    (p k r b n : ℕ) [Fact p.Prime] :
    vinogradovPrimePowerMultiBlockSingularSolutionSet p k r b n ∪
        vinogradovPrimePowerSomeBlockNonsingularSolutionSet p k r b n =
      vinogradovPrimePowerCompleteSolutionSet p k r b n := by
  classical
  ext xy
  rw [Finset.mem_union,
    mem_vinogradovPrimePowerMultiBlockSingularSolutionSet_iff,
    mem_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_iff,
    mem_vinogradovPrimePowerCompleteSolutionSet_iff]
  constructor
  · rintro (h | h)
    · exact h.2
    · exact h.2
  · intro hsolution
    by_cases hall : VinogradovAllBlocksSingular p k r b
        (fun i ↦
          (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p))
    · exact Or.inl ⟨hall, hsolution⟩
    · exact Or.inr
        ⟨(not_allBlocksSingular_iff_hasNonsingularBlock
          p k r b _).mp hall, hsolution⟩

/-- Exact prime-power decomposition of the complete modular solution count
into the all-singular and some-nonsingular branches. -/
theorem card_primePowerMultiBlockSingular_add_someNonsingular
    (p k r b n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerMultiBlockSingularSolutionSet p k r b n).card +
        (vinogradovPrimePowerSomeBlockNonsingularSolutionSet
          p k r b n).card =
      vinogradovSolutionCountMod (p ^ (n + 1)) k (b * k + r)
        (p ^ (n + 1)) := by
  have hcard := Finset.card_union_of_disjoint
    (disjoint_primePowerMultiBlockSingular_someNonsingular
      p k r b n)
  rw [union_primePowerMultiBlockSingular_someNonsingular_eq_complete,
    card_vinogradovPrimePowerCompleteSolutionSet] at hcard
  exact hcard.symm

/-- Reassociate the `q`-th first-nonsingular tuple length with the common
`0 + (b*k+r)` presentation used by the multiblock prime-power API. -/
def vinogradovPrimePowerFirstStratumCommonEquiv
    (p k r b n : ℕ) [Fact p.Prime] (q : Fin b) :
    ((Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1))) ×
        (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1)))) ≃
      vinogradovPrimePowerBasePair p 0 (b * k + r) n := by
  have hblocks : q.val + 1 + (b - 1 - q.val) = b := by
    omega
  have hsize :
      (q.val + 1 + (b - 1 - q.val)) * k + r =
        0 + (b * k + r) := by
    simp only [Nat.zero_add]
    rw [hblocks]
  exact Equiv.prodCongr
    (Equiv.arrowCongr (finCongr hsize) (Equiv.refl _))
    (Equiv.arrowCongr (finCongr hsize) (Equiv.refl _))

/-- The `q`-th first-nonsingular prime-power stratum transported to the
single common tuple type for `b` selected blocks. -/
noncomputable def vinogradovPrimePowerFirstStratumCommonSet
    (p k r b n : ℕ) [Fact p.Prime] (q : Fin b) :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) :=
  (vinogradovPrimePowerFirstNonsingularSolutionSet
      p k r q.val (b - 1 - q.val) n).map
    (vinogradovPrimePowerFirstStratumCommonEquiv
      p k r b n q).toEmbedding

/-- Membership in a common-coordinate stratum is pulled back exactly through
the coordinate equivalence. -/
theorem mem_vinogradovPrimePowerFirstStratumCommonSet_iff
    (p k r b n : ℕ) [Fact p.Prime] (q : Fin b)
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerFirstStratumCommonSet p k r b n q ↔
      (vinogradovPrimePowerFirstStratumCommonEquiv
        p k r b n q).symm xy ∈
        vinogradovPrimePowerFirstNonsingularSolutionSet
          p k r q.val (b - 1 - q.val) n := by
  classical
  simp [vinogradovPrimePowerFirstStratumCommonSet]

/-- Common-coordinate transport preserves the numerical value of every left
tuple coordinate. -/
theorem vinogradovPrimePowerFirstStratumCommonEquiv_fst_apply
    (p k r b n : ℕ) [Fact p.Prime] (q : Fin b)
    (xy :
      (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1))) ×
        (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1))))
    (i : Fin (b * k + r)) :
    ((vinogradovPrimePowerFirstStratumCommonEquiv
        p k r b n q) xy).1 (Fin.natAdd 0 i) =
      xy.1 (Fin.cast (by
        have hblocks : q.val + 1 + (b - 1 - q.val) = b := by omega
        simpa [hblocks]) i) := by
  simp [vinogradovPrimePowerFirstStratumCommonEquiv]

/-- Common-coordinate transport preserves the numerical value of every right
tuple coordinate. -/
theorem vinogradovPrimePowerFirstStratumCommonEquiv_snd_apply
    (p k r b n : ℕ) [Fact p.Prime] (q : Fin b)
    (xy :
      (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1))) ×
        (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1))))
    (i : Fin (b * k + r)) :
    ((vinogradovPrimePowerFirstStratumCommonEquiv
        p k r b n q) xy).2 (Fin.natAdd 0 i) =
      xy.2 (Fin.cast (by
        have hblocks : q.val + 1 + (b - 1 - q.val) = b := by omega
        simpa [hblocks]) i) := by
  simp [vinogradovPrimePowerFirstStratumCommonEquiv]

/-- The direct first-nonsingular predicate is invariant under transport to
the common multiblock coordinate type. -/
theorem vinogradovPrimePowerFirstStratumCommonEquiv_firstDirect_iff
    (p k r b n : ℕ) [Fact p.Prime] (q : Fin b)
    (xy :
      (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1))) ×
        (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1)))) :
    VinogradovFirstNonsingularBlockDirect p k r
        (q.val + 1 + (b - 1 - q.val)) ⟨q.val, by omega⟩
        (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ZMod p)) ↔
      VinogradovFirstNonsingularBlockDirect p k r b q
        (fun i ↦
          (((((vinogradovPrimePowerFirstStratumCommonEquiv
            p k r b n q) xy).1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) := by
  let sourceBlocks := q.val + 1 + (b - 1 - q.val)
  have hsourceBlocks : sourceBlocks = b := by
    dsimp [sourceBlocks]
    omega
  let toSource (j : Fin b) : Fin sourceBlocks :=
    ⟨j.val, by simpa [hsourceBlocks] using j.isLt⟩
  let toCommon (j : Fin sourceBlocks) : Fin b :=
    ⟨j.val, by simpa [hsourceBlocks] using j.isLt⟩
  let sourceResidue : Fin (sourceBlocks * k + r) → ZMod p :=
    fun i ↦ (((xy.1 i).val + 1 : ℕ) : ZMod p)
  let commonResidue : Fin (b * k + r) → ZMod p :=
    fun i ↦
      (((((vinogradovPrimePowerFirstStratumCommonEquiv
        p k r b n q) xy).1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)
  have hcoord (j : Fin b) (i : Fin k) :
      commonResidue (vinogradovSelectedBlockIndex k r b j i) =
        sourceResidue
          (vinogradovSelectedBlockIndex k r sourceBlocks (toSource j) i) := by
    dsimp [commonResidue, sourceResidue]
    rw [vinogradovPrimePowerFirstStratumCommonEquiv_fst_apply]
    congr 2
  change
    VinogradovFirstNonsingularBlockDirect p k r sourceBlocks
        ⟨q.val, by omega⟩ sourceResidue ↔
      VinogradovFirstNonsingularBlockDirect p k r b q commonResidue
  constructor
  · intro hsource
    constructor
    · intro j hj hjinj
      have hsing := hsource.1 (toSource j) (by
        change j.val < q.val
        exact hj)
      apply hsing
      intro i l hil
      apply hjinj
      change
        commonResidue (vinogradovSelectedBlockIndex k r b j i) =
          commonResidue (vinogradovSelectedBlockIndex k r b j l)
      rw [hcoord j i, hcoord j l]
      exact hil
    · intro i j hij
      apply hsource.2
      change
        sourceResidue
            (vinogradovSelectedBlockIndex k r sourceBlocks (toSource q) i) =
          sourceResidue
            (vinogradovSelectedBlockIndex k r sourceBlocks (toSource q) j)
      rw [← hcoord q i, ← hcoord q j]
      exact hij
  · intro hcommon
    constructor
    · intro j hj hjinj
      let j' := toCommon j
      have hj' : j' < q := by
        change j.val < q.val
        exact hj
      have hsing := hcommon.1 j' hj'
      apply hsing
      intro i l hil
      apply hjinj
      have hjcast : toSource j' = j := by
        apply Fin.ext
        rfl
      change
        sourceResidue (vinogradovSelectedBlockIndex k r sourceBlocks j i) =
          sourceResidue (vinogradovSelectedBlockIndex k r sourceBlocks j l)
      change
        commonResidue (vinogradovSelectedBlockIndex k r b j' i) =
          commonResidue (vinogradovSelectedBlockIndex k r b j' l) at hil
      rw [hcoord j' i, hcoord j' l, hjcast] at hil
      exact hil
    · intro i j hij
      apply hcommon.2
      have hq : toSource q = ⟨q.val, by omega⟩ := by
        apply Fin.ext
        rfl
      change
        commonResidue (vinogradovSelectedBlockIndex k r b q i) =
          commonResidue (vinogradovSelectedBlockIndex k r b q j)
      rw [hcoord q i, hcoord q j, hq]
      exact hij

/-- The modular Vinogradov equations are invariant under transport to the
common multiblock coordinate type. -/
theorem vinogradovPrimePowerFirstStratumCommonEquiv_solution_iff
    (p k r b n : ℕ) [Fact p.Prime] (q : Fin b)
    (xy :
      (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1))) ×
        (Fin ((q.val + 1 + (b - 1 - q.val)) * k + r) →
          Fin (p ^ (n + 1)))) :
    IsVinogradovSolutionMod (p ^ (n + 1)) k
        ((q.val + 1 + (b - 1 - q.val)) * k + r)
        (p ^ (n + 1)) xy.1 xy.2 ↔
      IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
        (p ^ (n + 1))
        (fun i ↦ ((vinogradovPrimePowerFirstStratumCommonEquiv
          p k r b n q) xy).1 (Fin.natAdd 0 i))
        (fun i ↦ ((vinogradovPrimePowerFirstStratumCommonEquiv
          p k r b n q) xy).2 (Fin.natAdd 0 i)) := by
  have hblocks : q.val + 1 + (b - 1 - q.val) = b := by
    omega
  have hsize :
      (q.val + 1 + (b - 1 - q.val)) * k + r = b * k + r := by
    rw [hblocks]
  let c := finCongr hsize
  let leftCommon : Fin (b * k + r) → Fin (p ^ (n + 1)) :=
    fun i ↦ ((vinogradovPrimePowerFirstStratumCommonEquiv
      p k r b n q) xy).1 (Fin.natAdd 0 i)
  let rightCommon : Fin (b * k + r) → Fin (p ^ (n + 1)) :=
    fun i ↦ ((vinogradovPrimePowerFirstStratumCommonEquiv
      p k r b n q) xy).2 (Fin.natAdd 0 i)
  have hx : (fun i ↦ leftCommon (c i)) = xy.1 := by
    funext i
    dsimp [leftCommon]
    rw [vinogradovPrimePowerFirstStratumCommonEquiv_fst_apply]
    congr 1
  have hy : (fun i ↦ rightCommon (c i)) = xy.2 := by
    funext i
    dsimp [rightCommon]
    rw [vinogradovPrimePowerFirstStratumCommonEquiv_snd_apply]
    congr 1
  have hiff := isVinogradovSolutionMod_comp_equiv_iff
    c leftCommon rightCommon (Q := p ^ (n + 1)) (k := k)
    (X := p ^ (n + 1))
  rw [hx, hy] at hiff
  exact hiff

/-- A common-coordinate stratum records exactly the direct first
nonsingular-block condition and the complete modular Vinogradov system. -/
theorem mem_vinogradovPrimePowerFirstStratumCommonSet_iff_direct
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (q : Fin b)
    (xy : vinogradovPrimePowerBasePair p 0 (b * k + r) n) :
    xy ∈ vinogradovPrimePowerFirstStratumCommonSet p k r b n q ↔
      VinogradovFirstNonsingularBlockDirect p k r b q
          (fun i ↦ (((xy.1 (Fin.natAdd 0 i)).val + 1 : ℕ) : ZMod p)) ∧
        IsVinogradovSolutionMod (p ^ (n + 1)) k (b * k + r)
          (p ^ (n + 1))
          (fun i ↦ xy.1 (Fin.natAdd 0 i))
          (fun i ↦ xy.2 (Fin.natAdd 0 i)) := by
  let e := vinogradovPrimePowerFirstStratumCommonEquiv p k r b n q
  let uv := e.symm xy
  have he : e uv = xy := e.apply_symm_apply xy
  rw [mem_vinogradovPrimePowerFirstStratumCommonSet_iff,
    mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff]
  constructor
  · rintro ⟨hfirst, hsolution⟩
    have hdirectSource :=
      (firstNonsingularBlock_iff_direct (p := p) hk
        (fun i ↦ (((uv.1 i).val + 1 : ℕ) : ZMod p))).mp hfirst
    have hdirectCommon :=
      (vinogradovPrimePowerFirstStratumCommonEquiv_firstDirect_iff
        p k r b n q uv).mp hdirectSource
    have hsolutionCommon :=
      (vinogradovPrimePowerFirstStratumCommonEquiv_solution_iff
        p k r b n q uv).mp hsolution
    rw [he] at hdirectCommon hsolutionCommon
    exact ⟨hdirectCommon, hsolutionCommon⟩
  · rintro ⟨hdirectCommon, hsolutionCommon⟩
    have hdirectSource :=
      (vinogradovPrimePowerFirstStratumCommonEquiv_firstDirect_iff
        p k r b n q uv).mpr (by
          simpa [e, uv] using hdirectCommon)
    have hfirst :=
      (firstNonsingularBlock_iff_direct (p := p) hk
        (fun i ↦ (((uv.1 i).val + 1 : ℕ) : ZMod p))).mpr hdirectSource
    have hsolution :=
      (vinogradovPrimePowerFirstStratumCommonEquiv_solution_iff
        p k r b n q uv).mpr (by
          simpa [e, uv] using hsolutionCommon)
    exact ⟨hfirst, hsolution⟩

/-- Transport to common coordinates preserves each first-stratum count. -/
theorem card_vinogradovPrimePowerFirstStratumCommonSet
    (p k r b n : ℕ) [Fact p.Prime] (q : Fin b) :
    (vinogradovPrimePowerFirstStratumCommonSet p k r b n q).card =
      (vinogradovPrimePowerFirstNonsingularSolutionSet
        p k r q.val (b - 1 - q.val) n).card := by
  simp [vinogradovPrimePowerFirstStratumCommonSet]

/-- Union of all common-coordinate first-nonsingular strata. -/
noncomputable def vinogradovPrimePowerFirstStrataCommonUnion
    (p k r b n : ℕ) [Fact p.Prime] :
    Finset (vinogradovPrimePowerBasePair p 0 (b * k + r) n) :=
  Finset.univ.biUnion fun q : Fin b ↦
    vinogradovPrimePowerFirstStratumCommonSet p k r b n q

/-- The common first-stratum union covers exactly the prime-power solutions
having at least one nonsingular selected block. -/
theorem vinogradovPrimePowerFirstStrataCommonUnion_eq_someBlock
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    vinogradovPrimePowerFirstStrataCommonUnion p k r b n =
      vinogradovPrimePowerSomeBlockNonsingularSolutionSet p k r b n := by
  classical
  ext xy
  rw [mem_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_iff]
  simp only [vinogradovPrimePowerFirstStrataCommonUnion,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    have hparts :=
      (mem_vinogradovPrimePowerFirstStratumCommonSet_iff_direct
        p k r b n hk q xy).mp hq
    exact ⟨
      (hasNonsingularBlock_iff_exists_firstNonsingularBlockDirect
        p k r b _).mpr ⟨q, hparts.1⟩,
      hparts.2⟩
  · rintro ⟨hhas, hsolution⟩
    obtain ⟨q, hq⟩ :=
      (hasNonsingularBlock_iff_exists_firstNonsingularBlockDirect
        p k r b _).mp hhas
    exact ⟨q,
      (mem_vinogradovPrimePowerFirstStratumCommonSet_iff_direct
        p k r b n hk q xy).mpr ⟨hq, hsolution⟩⟩

/-- The nonsingular branch is bounded by the sum of its first-nonsingular
strata, now that all strata inhabit a single finite type. -/
theorem card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_sum_first
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (vinogradovPrimePowerSomeBlockNonsingularSolutionSet
        p k r b n).card ≤
      ∑ q : Fin b,
        (vinogradovPrimePowerFirstNonsingularSolutionSet
          p k r q.val (b - 1 - q.val) n).card := by
  rw [← vinogradovPrimePowerFirstStrataCommonUnion_eq_someBlock
    p k r b n hk]
  calc
    (vinogradovPrimePowerFirstStrataCommonUnion p k r b n).card ≤
        ∑ q : Fin b,
          (vinogradovPrimePowerFirstStratumCommonSet
            p k r b n q).card := Finset.card_biUnion_le
    _ = ∑ q : Fin b,
          (vinogradovPrimePowerFirstNonsingularSolutionSet
            p k r q.val (b - 1 - q.val) n).card := by
      apply Finset.sum_congr rfl
      intro q _
      exact card_vinogradovPrimePowerFirstStratumCommonSet p k r b n q

/-- Substituting the stratified Hensel estimate term by term gives an explicit
finite-sum bound for the full nonsingular branch. -/
theorem card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_sum_stratified
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerSomeBlockNonsingularSolutionSet
        p k r b n).card ≤
      ∑ q : Fin b,
        ((p ^ k - p.descFactorial k) ^ q.val *
            p.descFactorial k * p ^ ((b - 1 - q.val) * k + r) *
            p ^ ((q.val + 1 + (b - 1 - q.val)) * k + r)) *
          (p ^ (k + 2 *
            (q.val * k + (b - 1 - q.val) * k + r))) ^ n := by
  calc
    (vinogradovPrimePowerSomeBlockNonsingularSolutionSet
        p k r b n).card ≤
        ∑ q : Fin b,
          (vinogradovPrimePowerFirstNonsingularSolutionSet
            p k r q.val (b - 1 - q.val) n).card :=
      card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_sum_first
        p k r b n hk
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      exact
        card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_stratified
          p k r q.val (b - 1 - q.val) n hk hkp

/-- For `q < b`, every factor in the stratified Hensel bound except the
finite geometric weight is independent of `q`. -/
theorem vinogradovPrimePowerFirstStratifiedTerm_eq_common
    (p k r b n q : ℕ) (hq : q < b) :
    ((p ^ k - p.descFactorial k) ^ q *
          p.descFactorial k * p ^ ((b - 1 - q) * k + r) *
          p ^ ((q + 1 + (b - 1 - q)) * k + r)) *
        (p ^ (k + 2 * (q * k + (b - 1 - q) * k + r))) ^ n =
      ((p ^ k - p.descFactorial k) ^ q *
          p.descFactorial k * (p ^ k) ^ (b - 1 - q)) *
        (p ^ r * p ^ (b * k + r) *
          (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) := by
  have hblocks : q + 1 + (b - 1 - q) = b := by
    omega
  have hprefix : q + (b - 1 - q) = b - 1 := by
    omega
  have htailExponent :
      q * k + (b - 1 - q) * k + r = (b - 1) * k + r := by
    rw [← Nat.add_mul, hprefix]
  have htailPow :
      p ^ ((b - 1 - q) * k + r) =
        (p ^ k) ^ (b - 1 - q) * p ^ r := by
    rw [pow_add, Nat.mul_comm (b - 1 - q) k, pow_mul]
  rw [hblocks, htailExponent, htailPow]
  ring

/-- Closed form of the sum of all stratified Hensel upper bounds. -/
theorem sum_vinogradovPrimePowerFirstStratified_eq
    (p k r b n : ℕ) :
    (∑ q : Fin b,
        ((p ^ k - p.descFactorial k) ^ q.val *
            p.descFactorial k * p ^ ((b - 1 - q.val) * k + r) *
            p ^ ((q.val + 1 + (b - 1 - q.val)) * k + r)) *
          (p ^ (k + 2 *
            (q.val * k + (b - 1 - q.val) * k + r))) ^ n) =
      ((p ^ k) ^ b - (p ^ k - p.descFactorial k) ^ b) *
        (p ^ r * p ^ (b * k + r) *
          (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) := by
  let term : ℕ → ℕ := fun q ↦
    ((p ^ k - p.descFactorial k) ^ q *
        p.descFactorial k * p ^ ((b - 1 - q) * k + r) *
        p ^ ((q + 1 + (b - 1 - q)) * k + r)) *
      (p ^ (k + 2 * (q * k + (b - 1 - q) * k + r))) ^ n
  change (∑ q : Fin b, term q.val) = _
  rw [Fin.sum_univ_eq_sum_range term b]
  dsimp only [term]
  calc
    (∑ q ∈ Finset.range b,
        ((p ^ k - p.descFactorial k) ^ q *
            p.descFactorial k * p ^ ((b - 1 - q) * k + r) *
            p ^ ((q + 1 + (b - 1 - q)) * k + r)) *
          (p ^ (k + 2 * (q * k + (b - 1 - q) * k + r))) ^ n) =
        ∑ q ∈ Finset.range b,
          ((p ^ k - p.descFactorial k) ^ q *
              p.descFactorial k * (p ^ k) ^ (b - 1 - q)) *
            (p ^ r * p ^ (b * k + r) *
              (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact vinogradovPrimePowerFirstStratifiedTerm_eq_common
        p k r b n q (Finset.mem_range.mp hq)
    _ = (∑ q ∈ Finset.range b,
          (p ^ k - p.descFactorial k) ^ q *
            p.descFactorial k * (p ^ k) ^ (b - 1 - q)) *
          (p ^ r * p ^ (b * k + r) *
            (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) := by
      rw [Finset.sum_mul]
    _ = ((p ^ k) ^ b - (p ^ k - p.descFactorial k) ^ b) *
          (p ^ r * p ^ (b * k + r) *
            (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) := by
      rw [sum_firstNonsingular_geometric]
      exact Nat.descFactorial_le_pow _ _

/-- Summing the first-nonsingular strata gives a closed upper bound for the
entire nonsingular multiblock branch. -/
theorem card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_closed
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerSomeBlockNonsingularSolutionSet
        p k r b n).card ≤
      ((p ^ k) ^ b - (p ^ k - p.descFactorial k) ^ b) *
        (p ^ r * p ^ (b * k + r) *
          (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) := by
  rw [← sum_vinogradovPrimePowerFirstStratified_eq p k r b n]
  exact
    card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_sum_stratified
      p k r b n hk hkp

/-- The all-singular and first-nonsingular estimates combine into a complete
explicit multiblock prime-power Vinogradov solution-count bound. -/
theorem vinogradovPrimePowerMultiBlockSolutionCount_le_strata
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    vinogradovSolutionCountMod (p ^ (n + 1)) k (b * k + r)
        (p ^ (n + 1)) ≤
      ((p ^ k - p.descFactorial k) ^ b * p ^ r *
          p ^ (b * k + r)) *
        (p ^ (2 * (b * k + r))) ^ n +
      ((p ^ k) ^ b - (p ^ k - p.descFactorial k) ^ b) *
        (p ^ r * p ^ (b * k + r) *
          (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) := by
  rw [← card_primePowerMultiBlockSingular_add_someNonsingular]
  exact Nat.add_le_add
    (card_vinogradovPrimePowerMultiBlockSingularSolutionSet_le p k r b n)
    (card_vinogradovPrimePowerSomeBlockNonsingularSolutionSet_le_closed
      p k r b n hk hkp)

/-- The multiblock strata estimate transfers to the normalized complete
Vinogradov moment. -/
theorem norm_normalizedVinogradovMomentMod_primePowerMultiBlock_le_strata
    (p k r b n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    ‖normalizedVinogradovMomentMod
        (p ^ (n + 1)) k (b * k + r) (p ^ (n + 1))‖ ≤
      ((((p ^ k - p.descFactorial k) ^ b * p ^ r *
            p ^ (b * k + r)) *
          (p ^ (2 * (b * k + r))) ^ n +
        ((p ^ k) ^ b - (p ^ k - p.descFactorial k) ^ b) *
          (p ^ r * p ^ (b * k + r) *
            (p ^ (k + 2 * ((b - 1) * k + r))) ^ n) : ℕ) : ℝ) := by
  letI : NeZero (p ^ (n + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [normalizedVinogradovMomentMod_eq_solutionCount]
  norm_cast
  exact vinogradovPrimePowerMultiBlockSolutionCount_le_strata
    p k r b n hk hkp

end

end ZeroFreeRegion.VinogradovKorobov
