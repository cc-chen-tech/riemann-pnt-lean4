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

end

end ZeroFreeRegion.VinogradovKorobov
