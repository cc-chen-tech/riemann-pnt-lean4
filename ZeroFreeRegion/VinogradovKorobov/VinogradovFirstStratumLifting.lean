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

/-- Undoing the selected-block cycle on a tuple pair preserves the bounded
Vinogradov system.  This packages the coordinate transport in the orientation
used by the restricted Hensel lift. -/
theorem isVinogradovSolutionMod_uncycledPair_iff
    (Q d X k r q a : ℕ) (hk : 0 < k)
    (xy :
      (Fin (k + (q * k + a * k + r)) → Fin X) ×
        (Fin (k + (q * k + a * k + r)) → Fin X)) :
    IsVinogradovSolutionMod Q d ((q + 1 + a) * k + r) X
        ((vinogradovCycledHeadTailPairEquiv
          (α := Fin X) k r q a hk).symm xy).1
        ((vinogradovCycledHeadTailPairEquiv
          (α := Fin X) k r q a hk).symm xy).2 ↔
      IsVinogradovSolutionMod Q d (k + (q * k + a * k + r)) X
        xy.1 xy.2 := by
  let e := vinogradovCycledHeadTailPairEquiv
    (α := Fin X) k r q a hk
  let uv := e.symm xy
  have h := (isVinogradovSolutionMod_cycledHeadTail_iff
    Q d X k r q a hk uv.1 uv.2).symm
  have he : e uv = xy := e.apply_symm_apply xy
  have hx : vinogradovCycledHeadTailTuple k r q a hk uv.1 = xy.1 := by
    simpa only [e, vinogradovCycledHeadTailPairEquiv,
      Equiv.prodCongr_apply,
      vinogradovCycledHeadTailFunctionEquiv_apply] using
        congrArg Prod.fst he
  have hy : vinogradovCycledHeadTailTuple k r q a hk uv.2 = xy.2 := by
    simpa only [e, vinogradovCycledHeadTailPairEquiv,
      Equiv.prodCongr_apply,
      vinogradovCycledHeadTailFunctionEquiv_apply] using
        congrArg Prod.snd he
  simpa only [uv, hx, hy] using h

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

/-- The one-based complete residue equivalence used to compare the first
prime-power level with the residue-field block stratification. -/
noncomputable def vinogradovFirstStratumCompleteResidueEquiv
    (p : ℕ) [NeZero p] : Fin p ≃ ZMod p :=
  (ZMod.finEquiv p).toEquiv.trans (Equiv.addRight 1)

theorem vinogradovFirstStratumCompleteResidueEquiv_apply
    (p : ℕ) [NeZero p] (x : Fin p) :
    vinogradovFirstStratumCompleteResidueEquiv p x =
      (x.val : ZMod p) + 1 := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p =>
      change (x + (1 : Fin (p + 1)) : Fin (p + 1)) =
        (⟨x.val % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩ :
          Fin (p + 1)) + 1
      congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt x.isLt]

/-- Coordinatewise complete-residue transport for an ordered tuple pair. -/
noncomputable def vinogradovFirstStratumCompleteResiduePairEquiv
    (p s : ℕ) [NeZero p] :
    ((Fin s → Fin (p ^ (0 + 1))) ×
        (Fin s → Fin (p ^ (0 + 1)))) ≃
      ((Fin s → ZMod p) × (Fin s → ZMod p)) :=
  Equiv.prodCongr
    (Equiv.piCongrRight fun _ ↦
      (finCongr (by simp)).trans
        (vinogradovFirstStratumCompleteResidueEquiv p))
    (Equiv.piCongrRight fun _ ↦
      (finCongr (by simp)).trans
        (vinogradovFirstStratumCompleteResidueEquiv p))

/-- At the first prime level, retain the exact first-nonsingular condition on
the left tuple and leave the right tuple unrestricted. -/
noncomputable def vinogradovPrimeFirstNonsingularAmbientSet
    (p k r q a : ℕ) [Fact p.Prime] :
    Finset
      ((Fin ((q + 1 + a) * k + r) → Fin (p ^ (0 + 1))) ×
        (Fin ((q + 1 + a) * k + r) → Fin (p ^ (0 + 1)))) := by
  classical
  let s := (q + 1 + a) * k + r
  let e := vinogradovFirstStratumCompleteResiduePairEquiv p s
  exact
    ((vinogradovFirstNonsingularResidueSet p k r q a).product
      (Finset.univ : Finset (Fin s → ZMod p))).map e.symm.toEmbedding

/-- Membership in the base ambient set is exactly the encoded first
nonsingular block condition. -/
theorem mem_vinogradovPrimeFirstNonsingularAmbientSet_iff
    (p k r q a : ℕ) [Fact p.Prime]
    (x y : Fin ((q + 1 + a) * k + r) → Fin (p ^ (0 + 1))) :
    (x, y) ∈ vinogradovPrimeFirstNonsingularAmbientSet p k r q a ↔
      VinogradovFirstNonsingularBlock p k r q a
        (fun i ↦ (((x i).val + 1 : ℕ) : ZMod p)) := by
  classical
  let s := (q + 1 + a) * k + r
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let e := vinogradovFirstStratumCompleteResiduePairEquiv p s
  have hxencode : (e (x, y)).1 =
      (fun i ↦ (((x i).val + 1 : ℕ) : ZMod p)) := by
    funext i
    change vinogradovFirstStratumCompleteResidueEquiv p
      (Fin.cast (by simp) (x i)) = _
    simpa only [Nat.cast_add, Nat.cast_one] using
      vinogradovFirstStratumCompleteResidueEquiv_apply p
        (Fin.cast (by simp) (x i))
  simp only [vinogradovPrimeFirstNonsingularAmbientSet, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hz_eq : z = e (x, y) := by
      calc
        z = e (e.symm z) := e.apply_symm_apply z |>.symm
        _ = e (x, y) := congrArg e hzx
    have hparts := Finset.mem_product.mp hz
    rw [hz_eq, hxencode] at hparts
    exact (mem_vinogradovFirstNonsingularResidueSet_iff
      p k r q a _).mp hparts.1
  · intro h
    refine ⟨e (x, y), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · apply (mem_vinogradovFirstNonsingularResidueSet_iff
          p k r q a _).mpr
        rw [hxencode]
        exact h
      · simp
    · change e.symm (e (x, y)) = (x, y)
      simp

/-- Exact cardinality of the base ambient first-nonsingular stratum. -/
theorem card_vinogradovPrimeFirstNonsingularAmbientSet
    (p k r q a : ℕ) [Fact p.Prime] :
    (vinogradovPrimeFirstNonsingularAmbientSet p k r q a).card =
      (p ^ k - p.descFactorial k) ^ q * p.descFactorial k *
        p ^ (a * k + r) * p ^ ((q + 1 + a) * k + r) := by
  classical
  let s := (q + 1 + a) * k + r
  rw [vinogradovPrimeFirstNonsingularAmbientSet, Finset.card_map]
  change
    ((vinogradovFirstNonsingularResidueSet p k r q a).product
      (Finset.univ : Finset (Fin s → ZMod p))).card = _
  calc
    ((vinogradovFirstNonsingularResidueSet p k r q a).product
        (Finset.univ : Finset (Fin s → ZMod p))).card =
        (vinogradovFirstNonsingularResidueSet p k r q a).card *
          (Finset.univ : Finset (Fin s → ZMod p)).card :=
      Finset.card_product _ _
    _ = _ := by
      rw [card_vinogradovFirstNonsingularResidueSet]
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        ZMod.card, s]

/-- The actual first-level modular solutions retain the exact `q`-block
singular saving from the residue stratification. -/
theorem card_vinogradovPrimePowerFirstNonsingularSolutionSet_zero_le
    (p k r q a : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a 0).card ≤
      (p ^ k - p.descFactorial k) ^ q * p.descFactorial k *
        p ^ (a * k + r) * p ^ ((q + 1 + a) * k + r) := by
  classical
  have hsubset :
      vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a 0 ⊆
        vinogradovPrimeFirstNonsingularAmbientSet p k r q a := by
    intro xy hxy
    apply (mem_vinogradovPrimeFirstNonsingularAmbientSet_iff
      p k r q a xy.1 xy.2).mpr
    exact (mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff
      p k r q a 0 xy.1 xy.2).mp hxy |>.1
  rw [← card_vinogradovPrimeFirstNonsingularAmbientSet p k r q a]
  exact Finset.card_le_card hsubset

/-- After a standard Hensel digit lift in cycled coordinates, undoing the
cycle preserves every original left coordinate modulo `p`. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_uncycled_fst_mod
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k)
    (xy : vinogradovPrimePowerBasePair p k
      (q * k + a * k + r) n)
    (z : vinogradovPrimePowerSplitCorrection p k
      (q * k + a * k + r))
    (i : Fin ((q + 1 + a) * k + r)) :
    (((((vinogradovCycledHeadTailPairEquiv
      (α := Fin (p ^ (n + 2))) k r q a hk).symm
        (vinogradovPrimePowerLiftAmbientEquiv p k
          (q * k + a * k + r) n ⟨xy, z⟩)).1 i).val + 1 : ℕ) :
        ZMod p) =
      (((((vinogradovCycledHeadTailPairEquiv
        (α := Fin (p ^ (n + 1))) k r q a hk).symm xy).1 i).val + 1 : ℕ) :
        ZMod p) := by
  simpa [vinogradovCycledHeadTailPairEquiv,
    vinogradovCycledHeadTailFunctionEquiv] using
      (vinogradovPrimePowerLiftAmbientEquiv_fst_mod p k
        (q * k + a * k + r) n xy z
        ((vinogradovCycledHeadTailEquiv k r q a hk).symm i))

/-- The exact first-nonsingular residue stratum is invariant under one
Hensel digit lift performed after cycling its selected block to the head. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_uncycled_firstNonsingular_iff
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k)
    (xy : vinogradovPrimePowerBasePair p k
      (q * k + a * k + r) n)
    (z : vinogradovPrimePowerSplitCorrection p k
      (q * k + a * k + r)) :
    VinogradovFirstNonsingularBlock p k r q a
        (fun i ↦
          (((((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 2))) k r q a hk).symm
              (vinogradovPrimePowerLiftAmbientEquiv p k
                (q * k + a * k + r) n ⟨xy, z⟩)).1 i).val + 1 : ℕ) :
            ZMod p)) ↔
      VinogradovFirstNonsingularBlock p k r q a
        (fun i ↦
          (((((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 1))) k r q a hk).symm xy).1 i).val + 1 : ℕ) :
            ZMod p)) := by
  have hfun :
      (fun i ↦
        (((((vinogradovCycledHeadTailPairEquiv
          (α := Fin (p ^ (n + 2))) k r q a hk).symm
            (vinogradovPrimePowerLiftAmbientEquiv p k
              (q * k + a * k + r) n ⟨xy, z⟩)).1 i).val + 1 : ℕ) :
          ZMod p)) =
        (fun i ↦
          (((((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 1))) k r q a hk).symm xy).1 i).val + 1 : ℕ) :
            ZMod p)) := by
    funext i
    exact vinogradovPrimePowerLiftAmbientEquiv_uncycled_fst_mod
      p k r q a n hk xy z i
  rw [hfun]

/-- The first-nonsingular solution stratum written in the cycled head-tail
coordinates used by the standard Hensel lift. -/
noncomputable def vinogradovPrimePowerCycledFirstNonsingularSolutionSet
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    Finset (vinogradovPrimePowerBasePair p k
      (q * k + a * k + r) n) := by
  classical
  exact
    (vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a n).map
      (vinogradovCycledHeadTailPairEquiv
        (α := Fin (p ^ (n + 1))) k r q a hk).toEmbedding

/-- Membership in the cycled stratum is transported exactly by the inverse
coordinate equivalence. -/
theorem mem_vinogradovPrimePowerCycledFirstNonsingularSolutionSet_iff
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k)
    (xy : vinogradovPrimePowerBasePair p k
      (q * k + a * k + r) n) :
    xy ∈ vinogradovPrimePowerCycledFirstNonsingularSolutionSet
        p k r q a n hk ↔
      (vinogradovCycledHeadTailPairEquiv
        (α := Fin (p ^ (n + 1))) k r q a hk).symm xy ∈
          vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a n := by
  classical
  simp only [vinogradovPrimePowerCycledFirstNonsingularSolutionSet,
    Finset.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro hz
    refine ⟨(vinogradovCycledHeadTailPairEquiv
      (α := Fin (p ^ (n + 1))) k r q a hk).symm xy, hz, ?_⟩
    simp

/-- Cycling coordinates does not change the stratum cardinality. -/
theorem card_vinogradovPrimePowerCycledFirstNonsingularSolutionSet
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (vinogradovPrimePowerCycledFirstNonsingularSolutionSet
      p k r q a n hk).card =
      (vinogradovPrimePowerFirstNonsingularSolutionSet
        p k r q a n).card := by
  classical
  simp [vinogradovPrimePowerCycledFirstNonsingularSolutionSet]

/-- The one-step Hensel correction space restricted to a single
first-nonsingular stratum. -/
noncomputable def vinogradovPrimePowerFirstNonsingularLiftSet
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    Finset
      (Σ _ : vinogradovPrimePowerBasePair p k
          (q * k + a * k + r) n,
        Σ _ : vinogradovFreeCorrectionData p k
          (q * k + a * k + r),
          Fin k → ZMod p) := by
  classical
  exact
    (vinogradovPrimePowerCycledFirstNonsingularSolutionSet
      p k r q a n hk).sigma fun xy ↦
        vinogradovSolutionCorrectionSet p k
          (q * k + a * k + r) n
          (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ))
          (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ))

/-- Restricting the base solutions preserves the uniform Hensel fiber bound. -/
theorem card_vinogradovPrimePowerFirstNonsingularLiftSet_le
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerFirstNonsingularLiftSet
      p k r q a n hk).card ≤
      (vinogradovPrimePowerFirstNonsingularSolutionSet
        p k r q a n).card *
        p ^ (k + 2 * (q * k + a * k + r)) := by
  classical
  rw [vinogradovPrimePowerFirstNonsingularLiftSet, Finset.card_sigma]
  calc
    (∑ xy ∈ vinogradovPrimePowerCycledFirstNonsingularSolutionSet
        p k r q a n hk,
      (vinogradovSolutionCorrectionSet p k
        (q * k + a * k + r) n
        (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ))
        (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ))).card) ≤
      ∑ _xy ∈ vinogradovPrimePowerCycledFirstNonsingularSolutionSet
        p k r q a n hk,
        p ^ (k + 2 * (q * k + a * k + r)) := by
      apply Finset.sum_le_sum
      intro xy hxy
      have hsource :=
        (mem_vinogradovPrimePowerCycledFirstNonsingularSolutionSet_iff
          p k r q a n hk xy).mp hxy
      have hfirst :=
        (mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff
          p k r q a n _ _).mp hsource |>.1
      have hinj := hfirst.cycledHeadTail_injective hk
      have hencoded :
          vinogradovCycledHeadTailTuple k r q a hk
              (fun i ↦
                ((((vinogradovCycledHeadTailFunctionEquiv
                  (α := Fin (p ^ (n + 1))) k r q a hk).symm xy.1 i).val + 1 :
                  ℕ) : ZMod p)) =
            (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ZMod p)) := by
        funext i
        simp [vinogradovCycledHeadTailTuple,
          vinogradovCycledHeadTailFunctionEquiv]
      rw [hencoded] at hinj
      have hcast : Function.Injective fun i : Fin k ↦
          (((((xy.1 (Fin.castAdd (q * k + a * k + r) i)).val + 1 : ℕ) :
            ℤ)) : ZMod p) := by
        intro i j hij
        apply hinj
        simpa using hij
      exact card_vinogradovSolutionCorrectionSet_le p k
        (q * k + a * k + r) n hkp
        (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ))
        (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ)) hcast
    _ = (vinogradovPrimePowerFirstNonsingularSolutionSet
          p k r q a n).card *
        p ^ (k + 2 * (q * k + a * k + r)) := by
      simp [card_vinogradovPrimePowerCycledFirstNonsingularSolutionSet]

/-- Membership in the restricted lift set is transported exactly to the same
first-nonsingular stratum at the next prime-power level. -/
theorem mem_vinogradovPrimePowerFirstNonsingularLiftSet_iff_image_mem
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k)
    (w : Σ _ : vinogradovPrimePowerBasePair p k
        (q * k + a * k + r) n,
      vinogradovPrimePowerSplitCorrection p k
        (q * k + a * k + r)) :
    w ∈ vinogradovPrimePowerFirstNonsingularLiftSet
        p k r q a n hk ↔
      vinogradovPrimePowerLiftAmbientEquiv p k
          (q * k + a * k + r) n w ∈
        vinogradovPrimePowerCycledFirstNonsingularSolutionSet
          p k r q a (n + 1) hk := by
  rcases w with ⟨xy, z⟩
  rw [vinogradovPrimePowerFirstNonsingularLiftSet, Finset.mem_sigma]
  constructor
  · rintro ⟨hbaseCycled, hcorrection⟩
    have hbaseOriginal :=
      (mem_vinogradovPrimePowerCycledFirstNonsingularSolutionSet_iff
        p k r q a n hk xy).mp hbaseCycled
    have hbaseParts :=
      (mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff
        p k r q a n _ _).mp hbaseOriginal
    have hhighCycled :=
      (mem_vinogradovSolutionCorrectionSet_iff_lifted_solution
        p k (q * k + a * k + r) n xy z).mp hcorrection
    have hhighOriginal :
        IsVinogradovSolutionMod (p ^ (n + 2)) k
          ((q + 1 + a) * k + r) (p ^ (n + 2))
          ((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 2))) k r q a hk).symm
              (vinogradovPrimePowerLiftAmbientEquiv p k
                (q * k + a * k + r) n ⟨xy, z⟩)).1
          ((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 2))) k r q a hk).symm
              (vinogradovPrimePowerLiftAmbientEquiv p k
                (q * k + a * k + r) n ⟨xy, z⟩)).2 :=
      (isVinogradovSolutionMod_uncycledPair_iff
        (p ^ (n + 2)) k (p ^ (n + 2)) k r q a hk _).mpr
          hhighCycled
    apply
      (mem_vinogradovPrimePowerCycledFirstNonsingularSolutionSet_iff
        p k r q a (n + 1) hk _).mpr
    apply
      (mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff
        p k r q a (n + 1) _ _).mpr
    constructor
    · exact
        (vinogradovPrimePowerLiftAmbientEquiv_uncycled_firstNonsingular_iff
          p k r q a n hk xy z).mpr hbaseParts.1
    · simpa only [Nat.add_assoc] using hhighOriginal
  · intro hhighCycledMem
    have hhighOriginalMem :=
      (mem_vinogradovPrimePowerCycledFirstNonsingularSolutionSet_iff
        p k r q a (n + 1) hk _).mp hhighCycledMem
    have hhighParts :=
      (mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff
        p k r q a (n + 1) _ _).mp hhighOriginalMem
    have hhighOriginal :
        IsVinogradovSolutionMod (p ^ (n + 2)) k
          ((q + 1 + a) * k + r) (p ^ (n + 2))
          ((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 2))) k r q a hk).symm
              (vinogradovPrimePowerLiftAmbientEquiv p k
                (q * k + a * k + r) n ⟨xy, z⟩)).1
          ((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 2))) k r q a hk).symm
              (vinogradovPrimePowerLiftAmbientEquiv p k
                (q * k + a * k + r) n ⟨xy, z⟩)).2 := by
      simpa only [Nat.add_assoc] using hhighParts.2
    have hhighCycled :=
      (isVinogradovSolutionMod_uncycledPair_iff
        (p ^ (n + 2)) k (p ^ (n + 2)) k r q a hk _).mp
          hhighOriginal
    have hbaseCycled :=
      vinogradovPrimePowerLiftAmbientEquiv_solution_to_base
        p k (q * k + a * k + r) n xy z hhighCycled
    have hbaseOriginal :
        IsVinogradovSolutionMod (p ^ (n + 1)) k
          ((q + 1 + a) * k + r) (p ^ (n + 1))
          ((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 1))) k r q a hk).symm xy).1
          ((vinogradovCycledHeadTailPairEquiv
            (α := Fin (p ^ (n + 1))) k r q a hk).symm xy).2 :=
      (isVinogradovSolutionMod_uncycledPair_iff
        (p ^ (n + 1)) k (p ^ (n + 1)) k r q a hk xy).mpr
          hbaseCycled
    constructor
    · apply
        (mem_vinogradovPrimePowerCycledFirstNonsingularSolutionSet_iff
          p k r q a n hk xy).mpr
      apply
        (mem_vinogradovPrimePowerFirstNonsingularSolutionSet_iff
          p k r q a n _ _).mpr
      constructor
      · exact
          (vinogradovPrimePowerLiftAmbientEquiv_uncycled_firstNonsingular_iff
            p k r q a n hk xy z).mp hhighParts.1
      · exact hbaseOriginal
    · exact
        (mem_vinogradovSolutionCorrectionSet_iff_lifted_solution
          p k (q * k + a * k + r) n xy z).mpr hhighCycled

/-- Mapping the restricted lift set through the digit equivalence gives
exactly the cycled first-nonsingular stratum at the next level. -/
theorem map_vinogradovPrimePowerFirstNonsingularLiftSet_eq
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (vinogradovPrimePowerFirstNonsingularLiftSet
        p k r q a n hk).map
        (vinogradovPrimePowerLiftAmbientEquiv p k
          (q * k + a * k + r) n).toEmbedding =
      vinogradovPrimePowerCycledFirstNonsingularSolutionSet
        p k r q a (n + 1) hk := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact
      (mem_vinogradovPrimePowerFirstNonsingularLiftSet_iff_image_mem
        p k r q a n hk w).mp hw
  · intro hv
    let e := vinogradovPrimePowerLiftAmbientEquiv p k
      (q * k + a * k + r) n
    let w := e.symm v
    have hew : e w = v := e.apply_symm_apply v
    apply Finset.mem_map.mpr
    refine ⟨w, ?_, hew⟩
    apply
      (mem_vinogradovPrimePowerFirstNonsingularLiftSet_iff_image_mem
        p k r q a n hk w).mpr
    simpa [e, w] using hv

/-- Each first-nonsingular stratum satisfies the same one-step Hensel
recurrence as the standard head stratum, without discarding its base saving. -/
theorem card_vinogradovPrimePowerFirstNonsingularSolutionSet_succ_le
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerFirstNonsingularSolutionSet
        p k r q a (n + 1)).card ≤
      (vinogradovPrimePowerFirstNonsingularSolutionSet
        p k r q a n).card *
        p ^ (k + 2 * (q * k + a * k + r)) := by
  rw [← card_vinogradovPrimePowerCycledFirstNonsingularSolutionSet
      p k r q a (n + 1) hk,
    ← map_vinogradovPrimePowerFirstNonsingularLiftSet_eq
      p k r q a n hk,
    Finset.card_map]
  exact card_vinogradovPrimePowerFirstNonsingularLiftSet_le
    p k r q a n hk hkp

/-- Iterating the restricted recurrence retains the exact cardinality of the
base first-nonsingular stratum. -/
theorem card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_base_mul_pow
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a n).card ≤
      (vinogradovPrimePowerFirstNonsingularSolutionSet
        p k r q a 0).card *
        (p ^ (k + 2 * (q * k + a * k + r))) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (vinogradovPrimePowerFirstNonsingularSolutionSet
            p k r q a (n + 1)).card ≤
            (vinogradovPrimePowerFirstNonsingularSolutionSet
              p k r q a n).card *
              p ^ (k + 2 * (q * k + a * k + r)) :=
          card_vinogradovPrimePowerFirstNonsingularSolutionSet_succ_le
            p k r q a n hk hkp
        _ ≤ ((vinogradovPrimePowerFirstNonsingularSolutionSet
              p k r q a 0).card *
              (p ^ (k + 2 * (q * k + a * k + r))) ^ n) *
              p ^ (k + 2 * (q * k + a * k + r)) :=
          Nat.mul_le_mul_right
            (p ^ (k + 2 * (q * k + a * k + r))) ih
        _ = (vinogradovPrimePowerFirstNonsingularSolutionSet
              p k r q a 0).card *
              (p ^ (k + 2 * (q * k + a * k + r))) ^ (n + 1) := by
          simp only [pow_succ, mul_assoc]

/-- Fully explicit first-stratum lifting bound.  The factor
`(p^k - p.descFactorial k)^q` records the saving from the `q` preceding
singular blocks and survives every prime-power lift. -/
theorem card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_stratified
    (p k r q a n : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    (vinogradovPrimePowerFirstNonsingularSolutionSet p k r q a n).card ≤
      ((p ^ k - p.descFactorial k) ^ q * p.descFactorial k *
          p ^ (a * k + r) * p ^ ((q + 1 + a) * k + r)) *
        (p ^ (k + 2 * (q * k + a * k + r))) ^ n := by
  exact
    (card_vinogradovPrimePowerFirstNonsingularSolutionSet_le_base_mul_pow
      p k r q a n hk hkp).trans
      (Nat.mul_le_mul_right
        ((p ^ (k + 2 * (q * k + a * k + r))) ^ n)
        (card_vinogradovPrimePowerFirstNonsingularSolutionSet_zero_le
          p k r q a))


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
