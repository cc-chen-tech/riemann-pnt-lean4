import ZeroFreeRegion.VinogradovKorobov.VinogradovMixedMoment

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- All degree-`d` Vinogradov solution pairs over the complete residue ring
`ZMod Q`. -/
noncomputable def vinogradovResidueSolutionPairSet
    (Q d s : ℕ) [NeZero Q] :
    Finset ((Fin s → ZMod Q) × (Fin s → ZMod Q)) := by
  classical
  exact Finset.univ.filter fun xy ↦
    IsVinogradovResidueSolution Q d s xy.1 xy.2

theorem mem_vinogradovResidueSolutionPairSet_iff
    (Q d s : ℕ) [NeZero Q]
    (xy : (Fin s → ZMod Q) × (Fin s → ZMod Q)) :
    xy ∈ vinogradovResidueSolutionPairSet Q d s ↔
      IsVinogradovResidueSolution Q d s xy.1 xy.2 := by
  classical
  simp [vinogradovResidueSolutionPairSet]

/-- The one-based complete interval is equivalent to its residue ring. -/
noncomputable def vinogradovCompleteResidueEquiv
    (Q : ℕ) [NeZero Q] : Fin Q ≃ ZMod Q :=
  (ZMod.finEquiv Q).toEquiv.trans (Equiv.addRight 1)

theorem vinogradovCompleteResidueEquiv_apply
    (Q : ℕ) [NeZero Q] (x : Fin Q) :
    vinogradovCompleteResidueEquiv Q x = (x.val : ZMod Q) + 1 := by
  cases Q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ Q =>
      change (x + (1 : Fin (Q + 1)) : Fin (Q + 1)) =
        (⟨x.val % (Q + 1), Nat.mod_lt _ (Nat.succ_pos Q)⟩ :
          Fin (Q + 1)) + 1
      congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt x.isLt]

/-- The one-based complete interval coordinates and residue coordinates on a
tuple pair are equivalent. -/
noncomputable def vinogradovCompleteResiduePairEquiv
    (Q s : ℕ) [NeZero Q] :
    ((Fin s → Fin Q) × (Fin s → Fin Q)) ≃
      ((Fin s → ZMod Q) × (Fin s → ZMod Q)) :=
  Equiv.prodCongr
    (Equiv.piCongrRight fun _ ↦
      vinogradovCompleteResidueEquiv Q)
    (Equiv.piCongrRight fun _ ↦
      vinogradovCompleteResidueEquiv Q)

/-- Counting complete residue-ring solutions agrees with the existing
normalized finite Vinogradov solution count. -/
theorem card_vinogradovResidueSolutionPairSet
    (Q d s : ℕ) [NeZero Q] :
    (vinogradovResidueSolutionPairSet Q d s).card =
      vinogradovSolutionCountMod Q d s Q := by
  classical
  let e := vinogradovCompleteResiduePairEquiv Q s
  have hcard :
      (vinogradovSolutionPairSetMod Q d s Q).card =
        (vinogradovResidueSolutionPairSet Q d s).card := by
    apply Finset.card_equiv e
    intro xy
    rw [mem_vinogradovSolutionPairSetMod_iff,
      mem_vinogradovResidueSolutionPairSet_iff]
    have hx : (e xy).1 =
        (fun i ↦ ((xy.1 i).val : ZMod Q) + 1) := by
      funext i
      simpa [e, vinogradovCompleteResiduePairEquiv,
        vinogradovCompleteResidueEquiv_apply]
    have hy : (e xy).2 =
        (fun i ↦ ((xy.2 i).val : ZMod Q) + 1) := by
      funext i
      simpa [e, vinogradovCompleteResiduePairEquiv,
        vinogradovCompleteResidueEquiv_apply]
    rw [hx, hy]
    exact isVinogradovSolutionMod_iff_residueSolution Q d s xy.1 xy.2
  rw [← hcard, card_vinogradovSolutionPairSetMod]

/-- Main tuple pairs whose affine coordinates satisfy the degree-`r`
Vinogradov system at the residual far scale. -/
def VinogradovMixedMainFarScalePairMem
    (p a b k r X gamma : ℕ) (xi : ℤ)
    (xy : (Fin r → Fin X) × (Fin r → Fin X)) : Prop :=
  ∃ x' y' : Fin r → ℤ,
    vinogradovFinTupleInt xy.1 =
        (fun i ↦ xi + (p : ℤ) ^ a * x' i) ∧
      vinogradovFinTupleInt xy.2 =
        (fun i ↦ xi + (p : ℤ) ^ a * y' i) ∧
      IsVinogradovSolutionIntMod
        (p ^ vinogradovFarScale k r a b gamma) r r x' y'

/-- The finite main-pair surface left after the mixed system has eliminated
the free restricted tail. -/
noncomputable def vinogradovMixedMainFarScalePairSet
    (p a b k r X gamma : ℕ) (xi : ℤ) :
    Finset ((Fin r → Fin X) × (Fin r → Fin X)) := by
  classical
  exact Finset.univ.filter
    (VinogradovMixedMainFarScalePairMem p a b k r X gamma xi)

theorem mem_vinogradovMixedMainFarScalePairSet_iff
    (p a b k r X gamma : ℕ) (xi : ℤ)
    (xy : (Fin r → Fin X) × (Fin r → Fin X)) :
    xy ∈ vinogradovMixedMainFarScalePairSet p a b k r X gamma xi ↔
      VinogradovMixedMainFarScalePairMem p a b k r X gamma xi xy := by
  classical
  simp [vinogradovMixedMainFarScalePairSet]

/-- A canonical choice of the integral affine coordinates certified by
membership in the far-scale main-pair surface. -/
noncomputable def vinogradovMixedMainAffineCoordinatePair
    (p a b k r X gamma : ℕ) (xi : ℤ)
    (xy : (Fin r → Fin X) × (Fin r → Fin X)) :
    (Fin r → ℤ) × (Fin r → ℤ) := by
  classical
  by_cases h : VinogradovMixedMainFarScalePairMem
      p a b k r X gamma xi xy
  · exact ⟨Classical.choose h,
      Classical.choose (Classical.choose_spec h)⟩
  · exact ⟨0, 0⟩

theorem vinogradovMixedMainAffineCoordinatePair_spec
    (p a b k r X gamma : ℕ) (xi : ℤ)
    (xy : (Fin r → Fin X) × (Fin r → Fin X))
    (h : VinogradovMixedMainFarScalePairMem
      p a b k r X gamma xi xy) :
    vinogradovFinTupleInt xy.1 =
        (fun i ↦ xi + (p : ℤ) ^ a *
          (vinogradovMixedMainAffineCoordinatePair
            p a b k r X gamma xi xy).1 i) ∧
      vinogradovFinTupleInt xy.2 =
        (fun i ↦ xi + (p : ℤ) ^ a *
          (vinogradovMixedMainAffineCoordinatePair
            p a b k r X gamma xi xy).2 i) ∧
      IsVinogradovSolutionIntMod
        (p ^ vinogradovFarScale k r a b gamma) r r
        (vinogradovMixedMainAffineCoordinatePair
          p a b k r X gamma xi xy).1
        (vinogradovMixedMainAffineCoordinatePair
          p a b k r X gamma xi xy).2 := by
  classical
  rw [vinogradovMixedMainAffineCoordinatePair]
  simp only [dif_pos h]
  exact Classical.choose_spec (Classical.choose_spec h)

/-- Reduce the chosen affine coordinates modulo the residual far scale. -/
noncomputable def vinogradovMixedMainFarScaleResidueMap
    (p a b k r X gamma : ℕ) [Fact p.Prime] (xi : ℤ)
    (xy : (Fin r → Fin X) × (Fin r → Fin X)) :
    (Fin r → ZMod (p ^ vinogradovFarScale k r a b gamma)) ×
      (Fin r → ZMod (p ^ vinogradovFarScale k r a b gamma)) :=
  let c := vinogradovMixedMainAffineCoordinatePair
    p a b k r X gamma xi xy
  ⟨fun i ↦ c.1 i, fun i ↦ c.2 i⟩

/-- The residue encoding of a far-scale main pair solves the complete
degree-`r` Vinogradov system over the residual ring. -/
theorem vinogradovMixedMainFarScaleResidueMap_mem
    (p a b k r X gamma : ℕ) [Fact p.Prime] (xi : ℤ)
    (xy : (Fin r → Fin X) × (Fin r → Fin X))
    (hxy : xy ∈ vinogradovMixedMainFarScalePairSet
      p a b k r X gamma xi) :
    vinogradovMixedMainFarScaleResidueMap p a b k r X gamma xi xy ∈
      vinogradovResidueSolutionPairSet
        (p ^ vinogradovFarScale k r a b gamma) r r := by
  letI : NeZero (p ^ vinogradovFarScale k r a b gamma) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [mem_vinogradovResidueSolutionPairSet_iff]
  have hmem := (mem_vinogradovMixedMainFarScalePairSet_iff
    p a b k r X gamma xi xy).mp hxy
  have hspec := vinogradovMixedMainAffineCoordinatePair_spec
    p a b k r X gamma xi xy hmem
  intro j
  have hcast := (ZMod.intCast_eq_intCast_iff
    (vinogradovPowerSumInt
      (vinogradovMixedMainAffineCoordinatePair
        p a b k r X gamma xi xy).1 j)
    (vinogradovPowerSumInt
      (vinogradovMixedMainAffineCoordinatePair
        p a b k r X gamma xi xy).2 j)
    (p ^ vinogradovFarScale k r a b gamma)).mpr (hspec.2.2 j)
  simpa only [vinogradovMixedMainFarScaleResidueMap,
    vinogradovResiduePowerSum, vinogradovPowerSumInt,
    Int.cast_sum, Int.cast_pow] using hcast

/-- Affine coordinates are injective modulo `Q` on an interval whose length
does not exceed the combined scale `p^a Q`. -/
theorem vinogradovFinTuple_eq_of_affineCoordinates_modEq
    (p a r X Q : ℕ) (xi : ℤ)
    (x y : Fin r → Fin X) (u v : Fin r → ℤ)
    (hx : vinogradovFinTupleInt x =
      (fun i ↦ xi + (p : ℤ) ^ a * u i))
    (hy : vinogradovFinTupleInt y =
      (fun i ↦ xi + (p : ℤ) ^ a * v i))
    (hmod : ∀ i, Int.ModEq (Q : ℤ) (u i) (v i))
    (hscale : X ≤ p ^ a * Q) :
    x = y := by
  funext i
  apply Fin.ext
  have hscaled : Int.ModEq ((p : ℤ) ^ a * (Q : ℤ))
      ((p : ℤ) ^ a * u i) ((p : ℤ) ^ a * v i) :=
    (hmod i).mul_left'
  have hshift := hscaled.add_left xi
  have hraw : Int.ModEq ((p ^ a * Q : ℕ) : ℤ)
      (vinogradovFinTupleInt x i) (vinogradovFinTupleInt y i) := by
    rw [congrFun hx i, congrFun hy i]
    simpa only [Nat.cast_mul, Nat.cast_pow] using hshift
  have hval : Int.ModEq ((p ^ a * Q : ℕ) : ℤ)
      ((x i).val : ℤ) ((y i).val : ℤ) := by
    have hsub := hraw.add_right (-1)
    simpa only [vinogradovFinTupleInt, Nat.cast_add, Nat.cast_one,
      add_neg_cancel_right] using hsub
  have hnat : Nat.ModEq (p ^ a * Q) (x i).val (y i).val := by
    rw [Nat.modEq_iff_dvd]
    exact hval.dvd
  exact hnat.eq_of_lt_of_lt
    ((x i).isLt.trans_le hscale) ((y i).isLt.trans_le hscale)

/-- Under the no-wrap scale condition, reducing the affine coordinates is
injective on the far-scale main-pair surface. -/
theorem vinogradovMixedMainFarScaleResidueMap_injOn
    (p a b k r X gamma : ℕ) [Fact p.Prime] (xi : ℤ)
    (hscale : X ≤ p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    Set.InjOn
      (vinogradovMixedMainFarScaleResidueMap
        p a b k r X gamma xi)
      (vinogradovMixedMainFarScalePairSet
        p a b k r X gamma xi : Set
          ((Fin r → Fin X) × (Fin r → Fin X))) := by
  intro xy hxy zw hzw heq
  have hxmem := (mem_vinogradovMixedMainFarScalePairSet_iff
    p a b k r X gamma xi xy).mp hxy
  have hwmem := (mem_vinogradovMixedMainFarScalePairSet_iff
    p a b k r X gamma xi zw).mp hzw
  have hxspec := vinogradovMixedMainAffineCoordinatePair_spec
    p a b k r X gamma xi xy hxmem
  have hwspec := vinogradovMixedMainAffineCoordinatePair_spec
    p a b k r X gamma xi zw hwmem
  apply Prod.ext
  · apply vinogradovFinTuple_eq_of_affineCoordinates_modEq
      p a r X (p ^ vinogradovFarScale k r a b gamma) xi
      xy.1 zw.1
      (vinogradovMixedMainAffineCoordinatePair
        p a b k r X gamma xi xy).1
      (vinogradovMixedMainAffineCoordinatePair
        p a b k r X gamma xi zw).1
      hxspec.1 hwspec.1
    · intro i
      apply (ZMod.intCast_eq_intCast_iff _ _
        (p ^ vinogradovFarScale k r a b gamma)).mp
      have hi := congrFun (congrArg Prod.fst heq) i
      exact hi
    · exact hscale
  · apply vinogradovFinTuple_eq_of_affineCoordinates_modEq
      p a r X (p ^ vinogradovFarScale k r a b gamma) xi
      xy.2 zw.2
      (vinogradovMixedMainAffineCoordinatePair
        p a b k r X gamma xi xy).2
      (vinogradovMixedMainAffineCoordinatePair
        p a b k r X gamma xi zw).2
      hxspec.2.1 hwspec.2.1
    · intro i
      apply (ZMod.intCast_eq_intCast_iff _ _
        (p ^ vinogradovFarScale k r a b gamma)).mp
      have hi := congrFun (congrArg Prod.snd heq) i
      exact hi
    · exact hscale

/-- The far-scale main-pair count is controlled by the standard complete
Vinogradov solution count at that residual modulus. -/
theorem card_vinogradovMixedMainFarScalePairSet_le_solutionCount
    (p a b k r X gamma : ℕ) [Fact p.Prime] (xi : ℤ)
    (hscale : X ≤ p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    (vinogradovMixedMainFarScalePairSet
        p a b k r X gamma xi).card ≤
      vinogradovSolutionCountMod
        (p ^ vinogradovFarScale k r a b gamma) r r
          (p ^ vinogradovFarScale k r a b gamma) := by
  letI : NeZero (p ^ vinogradovFarScale k r a b gamma) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  calc
    (vinogradovMixedMainFarScalePairSet
        p a b k r X gamma xi).card ≤
      (vinogradovResidueSolutionPairSet
        (p ^ vinogradovFarScale k r a b gamma) r r).card :=
      Finset.card_le_card_of_injOn
        (vinogradovMixedMainFarScaleResidueMap
          p a b k r X gamma xi)
        (fun _ h ↦ vinogradovMixedMainFarScaleResidueMap_mem
          p a b k r X gamma xi _ h)
        (vinogradovMixedMainFarScaleResidueMap_injOn
          p a b k r X gamma xi hscale)
    _ = vinogradovSolutionCountMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma) :=
      card_vinogradovResidueSolutionPairSet _ _ _

/-- Every modular mixed conditioned solution consists of a far-scale main
pair and an otherwise unrestricted tail pair.  This is the set-level first
step of the efficient-congruencing recurrence. -/
theorem vinogradovMixedModConditionedSolutionSet_subset_mainFarScale_product
    (p a b k r t X Y gamma : ℕ) [Fact p.Prime]
    (xi eta omega : ℤ)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcenter : xi - eta = omega * (p : ℤ) ^ gamma)
    (homega : IsCoprime (p : ℤ) omega) :
    vinogradovMixedModConditionedSolutionSet
        p ((k - r + 1) * b) a b k r t X Y xi eta ⊆
      (vinogradovMixedMainFarScalePairSet p a b k r X gamma xi).product
        (Finset.univ : Finset ((Fin t → Fin Y) × (Fin t → Fin Y))) := by
  classical
  intro z hz
  apply Finset.mem_product.mpr
  constructor
  · rw [mem_vinogradovMixedMainFarScalePairSet_iff]
    have hmem :=
      (mem_vinogradovMixedModConditionedSolutionSet_iff
        p ((k - r + 1) * b) a b k r t X Y xi eta z).mp hz
    obtain ⟨x', y', hx', hy', hfar⟩ :=
      hmem.exists_farScale_powerSumCongruences
        hrk hkp hb hgammaa hbudget htail hcenter homega
    refine ⟨x', y', hx', hy', ?_⟩
    intro j
    have hj := (hfar j).add_right (vinogradovPowerSumInt y' j)
    simpa only [vinogradovPowerSumDifferenceInt, vinogradovPowerSumInt,
      sub_add_cancel, zero_add] using hj
  · simp

/-- The mixed conditioned solution count is bounded by the number of free
tail pairs times the far-scale main-pair count. -/
theorem card_vinogradovMixedModConditionedSolutionSet_le_mainFarScale
    (p a b k r t X Y gamma : ℕ) [Fact p.Prime]
    (xi eta omega : ℤ)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcenter : xi - eta = omega * (p : ℤ) ^ gamma)
    (homega : IsCoprime (p : ℤ) omega) :
    (vinogradovMixedModConditionedSolutionSet
        p ((k - r + 1) * b) a b k r t X Y xi eta).card ≤
      (vinogradovMixedMainFarScalePairSet
        p a b k r X gamma xi).card * Y ^ (2 * t) := by
  calc
    (vinogradovMixedModConditionedSolutionSet
        p ((k - r + 1) * b) a b k r t X Y xi eta).card ≤
      ((vinogradovMixedMainFarScalePairSet p a b k r X gamma xi).product
        (Finset.univ : Finset ((Fin t → Fin Y) × (Fin t → Fin Y)))).card :=
      Finset.card_le_card
        (vinogradovMixedModConditionedSolutionSet_subset_mainFarScale_product
          p a b k r t X Y gamma xi eta omega hrk hkp hb hgammaa
            hbudget htail hcenter homega)
    _ = (vinogradovMixedMainFarScalePairSet
          p a b k r X gamma xi).card * Y ^ (2 * t) := by
      change
        ((vinogradovMixedMainFarScalePairSet p a b k r X gamma xi) ×ˢ
          (Finset.univ : Finset ((Fin t → Fin Y) × (Fin t → Fin Y)))).card = _
      rw [Finset.card_product]
      congr 1
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin]
      rw [← pow_add]
      congr 1
      omega

/-- Combining far-scale elimination with the no-wrap residue encoding bounds
the mixed solution count by a standard complete Vinogradov solution count. -/
theorem card_vinogradovMixedModConditionedSolutionSet_le_solutionCount
    (p a b k r t X Y gamma : ℕ) [Fact p.Prime]
    (xi eta omega : ℤ)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcenter : xi - eta = omega * (p : ℤ) ^ gamma)
    (homega : IsCoprime (p : ℤ) omega)
    (hscale : X ≤ p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    (vinogradovMixedModConditionedSolutionSet
        p ((k - r + 1) * b) a b k r t X Y xi eta).card ≤
      vinogradovSolutionCountMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma) *
        Y ^ (2 * t) := by
  calc
    (vinogradovMixedModConditionedSolutionSet
        p ((k - r + 1) * b) a b k r t X Y xi eta).card ≤
      (vinogradovMixedMainFarScalePairSet
        p a b k r X gamma xi).card * Y ^ (2 * t) :=
      card_vinogradovMixedModConditionedSolutionSet_le_mainFarScale
        p a b k r t X Y gamma xi eta omega hrk hkp hb hgammaa
          hbudget htail hcenter homega
    _ ≤ vinogradovSolutionCountMod
          (p ^ vinogradovFarScale k r a b gamma) r r
            (p ^ vinogradovFarScale k r a b gamma) * Y ^ (2 * t) :=
      Nat.mul_le_mul_right (Y ^ (2 * t))
        (card_vinogradovMixedMainFarScalePairSet_le_solutionCount
          p a b k r X gamma xi hscale)

/-- The product-form mixed Fourier moment obeys the same first recurrence:
the restricted tail contributes only its full `Y^(2t)` cardinality, while
the main pair has acquired the residual far-scale Vinogradov equations. -/
theorem norm_normalizedVinogradovMixedModConditionedMoment_le_mainFarScale
    (p a b k r t X Y gamma : ℕ) [Fact p.Prime]
    (xi eta omega : ℤ)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcenter : xi - eta = omega * (p : ℤ) ^ gamma)
    (homega : IsCoprime (p : ℤ) omega) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t X Y xi eta‖ ≤
      (((vinogradovMixedMainFarScalePairSet
          p a b k r X gamma xi).card * Y ^ (2 * t) : ℕ) : ℝ) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [normalizedVinogradovMixedModConditionedMoment_eq_solutionSetCard]
  norm_cast
  exact card_vinogradovMixedModConditionedSolutionSet_le_mainFarScale
    p a b k r t X Y gamma xi eta omega hrk hkp hb hgammaa
      hbudget htail hcenter homega

/-- First effective mixed-moment recurrence: after far-scale elimination and
under the no-wrap condition, the mixed conditioned moment is bounded by the
standard complete degree-`r` moment at the residual modulus, times the full
cardinality of the restricted tail pair. -/
theorem norm_normalizedVinogradovMixedModConditionedMoment_le_farScaleMoment
    (p a b k r t X Y gamma : ℕ) [Fact p.Prime]
    (xi eta omega : ℤ)
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b) (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcenter : xi - eta = omega * (p : ℤ) ^ gamma)
    (homega : IsCoprime (p : ℤ) omega)
    (hscale : X ≤ p ^ a * p ^ vinogradovFarScale k r a b gamma) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t X Y xi eta‖ ≤
      ‖normalizedVinogradovMomentMod
        (p ^ vinogradovFarScale k r a b gamma) r r
          (p ^ vinogradovFarScale k r a b gamma)‖ *
        (Y ^ (2 * t) : ℝ) := by
  letI : NeZero (p ^ ((k - r + 1) * b)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ vinogradovFarScale k r a b gamma) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [normalizedVinogradovMixedModConditionedMoment_eq_solutionSetCard,
    normalizedVinogradovMomentMod_eq_solutionCount]
  norm_cast
  exact card_vinogradovMixedModConditionedSolutionSet_le_solutionCount
    p a b k r t X Y gamma xi eta omega hrk hkp hb hgammaa
      hbudget htail hcenter homega hscale

/-- The explicit one-block prime-power strata bound used to terminate the
first mixed-moment recurrence. -/
def vinogradovDiagonalPrimePowerStrataBound (p r n : ℕ) : ℕ :=
  (p ^ r - p.descFactorial r) * p ^ r * (p ^ (2 * r)) ^ n +
    (p ^ r - (p ^ r - p.descFactorial r)) *
      (p ^ r * (p ^ r) ^ n)

/-- The first mixed-moment recurrence terminates unconditionally at the
existing prime-power rank stratification when the residual exponent is
written as `n+1`.  This is explicit but is not yet the optimal VMVT bound. -/
theorem norm_normalizedVinogradovMixedModConditionedMoment_le_primePowerStrata
    (p a b k r t X Y gamma n : ℕ) [Fact p.Prime]
    (xi eta omega : ℤ)
    (hr : 0 < r) (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hgammaa : gamma ≤ a)
    (hbudget : gamma * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (hcenter : xi - eta = omega * (p : ℤ) ^ gamma)
    (homega : IsCoprime (p : ℤ) omega)
    (hscale : X ≤ p ^ a * p ^ vinogradovFarScale k r a b gamma)
    (hfar : vinogradovFarScale k r a b gamma = n + 1) :
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t X Y xi eta‖ ≤
      (vinogradovDiagonalPrimePowerStrataBound p r n : ℝ) *
        (Y ^ (2 * t) : ℝ) := by
  have hrec :=
    norm_normalizedVinogradovMixedModConditionedMoment_le_farScaleMoment
      p a b k r t X Y gamma xi eta omega hrk hkp hb hgammaa
        hbudget htail hcenter homega hscale
  have hstrata :=
    norm_normalizedVinogradovMomentMod_primePowerMultiBlock_le_strata
      p r 0 1 n hr (hrk.trans_lt hkp)
  have hstrata' :
      ‖normalizedVinogradovMomentMod
        (p ^ (n + 1)) r r (p ^ (n + 1))‖ ≤
          (vinogradovDiagonalPrimePowerStrataBound p r n : ℝ) := by
    simpa [vinogradovDiagonalPrimePowerStrataBound] using hstrata
  calc
    ‖normalizedVinogradovMixedModConditionedMoment
        p ((k - r + 1) * b) a b k r t X Y xi eta‖ ≤
      ‖normalizedVinogradovMomentMod
        (p ^ vinogradovFarScale k r a b gamma) r r
          (p ^ vinogradovFarScale k r a b gamma)‖ *
        (Y ^ (2 * t) : ℝ) := hrec
    _ = ‖normalizedVinogradovMomentMod
          (p ^ (n + 1)) r r (p ^ (n + 1))‖ *
        (Y ^ (2 * t) : ℝ) := by rw [hfar]
    _ ≤ (vinogradovDiagonalPrimePowerStrataBound p r n : ℝ) *
        (Y ^ (2 * t) : ℝ) :=
      mul_le_mul_of_nonneg_right hstrata' (by positivity)

end

end ZeroFreeRegion.VinogradovKorobov
