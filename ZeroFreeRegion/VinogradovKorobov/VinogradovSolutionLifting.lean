import ZeroFreeRegion.VinogradovKorobov.VinogradovSolutionStrata

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- The `ZMod` formulation of the modular Vinogradov system is equivalent to
integer power-sum congruences for the representatives `x_i + 1`. -/
theorem isVinogradovSolutionMod_iff_powerSumInt_modEq
    (Q k s X : ℕ) (x y : Fin s → Fin X) :
    IsVinogradovSolutionMod Q k s X x y ↔
      ∀ j : Fin k,
        vinogradovPowerSumInt
            (fun i ↦ (((x i).val + 1 : ℕ) : ℤ)) j ≡
          vinogradovPowerSumInt
            (fun i ↦ (((y i).val + 1 : ℕ) : ℤ)) j [ZMOD Q] := by
  constructor
  · intro h j
    apply (ZMod.intCast_eq_intCast_iff _ _ Q).mp
    simpa [vinogradovPowerSumInt, vinogradovPowerSumMod] using h j
  · intro h j
    have hj := (ZMod.intCast_eq_intCast_iff _ _ Q).mpr (h j)
    simpa [vinogradovPowerSumInt, vinogradovPowerSumMod] using hj

/-- Corrections modulo `p` to a nonsingular head block which realize an
arbitrary prescribed vector of power sums at the next prime-power level. -/
noncomputable def vinogradovHeadCorrectionSet
    (p k n : ℕ) [Fact p.Prime] (x target : Fin k → ℤ) :
    Finset (Fin k → ZMod p) := by
  classical
  exact Finset.univ.filter fun u : Fin k → ZMod p ↦
    ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (u i).val) j ≡
        target j [ZMOD (p : ℤ) ^ (n + 1) * p]

/-- Membership unfolds to the prescribed next-level power-sum congruences. -/
theorem mem_vinogradovHeadCorrectionSet_iff
    (p k n : ℕ) [Fact p.Prime] (x target : Fin k → ℤ)
    (u : Fin k → ZMod p) :
    u ∈ vinogradovHeadCorrectionSet p k n x target ↔
      ∀ j : Fin k,
        vinogradovPowerSumInt
            (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (u i).val) j ≡
          target j [ZMOD (p : ℤ) ^ (n + 1) * p] := by
  classical
  simp [vinogradovHeadCorrectionSet]

/-- At a nonsingular base block, an arbitrary next-level target has at most
one correction class modulo `p`. -/
theorem card_vinogradovHeadCorrectionSet_le_one
    (p k n : ℕ) [Fact p.Prime] (hkp : k < p)
    (x target : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p))) :
    (vinogradovHeadCorrectionSet p k n x target).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.mpr
  intro u v hu hv
  apply funext
  intro i
  have hq0 : (p : ℤ) ^ (n + 1) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpq : (p : ℤ) ∣ (p : ℤ) ^ (n + 1) := by
    refine ⟨(p : ℤ) ^ n, ?_⟩
    rw [pow_succ]
    ring
  have hpower : ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (u i).val) j ≡
        vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (v i).val) j
          [ZMOD (p : ℤ) ^ (n + 1) * p] := by
    intro j
    exact
      ((mem_vinogradovHeadCorrectionSet_iff p k n x target u).mp hu j).trans
        ((mem_vinogradovHeadCorrectionSet_iff p k n x target v).mp hv j).symm
  have hi :=
    vinogradovPowerSumInt_affine_corrections_unique_mod_prime_at_scale
      p k hkp ((p : ℤ) ^ (n + 1)) hq0 hpq x
      (fun i ↦ ((u i).val : ℤ)) (fun i ↦ ((v i).val : ℤ)) hx hpower i
  have hiz :=
    (ZMod.intCast_eq_intCast_iff ((u i).val : ℤ) ((v i).val : ℤ) p).mpr hi
  simpa using hiz

/-- The correction variables not controlled by the nonsingular `k`-block:
the remaining `r` left coordinates and all `k+r` right coordinates. -/
abbrev vinogradovFreeCorrectionData (p k r : ℕ) :=
  (Fin r → ZMod p) × (Fin (k + r) → ZMod p)

/-- There are `p^(k+2r)` choices of free correction data. -/
theorem card_vinogradovFreeCorrectionData
    (p k r : ℕ) [Fact p.Prime] :
    Fintype.card (vinogradovFreeCorrectionData p k r) =
      p ^ (k + 2 * r) := by
  classical
  rw [Fintype.card_prod]
  simp only [Fintype.card_pi_const, ZMod.card]
  rw [← pow_add]
  congr 1
  omega

/-- A family of head-correction fibers parameterized by all free correction
variables. -/
noncomputable def vinogradovParameterizedCorrectionSet
    (p k r n : ℕ) [Fact p.Prime] (x : Fin k → ℤ)
    (target : vinogradovFreeCorrectionData p k r → Fin k → ℤ) :
    Finset (Σ _ : vinogradovFreeCorrectionData p k r,
      Fin k → ZMod p) := by
  classical
  exact Finset.univ.sigma fun free ↦
    vinogradovHeadCorrectionSet p k n x (target free)

/-- Summing singleton head fibers over all free data gives the expected
`p^(2s-k) = p^(k+2r)` one-step lifting bound. -/
theorem card_vinogradovParameterizedCorrectionSet_le
    (p k r n : ℕ) [Fact p.Prime] (hkp : k < p)
    (x : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p)))
    (target : vinogradovFreeCorrectionData p k r → Fin k → ℤ) :
    (vinogradovParameterizedCorrectionSet p k r n x target).card ≤
      p ^ (k + 2 * r) := by
  classical
  rw [vinogradovParameterizedCorrectionSet, Finset.card_sigma]
  calc
    (∑ free : vinogradovFreeCorrectionData p k r,
        (vinogradovHeadCorrectionSet p k n x (target free)).card) ≤
        ∑ _free : vinogradovFreeCorrectionData p k r, 1 := by
      apply Finset.sum_le_sum
      intro free _
      exact card_vinogradovHeadCorrectionSet_le_one
        p k n hkp x (target free) hx
    _ = Fintype.card (vinogradovFreeCorrectionData p k r) := by simp
    _ = p ^ (k + 2 * r) := card_vinogradovFreeCorrectionData p k r

/-- Join a head block and a tail block into one tuple. -/
def vinogradovJoinTuple {α : Type*} {k r : ℕ}
    (head : Fin k → α) (tail : Fin r → α) : Fin (k + r) → α :=
  fun i ↦ Sum.elim head tail (finSumFinEquiv.symm i)

@[simp]
theorem vinogradovJoinTuple_castAdd {α : Type*} {k r : ℕ}
    (head : Fin k → α) (tail : Fin r → α) (i : Fin k) :
    vinogradovJoinTuple head tail (Fin.castAdd r i) = head i := by
  simp [vinogradovJoinTuple]

@[simp]
theorem vinogradovJoinTuple_natAdd {α : Type*} {k r : ℕ}
    (head : Fin k → α) (tail : Fin r → α) (i : Fin r) :
    vinogradovJoinTuple head tail (Fin.natAdd k i) = tail i := by
  simp [vinogradovJoinTuple]

/-- Power sums split additively across the selected head and free tail
coordinates. -/
theorem vinogradovPowerSumInt_joinTuple {d k r : ℕ}
    (head : Fin k → ℤ) (tail : Fin r → ℤ) (j : Fin d) :
    vinogradovPowerSumInt (vinogradovJoinTuple head tail) j =
      vinogradovPowerSumInt head j + vinogradovPowerSumInt tail j := by
  unfold vinogradovPowerSumInt
  rw [← finSumFinEquiv.sum_comp
    (fun i ↦ vinogradovJoinTuple head tail i ^ (j.val + 1))]
  rw [Fintype.sum_sum_type]
  simp [vinogradovJoinTuple]

/-- For fixed free corrections, the right-hand power sum minus the corrected
left tail is the target imposed on the nonsingular head block. -/
def vinogradovSolutionCorrectionTarget
    (p k r n : ℕ) [Fact p.Prime]
    (x y : Fin (k + r) → ℤ)
    (free : vinogradovFreeCorrectionData p k r) : Fin k → ℤ :=
  fun j ↦
    vinogradovPowerSumInt
        (fun i ↦ y i + (p : ℤ) ^ (n + 1) * (free.2 i).val) j -
      vinogradovPowerSumInt
        (fun i ↦ x (Fin.natAdd k i) +
          (p : ℤ) ^ (n + 1) * (free.1 i).val) j

/-- All one-step corrections of a pair of length-`k+r` tuples, represented by
the free left-tail and right corrections together with the controlled left
head correction. -/
noncomputable def vinogradovSolutionCorrectionSet
    (p k r n : ℕ) [Fact p.Prime]
    (x y : Fin (k + r) → ℤ) :
    Finset (Σ _ : vinogradovFreeCorrectionData p k r,
      Fin k → ZMod p) :=
  vinogradovParameterizedCorrectionSet p k r n
    (fun i ↦ x (Fin.castAdd r i))
    (vinogradovSolutionCorrectionTarget p k r n x y)

/-- Membership is exactly the complete next-level Vinogradov system after
joining the controlled head correction to the free tail correction. -/
theorem mem_vinogradovSolutionCorrectionSet_iff
    (p k r n : ℕ) [Fact p.Prime]
    (x y : Fin (k + r) → ℤ)
    (z : Σ _ : vinogradovFreeCorrectionData p k r,
      Fin k → ZMod p) :
    z ∈ vinogradovSolutionCorrectionSet p k r n x y ↔
      ∀ j : Fin k,
        vinogradovPowerSumInt
            (vinogradovJoinTuple
              (fun i ↦ x (Fin.castAdd r i) +
                (p : ℤ) ^ (n + 1) * (z.2 i).val)
              (fun i ↦ x (Fin.natAdd k i) +
                (p : ℤ) ^ (n + 1) * (z.1.1 i).val)) j ≡
          vinogradovPowerSumInt
            (fun i ↦ y i +
              (p : ℤ) ^ (n + 1) * (z.1.2 i).val) j
            [ZMOD (p : ℤ) ^ (n + 1) * p] := by
  classical
  simp only [vinogradovSolutionCorrectionSet,
    vinogradovParameterizedCorrectionSet, Finset.mem_sigma,
    Finset.mem_univ, true_and,
    mem_vinogradovHeadCorrectionSet_iff]
  constructor
  · intro h j
    rw [vinogradovPowerSumInt_joinTuple]
    have := (h j).add_right
      (vinogradovPowerSumInt
        (fun i ↦ x (Fin.natAdd k i) +
          (p : ℤ) ^ (n + 1) * (z.1.1 i).val) j)
    simpa [vinogradovSolutionCorrectionTarget] using this
  · intro h j
    have hj := h j
    rw [vinogradovPowerSumInt_joinTuple] at hj
    have := hj.add_right
      (-vinogradovPowerSumInt
        (fun i ↦ x (Fin.natAdd k i) +
          (p : ℤ) ^ (n + 1) * (z.1.1 i).val) j)
    simpa [vinogradovSolutionCorrectionTarget] using this

/-- A nonsingular left head block leaves at most `p^(k+2r)` complete
one-step corrections of the pair. -/
theorem card_vinogradovSolutionCorrectionSet_le
    (p k r n : ℕ) [Fact p.Prime] (hkp : k < p)
    (x y : Fin (k + r) → ℤ)
    (hx : Function.Injective
      (fun i : Fin k ↦ (x (Fin.castAdd r i) : ZMod p))) :
    (vinogradovSolutionCorrectionSet p k r n x y).card ≤
      p ^ (k + 2 * r) := by
  exact card_vinogradovParameterizedCorrectionSet_le p k r n hkp
    (fun i ↦ x (Fin.castAdd r i)) hx
    (vinogradovSolutionCorrectionTarget p k r n x y)

/-- Solutions modulo `p^(n+1)` whose selected left block remains
nonsingular after reduction modulo `p`. -/
noncomputable def vinogradovPrimePowerNonsingularSolutionSet
    (p k r n : ℕ) [Fact p.Prime] :
    Finset
      ((Fin (k + r) → Fin (p ^ (n + 1))) ×
        (Fin (k + r) → Fin (p ^ (n + 1)))) := by
  classical
  exact
    (vinogradovSolutionPairSetMod
      (p ^ (n + 1)) k (k + r) (p ^ (n + 1))).filter fun xy ↦
        Function.Injective fun i : Fin k ↦
          (((xy.1 (Fin.castAdd r i)).val + 1 : ℕ) : ZMod p)

/-- Membership combines the level-`n+1` Vinogradov equations with
nonsingularity of the selected left block modulo `p`. -/
theorem mem_vinogradovPrimePowerNonsingularSolutionSet_iff
    (p k r n : ℕ) [Fact p.Prime]
    (x y : Fin (k + r) → Fin (p ^ (n + 1))) :
    (x, y) ∈ vinogradovPrimePowerNonsingularSolutionSet p k r n ↔
      Function.Injective (fun i : Fin k ↦
        (((x (Fin.castAdd r i)).val + 1 : ℕ) : ZMod p)) ∧
      IsVinogradovSolutionMod
        (p ^ (n + 1)) k (k + r) (p ^ (n + 1)) x y := by
  classical
  simp [vinogradovPrimePowerNonsingularSolutionSet,
    mem_vinogradovSolutionPairSetMod_iff, and_comm]

/-- The total one-step lift space above all nonsingular solutions at level
`p^(n+1)`.  Each fiber records the free and controlled corrections separately. -/
noncomputable def vinogradovPrimePowerNonsingularLiftSet
    (p k r n : ℕ) [Fact p.Prime] :
    Finset
      (Σ _ :
          ((Fin (k + r) → Fin (p ^ (n + 1))) ×
            (Fin (k + r) → Fin (p ^ (n + 1)))),
        Σ _ : vinogradovFreeCorrectionData p k r,
          Fin k → ZMod p) := by
  classical
  exact
    (vinogradovPrimePowerNonsingularSolutionSet p k r n).sigma fun xy ↦
      vinogradovSolutionCorrectionSet p k r n
        (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ))
        (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ))

/-- Summing the `p^(k+2r)` fiber bound over all nonsingular base solutions
gives the one-step prime-power lifting recurrence. -/
theorem card_vinogradovPrimePowerNonsingularLiftSet_le
    (p k r n : ℕ) [Fact p.Prime] (hkp : k < p) :
    (vinogradovPrimePowerNonsingularLiftSet p k r n).card ≤
      (vinogradovPrimePowerNonsingularSolutionSet p k r n).card *
        p ^ (k + 2 * r) := by
  classical
  rw [vinogradovPrimePowerNonsingularLiftSet, Finset.card_sigma]
  calc
    (∑ xy ∈ vinogradovPrimePowerNonsingularSolutionSet p k r n,
        (vinogradovSolutionCorrectionSet p k r n
          (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ))
          (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ))).card) ≤
        ∑ _xy ∈ vinogradovPrimePowerNonsingularSolutionSet p k r n,
          p ^ (k + 2 * r) := by
      apply Finset.sum_le_sum
      intro xy hxy
      have hx :=
        (mem_vinogradovPrimePowerNonsingularSolutionSet_iff
          p k r n xy.1 xy.2).mp hxy |>.1
      have hcast : Function.Injective
          (fun i : Fin k ↦
            (((((xy.1 (Fin.castAdd r i)).val + 1 : ℕ) : ℤ)) : ZMod p)) := by
        intro i j hij
        apply hx
        simpa using hij
      exact card_vinogradovSolutionCorrectionSet_le p k r n hkp
        (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ))
        (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ)) hcast
    _ = (vinogradovPrimePowerNonsingularSolutionSet p k r n).card *
        p ^ (k + 2 * r) := by simp

/-- Base-`p` digit decomposition between one coordinate modulo `p^(n+2)`
and a coordinate modulo `p^(n+1)` together with one new residue digit. -/
noncomputable def vinogradovPrimePowerDigitEquiv
    (p n : ℕ) [Fact p.Prime] :
    Fin (p ^ (n + 1)) × ZMod p ≃ Fin (p ^ (n + 2)) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpow : p * p ^ (n + 1) = p ^ (n + 2) := by
    calc
      p * p ^ (n + 1) = p ^ (n + 1) * p := by ac_rfl
      _ = p ^ (n + 2) := by
        simp only [pow_succ]
  exact
    (Equiv.prodCongr (Equiv.refl (Fin (p ^ (n + 1))))
        (ZMod.finEquiv p).symm.toEquiv).trans
      ((Equiv.prodComm _ _).trans
        (finProdFinEquiv.trans (finCongr hpow)))

/-- Combining a base coordinate and a new digit has the expected integer
value `base + p^(n+1) * digit`. -/
theorem vinogradovPrimePowerDigitEquiv_apply_val
    (p n : ℕ) [Fact p.Prime]
    (x : Fin (p ^ (n + 1))) (u : ZMod p) :
    (vinogradovPrimePowerDigitEquiv p n (x, u)).val =
      x.val + p ^ (n + 1) * u.val := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Fact.out : p.Prime).ne_zero
  simp [vinogradovPrimePowerDigitEquiv, Equiv.trans_apply,
    finProdFinEquiv]
  rfl

/-- The digit decomposition recombines to the original higher-level
coordinate. -/
theorem vinogradovPrimePowerDigitEquiv_symm_apply
    (p n : ℕ) [Fact p.Prime] (z : Fin (p ^ (n + 2))) :
    vinogradovPrimePowerDigitEquiv p n
      ((vinogradovPrimePowerDigitEquiv p n).symm z) = z :=
  (vinogradovPrimePowerDigitEquiv p n).apply_symm_apply z

/-- Coordinatewise digit decomposition for a complete tuple. -/
noncomputable def vinogradovPrimePowerTupleDigitEquiv
    (p s n : ℕ) [Fact p.Prime] :
    ((Fin s → Fin (p ^ (n + 1))) × (Fin s → ZMod p)) ≃
      (Fin s → Fin (p ^ (n + 2))) where
  toFun z i := vinogradovPrimePowerDigitEquiv p n (z.1 i, z.2 i)
  invFun z :=
    (fun i ↦ ((vinogradovPrimePowerDigitEquiv p n).symm (z i)).1,
      fun i ↦ ((vinogradovPrimePowerDigitEquiv p n).symm (z i)).2)
  left_inv z := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst
        ((vinogradovPrimePowerDigitEquiv p n).symm_apply_apply
          (z.1 i, z.2 i))
    · funext i
      exact congrArg Prod.snd
        ((vinogradovPrimePowerDigitEquiv p n).symm_apply_apply
          (z.1 i, z.2 i))
  right_inv z := by
    funext i
    exact (vinogradovPrimePowerDigitEquiv p n).apply_symm_apply (z i)

/-- The coordinatewise tuple equivalence has the same base-plus-digit value
formula as the scalar equivalence. -/
theorem vinogradovPrimePowerTupleDigitEquiv_apply_val
    (p s n : ℕ) [Fact p.Prime]
    (x : Fin s → Fin (p ^ (n + 1))) (u : Fin s → ZMod p)
    (i : Fin s) :
    (vinogradovPrimePowerTupleDigitEquiv p s n (x, u) i).val =
      (x i).val + p ^ (n + 1) * (u i).val :=
  vinogradovPrimePowerDigitEquiv_apply_val p n (x i) (u i)

/-- Splitting a full tuple into its first `k` and last `r` coordinates and
joining the blocks again recovers the tuple. -/
theorem vinogradovJoinTuple_split {α : Type*} {k r : ℕ}
    (x : Fin (k + r) → α) :
    vinogradovJoinTuple
      (fun i ↦ x (Fin.castAdd r i))
      (fun i ↦ x (Fin.natAdd k i)) = x := by
  funext i
  rcases finSumFinEquiv.surjective i with ⟨z, rfl⟩
  cases z with
  | inl i => simp
  | inr i => simp

/-- The head-tail representation is equivalent to an ordinary tuple of
length `k+r`. -/
def vinogradovJoinTupleEquiv (α : Type*) (k r : ℕ) :
    ((Fin k → α) × (Fin r → α)) ≃ (Fin (k + r) → α) where
  toFun z := vinogradovJoinTuple z.1 z.2
  invFun x :=
    (fun i ↦ x (Fin.castAdd r i), fun i ↦ x (Fin.natAdd k i))
  left_inv z := by
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp
  right_inv := vinogradovJoinTuple_split

/-- The nested free/head correction representation used by the lifting
fibers is equivalent to an ordinary pair of complete correction tuples. -/
def vinogradovSplitCorrectionEquiv (p k r : ℕ) :
    (Σ _ : vinogradovFreeCorrectionData p k r,
      Fin k → ZMod p) ≃
      ((Fin (k + r) → ZMod p) × (Fin (k + r) → ZMod p)) where
  toFun z := (vinogradovJoinTuple z.2 z.1.1, z.1.2)
  invFun uv :=
    ⟨((fun i ↦ uv.1 (Fin.natAdd k i)), uv.2),
      fun i ↦ uv.1 (Fin.castAdd r i)⟩
  left_inv z := by
    rcases z with ⟨⟨tail, right⟩, head⟩
    apply Sigma.ext
    · apply Prod.ext
      · funext i
        simp
      · rfl
    · simp
  right_inv uv := by
    apply Prod.ext
    · exact vinogradovJoinTuple_split uv.1
    · rfl

/-- A pair of base-level Vinogradov tuples modulo `p^(n+1)`. -/
abbrev vinogradovPrimePowerBasePair (p k r n : ℕ) :=
  ((Fin (k + r) → Fin (p ^ (n + 1))) ×
    (Fin (k + r) → Fin (p ^ (n + 1))))

/-- The split correction data carried by a one-step nonsingular lift. -/
abbrev vinogradovPrimePowerSplitCorrection (p k r : ℕ) :=
  Σ _ : vinogradovFreeCorrectionData p k r, Fin k → ZMod p

/-- A pair of lifted Vinogradov tuples modulo `p^(n+2)`. -/
abbrev vinogradovPrimePowerHigherPair (p k r n : ℕ) :=
  ((Fin (k + r) → Fin (p ^ (n + 2))) ×
    (Fin (k + r) → Fin (p ^ (n + 2))))

/-- Regroup two pairs so that each base tuple is paired with its own digit
tuple. -/
private def pairInterleaveEquiv (A B C D : Type*) :
    ((A × B) × (C × D)) ≃ ((A × C) × (B × D)) where
  toFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  invFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  left_inv z := by
    rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl
  right_inv z := by
    rcases z with ⟨⟨a, c⟩, ⟨b, d⟩⟩
    rfl

/-- A base-level pair together with all its split correction digits is
equivalent to an unrestricted pair of tuples at the next prime-power level. -/
noncomputable def vinogradovPrimePowerLiftAmbientEquiv
    (p k r n : ℕ) [Fact p.Prime] :
    (Σ _ : vinogradovPrimePowerBasePair p k r n,
      vinogradovPrimePowerSplitCorrection p k r) ≃
      vinogradovPrimePowerHigherPair p k r n :=
  (Equiv.sigmaEquivProd
      (vinogradovPrimePowerBasePair p k r n)
      (vinogradovPrimePowerSplitCorrection p k r)).trans
    ((Equiv.prodCongr
        (Equiv.refl (vinogradovPrimePowerBasePair p k r n))
        (vinogradovSplitCorrectionEquiv p k r)).trans
      ((pairInterleaveEquiv _ _ _ _).trans
        (Equiv.prodCongr
          (vinogradovPrimePowerTupleDigitEquiv p (k + r) n)
          (vinogradovPrimePowerTupleDigitEquiv p (k + r) n))))

/-- The left tuple produced by the ambient lift has the expected
base-plus-digit representative. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_apply_fst_val
    (p k r n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p k r n)
    (z : vinogradovPrimePowerSplitCorrection p k r)
    (i : Fin (k + r)) :
    ((vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).1 i).val =
      (xy.1 i).val + p ^ (n + 1) *
        ((vinogradovSplitCorrectionEquiv p k r z).1 i).val := by
  change
    (vinogradovPrimePowerTupleDigitEquiv p (k + r) n
      (xy.1, (vinogradovSplitCorrectionEquiv p k r z).1) i).val = _
  exact vinogradovPrimePowerTupleDigitEquiv_apply_val
    p (k + r) n xy.1 (vinogradovSplitCorrectionEquiv p k r z).1 i

/-- The right tuple produced by the ambient lift has the expected
base-plus-digit representative. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_apply_snd_val
    (p k r n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p k r n)
    (z : vinogradovPrimePowerSplitCorrection p k r)
    (i : Fin (k + r)) :
    ((vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).2 i).val =
      (xy.2 i).val + p ^ (n + 1) *
        ((vinogradovSplitCorrectionEquiv p k r z).2 i).val := by
  change
    (vinogradovPrimePowerTupleDigitEquiv p (k + r) n
      (xy.2, (vinogradovSplitCorrectionEquiv p k r z).2) i).val = _
  exact vinogradovPrimePowerTupleDigitEquiv_apply_val
    p (k + r) n xy.2 (vinogradovSplitCorrectionEquiv p k r z).2 i

/-- A split correction belongs to its one-step fiber exactly when the tuples
obtained from the ambient digit equivalence solve the next-level Vinogradov
system. -/
theorem mem_vinogradovSolutionCorrectionSet_iff_lifted_solution
    (p k r n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p k r n)
    (z : vinogradovPrimePowerSplitCorrection p k r) :
    z ∈ vinogradovSolutionCorrectionSet p k r n
        (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ))
        (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ)) ↔
      IsVinogradovSolutionMod (p ^ (n + 2)) k (k + r) (p ^ (n + 2))
        (vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).1
        (vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).2 := by
  rw [mem_vinogradovSolutionCorrectionSet_iff,
    isVinogradovSolutionMod_iff_powerSumInt_modEq]
  have hmod : (p : ℤ) ^ (n + 1) * p = (p ^ (n + 2) : ℕ) := by
    norm_num [pow_succ]
  have hleft :
      vinogradovJoinTuple
          (fun i ↦ (((xy.1 (Fin.castAdd r i)).val + 1 : ℕ) : ℤ) +
            (p : ℤ) ^ (n + 1) * (z.2 i).val)
          (fun i ↦ (((xy.1 (Fin.natAdd k i)).val + 1 : ℕ) : ℤ) +
            (p : ℤ) ^ (n + 1) * (z.1.1 i).val) =
        fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ) +
          (p : ℤ) ^ (n + 1) *
            ((vinogradovSplitCorrectionEquiv p k r z).1 i).val := by
    funext i
    rcases finSumFinEquiv.surjective i with ⟨w, rfl⟩
    cases w with
    | inl i => simp [vinogradovSplitCorrectionEquiv]
    | inr i => simp [vinogradovSplitCorrectionEquiv]
  have hright :
      (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ) +
          (p : ℤ) ^ (n + 1) * (z.1.2 i).val) =
        fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ) +
          (p : ℤ) ^ (n + 1) *
            ((vinogradovSplitCorrectionEquiv p k r z).2 i).val := by
    rfl
  have horderLeft :
      (fun i ↦ (((xy.1 i).val + 1 : ℕ) : ℤ) +
          (p : ℤ) ^ (n + 1) *
            ((vinogradovSplitCorrectionEquiv p k r z).1 i).val) =
        fun i ↦ (xy.1 i).val +
          (p : ℤ) ^ (n + 1) *
            ((vinogradovSplitCorrectionEquiv p k r z).1 i).val + 1 := by
    funext i
    push_cast
    ring
  have horderRight :
      (fun i ↦ (((xy.2 i).val + 1 : ℕ) : ℤ) +
          (p : ℤ) ^ (n + 1) *
            ((vinogradovSplitCorrectionEquiv p k r z).2 i).val) =
        fun i ↦ (xy.2 i).val +
          (p : ℤ) ^ (n + 1) *
            ((vinogradovSplitCorrectionEquiv p k r z).2 i).val + 1 := by
    funext i
    push_cast
    ring
  constructor
  · intro h j
    rw [hleft, hright, horderLeft, horderRight] at h
    rw [← hmod]
    simpa [vinogradovSplitCorrectionEquiv,
      vinogradovPrimePowerLiftAmbientEquiv_apply_fst_val,
      vinogradovPrimePowerLiftAmbientEquiv_apply_snd_val] using h j
  · intro h j
    rw [hmod]
    rw [hleft, hright, horderLeft, horderRight]
    simpa [vinogradovSplitCorrectionEquiv,
      vinogradovPrimePowerLiftAmbientEquiv_apply_fst_val,
      vinogradovPrimePowerLiftAmbientEquiv_apply_snd_val] using h j

/-- Reducing a lifted left coordinate modulo `p` recovers its base
coordinate modulo `p`; the new digit is multiplied by `p^(n+1)`. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_fst_mod
    (p k r n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p k r n)
    (z : vinogradovPrimePowerSplitCorrection p k r)
    (i : Fin (k + r)) :
    ((((vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).1 i).val + 1 : ℕ) :
        ZMod p) =
      (((xy.1 i).val + 1 : ℕ) : ZMod p) := by
  rw [vinogradovPrimePowerLiftAmbientEquiv_apply_fst_val]
  push_cast
  simp [pow_succ]

/-- The selected left block is nonsingular after a one-step lift exactly
when the selected base block is nonsingular. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_head_injective_iff
    (p k r n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p k r n)
    (z : vinogradovPrimePowerSplitCorrection p k r) :
    Function.Injective (fun i : Fin k ↦
        (((((vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).1
          (Fin.castAdd r i)).val + 1 : ℕ)) : ZMod p)) ↔
      Function.Injective (fun i : Fin k ↦
        (((xy.1 (Fin.castAdd r i)).val + 1 : ℕ) : ZMod p)) := by
  constructor
  · intro h i j hij
    apply h
    simpa only [vinogradovPrimePowerLiftAmbientEquiv_fst_mod] using hij
  · intro h i j hij
    apply h
    simpa only [vinogradovPrimePowerLiftAmbientEquiv_fst_mod] using hij

/-- Any next-level solution obtained from the digit equivalence reduces to a
solution at the base prime-power level. -/
theorem vinogradovPrimePowerLiftAmbientEquiv_solution_to_base
    (p k r n : ℕ) [Fact p.Prime]
    (xy : vinogradovPrimePowerBasePair p k r n)
    (z : vinogradovPrimePowerSplitCorrection p k r)
    (h : IsVinogradovSolutionMod (p ^ (n + 2)) k (k + r) (p ^ (n + 2))
      (vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).1
      (vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).2) :
    IsVinogradovSolutionMod (p ^ (n + 1)) k (k + r) (p ^ (n + 1))
      xy.1 xy.2 := by
  apply (isVinogradovSolutionMod_iff_powerSumInt_modEq
    (p ^ (n + 1)) k (k + r) (p ^ (n + 1)) xy.1 xy.2).mpr
  intro j
  have hhigh :=
    (isVinogradovSolutionMod_iff_powerSumInt_modEq
      (p ^ (n + 2)) k (k + r) (p ^ (n + 2))
      (vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).1
      (vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).2).mp h j
  have hdiv : (p : ℤ) ^ (n + 1) ∣ (p : ℤ) ^ (n + 2) := by
    refine ⟨p, ?_⟩
    rw [pow_succ]
  have hxcoord : ∀ i : Fin (k + r),
      (((xy.1 i).val + 1 : ℕ) : ℤ) ≡
        (((((vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).1 i).val + 1 :
          ℕ)) : ℤ) [ZMOD (p : ℤ) ^ (n + 1)] := by
    intro i
    rw [vinogradovPrimePowerLiftAmbientEquiv_apply_fst_val]
    push_cast
    simpa [add_assoc, add_comm, add_left_comm] using
      (Int.modEq_add_fac_self
        (a := ((xy.1 i).val : ℤ) + 1)
        (t := (((vinogradovSplitCorrectionEquiv p k r z).1 i).val : ℤ))
        (n := (p : ℤ) ^ (n + 1))).symm
  have hycoord : ∀ i : Fin (k + r),
      (((xy.2 i).val + 1 : ℕ) : ℤ) ≡
        (((((vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).2 i).val + 1 :
          ℕ)) : ℤ) [ZMOD (p : ℤ) ^ (n + 1)] := by
    intro i
    rw [vinogradovPrimePowerLiftAmbientEquiv_apply_snd_val]
    push_cast
    simpa [add_assoc, add_comm, add_left_comm] using
      (Int.modEq_add_fac_self
        (a := ((xy.2 i).val : ℤ) + 1)
        (t := (((vinogradovSplitCorrectionEquiv p k r z).2 i).val : ℤ))
        (n := (p : ℤ) ^ (n + 1))).symm
  have hxpower := vinogradovPowerSumInt_modEq
    ((p : ℤ) ^ (n + 1)) hxcoord j
  have hypower := vinogradovPowerSumInt_modEq
    ((p : ℤ) ^ (n + 1)) hycoord j
  have hhigh' :
      vinogradovPowerSumInt
          (fun i ↦ (((((vinogradovPrimePowerLiftAmbientEquiv p k r n
            ⟨xy, z⟩).1 i).val + 1 : ℕ)) : ℤ)) j ≡
        vinogradovPowerSumInt
          (fun i ↦ (((((vinogradovPrimePowerLiftAmbientEquiv p k r n
            ⟨xy, z⟩).2 i).val + 1 : ℕ)) : ℤ)) j
        [ZMOD (p : ℤ) ^ (n + 1)] := by
    apply (show
      vinogradovPowerSumInt
          (fun i ↦ (((((vinogradovPrimePowerLiftAmbientEquiv p k r n
            ⟨xy, z⟩).1 i).val + 1 : ℕ)) : ℤ)) j ≡
        vinogradovPowerSumInt
          (fun i ↦ (((((vinogradovPrimePowerLiftAmbientEquiv p k r n
            ⟨xy, z⟩).2 i).val + 1 : ℕ)) : ℤ)) j
        [ZMOD (p : ℤ) ^ (n + 2)] from by simpa using hhigh).of_dvd
    exact hdiv
  exact hxpower.trans (hhigh'.trans hypower.symm)

/-- Membership in the total nonsingular lift space is transported exactly to
membership in the next-level nonsingular solution set. -/
theorem mem_vinogradovPrimePowerNonsingularLiftSet_iff_image_mem
    (p k r n : ℕ) [Fact p.Prime]
    (w : Σ _ : vinogradovPrimePowerBasePair p k r n,
      vinogradovPrimePowerSplitCorrection p k r) :
    w ∈ vinogradovPrimePowerNonsingularLiftSet p k r n ↔
      vinogradovPrimePowerLiftAmbientEquiv p k r n w ∈
        vinogradovPrimePowerNonsingularSolutionSet p k r (n + 1) := by
  rcases w with ⟨xy, z⟩
  rw [vinogradovPrimePowerNonsingularLiftSet, Finset.mem_sigma,
    mem_vinogradovPrimePowerNonsingularSolutionSet_iff,
    mem_vinogradovSolutionCorrectionSet_iff_lifted_solution,
    mem_vinogradovPrimePowerNonsingularSolutionSet_iff]
  constructor
  · rintro ⟨⟨hbaseInj, _hbaseSol⟩, hhighSol⟩
    refine ⟨?_, ?_⟩
    · exact
        (vinogradovPrimePowerLiftAmbientEquiv_head_injective_iff
          p k r n xy z).mpr hbaseInj
    · simpa only [Nat.add_assoc] using hhighSol
  · rintro ⟨hhighInj, hhighSol⟩
    have hhighSol' :
        IsVinogradovSolutionMod (p ^ (n + 2)) k (k + r) (p ^ (n + 2))
          (vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).1
          (vinogradovPrimePowerLiftAmbientEquiv p k r n ⟨xy, z⟩).2 := by
      simpa only [Nat.add_assoc] using hhighSol
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact
        (vinogradovPrimePowerLiftAmbientEquiv_head_injective_iff
          p k r n xy z).mp hhighInj
    · exact vinogradovPrimePowerLiftAmbientEquiv_solution_to_base
        p k r n xy z hhighSol'
    · exact hhighSol'

/-- Mapping the total nonsingular lift set through the digit equivalence gives
exactly the nonsingular solution set at the next prime-power level. -/
theorem map_vinogradovPrimePowerNonsingularLiftSet_eq
    (p k r n : ℕ) [Fact p.Prime] :
    (vinogradovPrimePowerNonsingularLiftSet p k r n).map
        (vinogradovPrimePowerLiftAmbientEquiv p k r n).toEmbedding =
      vinogradovPrimePowerNonsingularSolutionSet p k r (n + 1) := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
    exact
      (mem_vinogradovPrimePowerNonsingularLiftSet_iff_image_mem
        p k r n w).mp hw
  · intro hv
    let e := vinogradovPrimePowerLiftAmbientEquiv p k r n
    let w := e.symm v
    have hew : e w = v := e.apply_symm_apply v
    apply Finset.mem_map.mpr
    refine ⟨w, ?_, hew⟩
    apply
      (mem_vinogradovPrimePowerNonsingularLiftSet_iff_image_mem
        p k r n w).mpr
    simpa [e, w] using hv

/-- The nonsingular modular solution count satisfies the one-step
prime-power recurrence coming from the `p^(k+2r)` correction bound. -/
theorem card_vinogradovPrimePowerNonsingularSolutionSet_succ_le
    (p k r n : ℕ) [Fact p.Prime] (hkp : k < p) :
    (vinogradovPrimePowerNonsingularSolutionSet p k r (n + 1)).card ≤
      (vinogradovPrimePowerNonsingularSolutionSet p k r n).card *
        p ^ (k + 2 * r) := by
  rw [← map_vinogradovPrimePowerNonsingularLiftSet_eq p k r n,
    Finset.card_map]
  exact card_vinogradovPrimePowerNonsingularLiftSet_le p k r n hkp

end

end ZeroFreeRegion.VinogradovKorobov
