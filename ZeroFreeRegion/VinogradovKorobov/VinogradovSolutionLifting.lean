import ZeroFreeRegion.VinogradovKorobov.VinogradovSolutionStrata

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

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

end

end ZeroFreeRegion.VinogradovKorobov
