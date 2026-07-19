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

end

end ZeroFreeRegion.VinogradovKorobov
