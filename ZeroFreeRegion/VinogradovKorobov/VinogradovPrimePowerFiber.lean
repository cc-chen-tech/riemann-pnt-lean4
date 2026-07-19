import ZeroFreeRegion.VinogradovKorobov.VinogradovHensel
import Mathlib.Data.Fintype.CardEmbedding

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Coordinatewise congruent integer tuples have congruent power sums. -/
theorem vinogradovPowerSumInt_modEq
    {k s : ℕ} (m : ℤ) {x y : Fin s → ℤ}
    (hxy : ∀ i : Fin s, x i ≡ y i [ZMOD m]) (j : Fin k) :
    vinogradovPowerSumInt x j ≡ vinogradovPowerSumInt y j [ZMOD m] := by
  unfold vinogradovPowerSumInt
  apply Int.ModEq.sum
  intro i _
  exact (hxy i).pow (j.val + 1)

/-- The finite set of residue correction vectors that realize a prescribed
first-order power-sum change at prime-power level `p^(n+2)`. -/
noncomputable def vinogradovPrimePowerCorrectionSet
    (p k n : ℕ) [Fact p.Prime] (x b : Fin k → ℤ) :
    Finset (Fin k → ZMod p) := by
  classical
  exact Finset.univ.filter fun u : Fin k → ZMod p ↦
    ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (u i).val) j ≡
        vinogradovPowerSumInt x j + (p : ℤ) ^ (n + 1) * b j
          [ZMOD (p : ℤ) ^ (n + 2)]

/-- At a nonsingular residue vector, every prime-power correction fiber has
exactly one residue class. -/
theorem card_vinogradovPrimePowerCorrectionSet_eq_one
    (p k n : ℕ) [Fact p.Prime] (hkp : k < p) (x b : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p))) :
    (vinogradovPrimePowerCorrectionSet p k n x b).card = 1 := by
  classical
  obtain ⟨h, hh, hunique⟩ :=
    exists_unique_mod_vinogradovPowerSumInt_affine_lift_mod_prime_pow_succ
      p k n hkp x b hx
  let u : Fin k → ZMod p := fun i ↦ (h i : ZMod p)
  have hhu : ∀ i : Fin k, h i ≡ ((u i).val : ℤ) [ZMOD (p : ℤ)] := by
    intro i
    apply (ZMod.intCast_eq_intCast_iff (h i) ((u i).val : ℤ) p).mp
    simp [u]
  have hcoord : ∀ i : Fin k,
      x i + (p : ℤ) ^ (n + 1) * h i ≡
        x i + (p : ℤ) ^ (n + 1) * (u i).val
          [ZMOD (p : ℤ) ^ (n + 2)] := by
    intro i
    simpa [pow_succ] using
      ((hhu i).mul_left'.add_left (x i))
  have huPower : ∀ j : Fin k,
      vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (u i).val) j ≡
        vinogradovPowerSumInt x j + (p : ℤ) ^ (n + 1) * b j
          [ZMOD (p : ℤ) ^ (n + 2)] := by
    intro j
    exact (vinogradovPowerSumInt_modEq
      ((p : ℤ) ^ (n + 2)) hcoord j).symm.trans (hh j)
  have hu : u ∈ vinogradovPrimePowerCorrectionSet p k n x b := by
    simpa [vinogradovPrimePowerCorrectionSet] using huPower
  have hset : vinogradovPrimePowerCorrectionSet p k n x b = {u} := by
    ext v
    simp only [Finset.mem_singleton]
    constructor
    · intro hv
      have hvPower : ∀ j : Fin k,
          vinogradovPowerSumInt
              (fun i ↦ x i + (p : ℤ) ^ (n + 1) * (v i).val) j ≡
            vinogradovPowerSumInt x j + (p : ℤ) ^ (n + 1) * b j
              [ZMOD (p : ℤ) ^ (n + 2)] := by
        simpa [vinogradovPrimePowerCorrectionSet] using hv
      apply funext
      intro i
      have hi := hunique (fun i : Fin k ↦ ((v i).val : ℤ)) hvPower i
      have hiz :=
        (ZMod.intCast_eq_intCast_iff ((v i).val : ℤ) (h i) p).mpr hi
      simpa [u] using hiz
    · intro hv
      simpa [hv] using hu
  rw [hset, Finset.card_singleton]

/-- Residue vectors whose coordinates are pairwise distinct modulo `p`.  These
are exactly the nonsingular base points for the power-sum Jacobian when
`k < p`. -/
noncomputable def vinogradovNonsingularResidueSet
    (p k : ℕ) [Fact p.Prime] : Finset (Fin k → ZMod p) := by
  classical
  exact Finset.univ.filter Function.Injective

private def injectiveResidueTupleEquivEmbedding (p k : ℕ) :
    {x : Fin k → ZMod p // Function.Injective x} ≃ (Fin k ↪ ZMod p) where
  toFun x := ⟨x.1, x.2⟩
  invFun e := ⟨e, e.injective⟩
  left_inv x := by
    ext i
    rfl
  right_inv e := by
    ext i
    rfl

/-- There are exactly `p.descFactorial k` pairwise-distinct residue vectors of
length `k` modulo the prime `p`. -/
theorem card_vinogradovNonsingularResidueSet
    (p k : ℕ) [Fact p.Prime] :
    (vinogradovNonsingularResidueSet p k).card = p.descFactorial k := by
  classical
  unfold vinogradovNonsingularResidueSet
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (injectiveResidueTupleEquivEmbedding p k)]
  simpa using
    (Fintype.card_embedding_eq (α := Fin k) (β := ZMod p))

/-- Residue vectors at which the power-sum Jacobian is singular: at least two
coordinates coincide modulo `p`. -/
noncomputable def vinogradovSingularResidueSet
    (p k : ℕ) [Fact p.Prime] : Finset (Fin k → ZMod p) := by
  classical
  exact Finset.univ.filter fun x ↦ ¬Function.Injective x

/-- The nonsingular and singular residue vectors partition all `p^k` residue
vectors. -/
theorem card_nonsingular_add_card_singular
    (p k : ℕ) [Fact p.Prime] :
    (vinogradovNonsingularResidueSet p k).card +
        (vinogradovSingularResidueSet p k).card = p ^ k := by
  classical
  simpa [vinogradovNonsingularResidueSet, vinogradovSingularResidueSet,
    Fintype.card_pi_const, ZMod.card] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k → ZMod p))) Function.Injective)

/-- Consequently, the singular stratum has exact cardinality
`p^k - p.descFactorial k`. -/
theorem card_vinogradovSingularResidueSet
    (p k : ℕ) [Fact p.Prime] :
    (vinogradovSingularResidueSet p k).card =
      p ^ k - p.descFactorial k := by
  have h := card_nonsingular_add_card_singular p k
  rw [card_vinogradovNonsingularResidueSet] at h
  omega

/-- The total space of first-order prime-power correction fibers above all
nonsingular residue vectors. -/
noncomputable def vinogradovNonsingularPrimePowerLiftSet
    (p k n : ℕ) [Fact p.Prime] (b : Fin k → ℤ) :
    Finset (Σ _ : Fin k → ZMod p, Fin k → ZMod p) :=
  (vinogradovNonsingularResidueSet p k).sigma fun x ↦
    vinogradovPrimePowerCorrectionSet p k n
      (fun i ↦ ((x i).val : ℤ)) b

/-- Every nonsingular base vector contributes exactly one correction class, so
the total nonsingular lift space has the same cardinality as its base. -/
theorem card_vinogradovNonsingularPrimePowerLiftSet
    (p k n : ℕ) [Fact p.Prime] (hkp : k < p) (b : Fin k → ℤ) :
    (vinogradovNonsingularPrimePowerLiftSet p k n b).card =
      p.descFactorial k := by
  classical
  rw [vinogradovNonsingularPrimePowerLiftSet, Finset.card_sigma]
  calc
    _ = ∑ _x ∈ vinogradovNonsingularResidueSet p k, 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxin : Function.Injective x := by
        simpa [vinogradovNonsingularResidueSet] using hx
      have hcast :
          Function.Injective
            (fun i : Fin k ↦ ((((x i).val : ℤ)) : ZMod p)) := by
        simpa using hxin
      exact card_vinogradovPrimePowerCorrectionSet_eq_one
        p k n hkp (fun i ↦ ((x i).val : ℤ)) b hcast
    _ = (vinogradovNonsingularResidueSet p k).card := by simp
    _ = p.descFactorial k := card_vinogradovNonsingularResidueSet p k

end

end ZeroFreeRegion.VinogradovKorobov
