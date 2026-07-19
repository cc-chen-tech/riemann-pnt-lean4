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

private theorem mul_sub_mul_tsub_eq
    (p A F k : ℕ) (hk : k ≤ p) (hF : F ≤ A) :
    p * A - (p - k) * F = p * (A - F) + k * F := by
  apply (Nat.sub_eq_iff_eq_add (Nat.mul_le_mul (Nat.sub_le _ _) hF)).mpr
  calc
    p * A = p * ((A - F) + F) := by rw [Nat.sub_add_cancel hF]
    _ = p * (A - F) + p * F := by rw [Nat.mul_add]
    _ = p * (A - F) + ((p - k) + k) * F := by
      rw [Nat.sub_add_cancel hk]
    _ = (p * (A - F) + k * F) + (p - k) * F := by
      rw [Nat.add_mul]
      ac_rfl

/-- The proportion of non-injective length-`k` tuples over a set of size `p`
is at most the union-bound scale `k^2 / p`. -/
theorem pow_sub_descFactorial_le_sq_mul_pow_pred
    (p k : ℕ) (hp : 0 < p) :
    p ^ k - p.descFactorial k ≤ k ^ 2 * p ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      by_cases hkp : k < p
      · have hk : k ≤ p := Nat.le_of_lt hkp
        have hF : p.descFactorial k ≤ p ^ k :=
          Nat.descFactorial_le_pow p k
        rw [Nat.descFactorial_succ, pow_succ]
        rw [show p ^ k * p = p * p ^ k by ac_rfl]
        rw [mul_sub_mul_tsub_eq p (p ^ k) (p.descFactorial k) k hk hF]
        have h1 :
            p * (p ^ k - p.descFactorial k) ≤
              p * (k ^ 2 * p ^ (k - 1)) :=
          Nat.mul_le_mul_left p ih
        have h2 : k * p.descFactorial k ≤ k * p ^ k :=
          Nat.mul_le_mul_left k hF
        calc
          p * (p ^ k - p.descFactorial k) + k * p.descFactorial k
              ≤ p * (k ^ 2 * p ^ (k - 1)) + k * p ^ k :=
            Nat.add_le_add h1 h2
          _ ≤ (k + 1) ^ 2 * p ^ k := by
            by_cases hk0 : k = 0
            · subst k
              simp
            · have hpow : p ^ k = p * p ^ (k - 1) := by
                conv_lhs => rw [show k = (k - 1) + 1 by omega]
                rw [pow_succ]
                ac_rfl
              rw [hpow]
              ring_nf
              gcongr
              omega
      · have hpk : p ≤ k := Nat.le_of_not_gt hkp
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.sub_zero]
        rw [show k + 1 - 1 = k by omega]
        rw [pow_succ]
        calc
          p ^ k * p = p * p ^ k := by ac_rfl
          _ ≤ (k + 1) ^ 2 * p ^ k :=
            Nat.mul_le_mul_right (p ^ k) (by nlinarith)

/-- The singular residue stratum saves one full power of `p`, up to the
explicit polynomial factor `k^2`. -/
theorem card_vinogradovSingularResidueSet_le_sq_mul_pow_pred
    (p k : ℕ) [Fact p.Prime] :
    (vinogradovSingularResidueSet p k).card ≤
      k ^ 2 * p ^ (k - 1) := by
  rw [card_vinogradovSingularResidueSet]
  exact pow_sub_descFactorial_le_sq_mul_pow_pred p k
    (Fact.out : p.Prime).pos

private noncomputable def splitResidueTupleEquiv
    (p k r : ℕ) :
    (Fin (k + r) → ZMod p) ≃
      (Fin k → ZMod p) × (Fin r → ZMod p) :=
  ((finSumFinEquiv : Fin k ⊕ Fin r ≃ Fin (k + r)).piCongrLeft
      (fun _ ↦ ZMod p)).symm.trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin r ↦ ZMod p))

/-- Length-`k+r` residue vectors whose first block of `k` coordinates is
singular.  The tail block is unrestricted. -/
noncomputable def vinogradovBlockSingularResidueSet
    (p k r : ℕ) [Fact p.Prime] : Finset (Fin (k + r) → ZMod p) := by
  classical
  exact
    ((vinogradovSingularResidueSet p k).product
      (Finset.univ : Finset (Fin r → ZMod p))).map
        (splitResidueTupleEquiv p k r).symm.toEmbedding

/-- Membership in the block-singular set means exactly that two coordinates
in the first block coincide. -/
theorem mem_vinogradovBlockSingularResidueSet_iff
    (p k r : ℕ) [Fact p.Prime] (x : Fin (k + r) → ZMod p) :
    x ∈ vinogradovBlockSingularResidueSet p k r ↔
      ¬Function.Injective (fun i : Fin k ↦ x (Fin.castAdd r i)) := by
  classical
  simp [vinogradovBlockSingularResidueSet, vinogradovSingularResidueSet,
    splitResidueTupleEquiv, Equiv.trans_apply]

/-- Appending `r` unrestricted coordinates multiplies the singular block
count by exactly `p^r`. -/
theorem card_vinogradovBlockSingularResidueSet
    (p k r : ℕ) [Fact p.Prime] :
    (vinogradovBlockSingularResidueSet p k r).card =
      (p ^ k - p.descFactorial k) * p ^ r := by
  classical
  rw [vinogradovBlockSingularResidueSet, Finset.card_map]
  change
    ((vinogradovSingularResidueSet p k) ×ˢ
      (Finset.univ : Finset (Fin r → ZMod p))).card = _
  rw [Finset.card_product, card_vinogradovSingularResidueSet]
  congr 1
  simpa [Fintype.card_pi_const, ZMod.card] using
    (Finset.card_univ :
      (Finset.univ : Finset (Fin r → ZMod p)).card =
        Fintype.card (Fin r → ZMod p))

/-- A singular head block still saves one full power of `p` after adjoining
an arbitrary tail. -/
theorem card_vinogradovBlockSingularResidueSet_le_sq_mul_pow_pred
    (p k r : ℕ) [Fact p.Prime] :
    (vinogradovBlockSingularResidueSet p k r).card ≤
      k ^ 2 * p ^ (k + r - 1) := by
  rw [card_vinogradovBlockSingularResidueSet]
  by_cases hk : k = 0
  · subst k
    simp
  · calc
      (p ^ k - p.descFactorial k) * p ^ r
          ≤ (k ^ 2 * p ^ (k - 1)) * p ^ r :=
        Nat.mul_le_mul_right (p ^ r)
          (pow_sub_descFactorial_le_sq_mul_pow_pred p k
            (Fact.out : p.Prime).pos)
      _ = k ^ 2 * p ^ (k + r - 1) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega

end

end ZeroFreeRegion.VinogradovKorobov
