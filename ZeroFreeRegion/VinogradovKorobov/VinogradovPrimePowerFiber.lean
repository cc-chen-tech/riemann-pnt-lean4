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

/-- A power sum of a tuple whose entries already lie in the residue field. -/
def vinogradovResiduePowerSum
    (p : ℕ) {d s : ℕ} (x : Fin s → ZMod p) (j : Fin d) : ZMod p :=
  ∑ i, x i ^ (j.val + 1)

/-- The Vinogradov system over the residue field `ZMod p`. -/
def IsVinogradovResidueSolution
    (p d s : ℕ) (x y : Fin s → ZMod p) : Prop :=
  ∀ j : Fin d,
    vinogradovResiduePowerSum p x j =
      vinogradovResiduePowerSum p y j

/-- At the complete residue scale `X = p`, the original modular Vinogradov
system is exactly the residue-field system after encoding `{1, ..., p}` in
`ZMod p`. -/
theorem isVinogradovSolutionMod_iff_residueSolution
    (p d s : ℕ) (x y : Fin s → Fin p) :
    IsVinogradovSolutionMod p d s p x y ↔
      IsVinogradovResidueSolution p d s
        (fun i ↦ ((x i).val + 1 : ZMod p))
        (fun i ↦ ((y i).val + 1 : ZMod p)) := by
  rfl

/-- Residue-field Vinogradov solutions for which the first block on the
left-hand side is singular. -/
noncomputable def vinogradovBlockSingularSolutionSet
    (p d k r : ℕ) [Fact p.Prime] :
    Finset ((Fin (k + r) → ZMod p) × (Fin (k + r) → ZMod p)) := by
  classical
  exact
    ((vinogradovBlockSingularResidueSet p k r).product Finset.univ).filter
      fun xy ↦ IsVinogradovResidueSolution p d (k + r) xy.1 xy.2

/-- Membership records both the singular first block and all residue power-sum
equations. -/
theorem mem_vinogradovBlockSingularSolutionSet_iff
    (p d k r : ℕ) [Fact p.Prime]
    (x y : Fin (k + r) → ZMod p) :
    (x, y) ∈ vinogradovBlockSingularSolutionSet p d k r ↔
      (¬Function.Injective
          (fun i : Fin k ↦ x (Fin.castAdd r i))) ∧
        IsVinogradovResidueSolution p d (k + r) x y := by
  classical
  simp [vinogradovBlockSingularSolutionSet,
    mem_vinogradovBlockSingularResidueSet_iff]

/-- The singular part of the residue-field solution space inherits the full
one-power saving from the singular coordinate block. -/
theorem card_vinogradovBlockSingularSolutionSet_le
    (p d k r : ℕ) [Fact p.Prime] :
    (vinogradovBlockSingularSolutionSet p d k r).card ≤
      k ^ 2 * p ^ (2 * (k + r) - 1) := by
  classical
  have hsubset :
      (vinogradovBlockSingularSolutionSet p d k r).card ≤
        (vinogradovBlockSingularResidueSet p k r).card *
          p ^ (k + r) := by
    unfold vinogradovBlockSingularSolutionSet
    calc
      (((vinogradovBlockSingularResidueSet p k r).product
          (Finset.univ : Finset (Fin (k + r) → ZMod p))).filter
            fun xy ↦
              IsVinogradovResidueSolution p d (k + r) xy.1 xy.2).card ≤
          ((vinogradovBlockSingularResidueSet p k r).product
            (Finset.univ :
              Finset (Fin (k + r) → ZMod p))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = (vinogradovBlockSingularResidueSet p k r).card *
          p ^ (k + r) := by
        change
          ((vinogradovBlockSingularResidueSet p k r) ×ˢ
            (Finset.univ : Finset (Fin (k + r) → ZMod p))).card = _
        rw [Finset.card_product]
        congr 1
        simpa [Fintype.card_pi_const, ZMod.card] using
          (Finset.card_univ :
            (Finset.univ : Finset (Fin (k + r) → ZMod p)).card =
              Fintype.card (Fin (k + r) → ZMod p))
  by_cases hk : k = 0
  · subst k
    simpa [card_vinogradovBlockSingularResidueSet] using hsubset
  · calc
      (vinogradovBlockSingularSolutionSet p d k r).card ≤
          (vinogradovBlockSingularResidueSet p k r).card *
            p ^ (k + r) := hsubset
      _ ≤ (k ^ 2 * p ^ (k + r - 1)) * p ^ (k + r) :=
        Nat.mul_le_mul_right (p ^ (k + r))
          (card_vinogradovBlockSingularResidueSet_le_sq_mul_pow_pred p k r)
      _ = k ^ 2 * p ^ (2 * (k + r) - 1) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega

private noncomputable def completeResidueEquiv
    (p : ℕ) [NeZero p] : Fin p ≃ ZMod p :=
  (ZMod.finEquiv p).toEquiv.trans (Equiv.addRight 1)

private theorem completeResidueEquiv_apply
    (p : ℕ) [NeZero p] (x : Fin p) :
    completeResidueEquiv p x = (x.val : ZMod p) + 1 := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p =>
      change (x + (1 : Fin (p + 1)) : Fin (p + 1)) =
        (⟨x.val % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩ :
          Fin (p + 1)) + 1
      congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt x.isLt]

private noncomputable def completeResidueTupleEquiv
    (p s : ℕ) [NeZero p] :
    (Fin s → Fin p) ≃ (Fin s → ZMod p) :=
  Equiv.piCongrRight fun _ ↦ completeResidueEquiv p

private noncomputable def completeResiduePairEquiv
    (p s : ℕ) [NeZero p] :
    ((Fin s → Fin p) × (Fin s → Fin p)) ≃
      ((Fin s → ZMod p) × (Fin s → ZMod p)) :=
  Equiv.prodCongr (completeResidueTupleEquiv p s)
    (completeResidueTupleEquiv p s)

/-- The singular solution stratum in the original `IsVinogradovSolutionMod`
coordinates at the complete residue scale `X = p`. -/
noncomputable def vinogradovBlockSingularSolutionSetMod
    (p d k r : ℕ) [Fact p.Prime] :
    Finset ((Fin (k + r) → Fin p) × (Fin (k + r) → Fin p)) := by
  classical
  exact
    (vinogradovBlockSingularSolutionSet p d k r).map
      (completeResiduePairEquiv p (k + r)).symm.toEmbedding

/-- The transported set is exactly the singular stratum of the modular
Vinogradov system already used by the finite-moment identity. -/
theorem mem_vinogradovBlockSingularSolutionSetMod_iff
    (p d k r : ℕ) [Fact p.Prime]
    (x y : Fin (k + r) → Fin p) :
    (x, y) ∈ vinogradovBlockSingularSolutionSetMod p d k r ↔
      (¬Function.Injective
          (fun i : Fin k ↦ x (Fin.castAdd r i))) ∧
        IsVinogradovSolutionMod p d (k + r) p x y := by
  classical
  have hxencode :
      completeResidueTupleEquiv p (k + r) x =
        (fun i ↦ ((x i).val + 1 : ZMod p)) := by
    funext i
    change completeResidueEquiv p (x i) = _
    exact completeResidueEquiv_apply p (x i)
  have hyencode :
      completeResidueTupleEquiv p (k + r) y =
        (fun i ↦ ((y i).val + 1 : ZMod p)) := by
    funext i
    change completeResidueEquiv p (y i) = _
    exact completeResidueEquiv_apply p (y i)
  simp only [vinogradovBlockSingularSolutionSetMod, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hz_eq : z = completeResiduePairEquiv p (k + r) (x, y) := by
      calc
        z = completeResiduePairEquiv p (k + r)
            ((completeResiduePairEquiv p (k + r)).symm z) :=
          (completeResiduePairEquiv p (k + r)).apply_symm_apply z |>.symm
        _ = completeResiduePairEquiv p (k + r) (x, y) :=
          congrArg (completeResiduePairEquiv p (k + r)) hzx
    rw [hz_eq] at hz
    have hz' :=
      (mem_vinogradovBlockSingularSolutionSet_iff p d k r
        ((completeResidueTupleEquiv p (k + r)) x)
        ((completeResidueTupleEquiv p (k + r)) y)).mp hz
    constructor
    · intro hxinj
      apply hz'.1
      exact (completeResidueEquiv p).injective.comp hxinj
    · apply (isVinogradovSolutionMod_iff_residueSolution p d (k + r) x y).mpr
      rw [hxencode, hyencode] at hz'
      exact hz'.2
  · rintro ⟨hx, hsol⟩
    refine ⟨completeResiduePairEquiv p (k + r) (x, y), ?_, by simp⟩
    apply (mem_vinogradovBlockSingularSolutionSet_iff p d k r _ _).mpr
    constructor
    · intro hcomp
      apply hx
      intro i j hij
      apply hcomp
      simp only [completeResidueTupleEquiv, Equiv.piCongrRight_apply]
      exact congrArg (completeResidueEquiv p) hij
    · have hres :=
        (isVinogradovSolutionMod_iff_residueSolution p d (k + r) x y).mp hsol
      rw [hxencode, hyencode]
      exact hres

/-- Transport to the original complete modular coordinates preserves the
number of singular solutions. -/
theorem card_vinogradovBlockSingularSolutionSetMod_eq_residue
    (p d k r : ℕ) [Fact p.Prime] :
    (vinogradovBlockSingularSolutionSetMod p d k r).card =
      (vinogradovBlockSingularSolutionSet p d k r).card := by
  rw [vinogradovBlockSingularSolutionSetMod, Finset.card_map]

/-- Hence the singular part of the existing complete modular moment has the
same one-power saving. -/
theorem card_vinogradovBlockSingularSolutionSetMod_le
    (p d k r : ℕ) [Fact p.Prime] :
    (vinogradovBlockSingularSolutionSetMod p d k r).card ≤
      k ^ 2 * p ^ (2 * (k + r) - 1) := by
  rw [card_vinogradovBlockSingularSolutionSetMod_eq_residue]
  exact card_vinogradovBlockSingularSolutionSet_le p d k r

end

end ZeroFreeRegion.VinogradovKorobov
