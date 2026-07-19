import ZeroFreeRegion.VinogradovKorobov.VinogradovLinearLift
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The Jacobian of the first `d` power sums in an arbitrary number `s` of
variables. -/
def vinogradovRectangularPowerSumJacobian
    {R : Type*} [CommRing R] {d s : ℕ}
    (x : Fin s → R) : Matrix (Fin d) (Fin s) R :=
  fun j i ↦ (j.val + 1 : ℕ) * x i ^ j.val

/-- The existing square Jacobian is the square specialization of the
rectangular definition. -/
theorem vinogradovRectangularPowerSumJacobian_eq_square
    {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) :
    vinogradovRectangularPowerSumJacobian (d := k) x =
      vinogradovPowerSumJacobian x := by
  rfl

/-- First-order Taylor expansion for `d` power sums in `s` variables. -/
theorem vinogradovPowerSumInt_affine_modEq_sq_rectangular
    {d s : ℕ} (q : ℤ) (x h : Fin s → ℤ) (j : Fin d) :
    vinogradovPowerSumInt (fun i ↦ x i + q * h i) j ≡
      vinogradovPowerSumInt x j +
        q * (vinogradovRectangularPowerSumJacobian x).mulVec h j
      [ZMOD q ^ 2] := by
  have hsum :
      (∑ i : Fin s, (x i + q * h i) ^ (j.val + 1)) ≡
        ∑ i : Fin s,
          (x i ^ (j.val + 1) +
            q * (((j.val + 1 : ℕ) : ℤ) * x i ^ j.val * h i))
          [ZMOD q ^ 2] := by
    apply Int.ModEq.sum
    intro i _hi
    convert int_pow_add_mul_modEq_sq q (x i) (h i) (j.val + 1) using 1 <;>
      simp <;> ring
  simpa [vinogradovPowerSumInt,
    vinogradovRectangularPowerSumJacobian,
    Matrix.mulVec, dotProduct, Finset.sum_add_distrib,
    Finset.mul_sum] using hsum

/-- Taylor expansion modulo `q*r` whenever `r` divides the affine scale
`q`, with equation degree independent of tuple length. -/
theorem vinogradovPowerSumInt_affine_modEq_mul_of_dvd_rectangular
    {d s : ℕ} (q r : ℤ) (hrq : r ∣ q)
    (x h : Fin s → ℤ) (j : Fin d) :
    vinogradovPowerSumInt (fun i ↦ x i + q * h i) j ≡
      vinogradovPowerSumInt x j +
        q * (vinogradovRectangularPowerSumJacobian x).mulVec h j
      [ZMOD q * r] := by
  apply (vinogradovPowerSumInt_affine_modEq_sq_rectangular q x h j).of_dvd
  obtain ⟨c, rfl⟩ := hrq
  exact ⟨c, by ring⟩

/-- Linearized first-order power-sum change of a pair of correction tuples. -/
def vinogradovPairCorrectionLinearMap
    (p d s : ℕ) [Fact p.Prime]
    (x y : Fin s → ZMod p) :
    ((Fin s → ZMod p) × (Fin s → ZMod p)) →ₗ[ZMod p]
      (Fin d → ZMod p) :=
  ((vinogradovRectangularPowerSumJacobian x).mulVecLin.comp
      (LinearMap.fst (ZMod p) (Fin s → ZMod p) (Fin s → ZMod p))) -
    ((vinogradovRectangularPowerSumJacobian y).mulVecLin.comp
      (LinearMap.snd (ZMod p) (Fin s → ZMod p) (Fin s → ZMod p)))

theorem vinogradovPairCorrectionLinearMap_apply
    (p d s : ℕ) [Fact p.Prime]
    (x y : Fin s → ZMod p)
    (u v : Fin s → ZMod p) (j : Fin d) :
    vinogradovPairCorrectionLinearMap p d s x y (u, v) j =
      (vinogradovRectangularPowerSumJacobian x).mulVec u j -
        (vinogradovRectangularPowerSumJacobian y).mulVec v j := by
  rfl

/-- As soon as there is at least one equation and one variable, the first
power-sum row makes the pair correction Jacobian nonzero. -/
theorem one_le_finrank_vinogradovPairCorrectionLinearMap_range
    (p d s : ℕ) [Fact p.Prime] (hd : 0 < d) (hs : 0 < s)
    (x y : Fin s → ZMod p) :
    1 ≤ Module.finrank (ZMod p)
      (vinogradovPairCorrectionLinearMap p d s x y).range := by
  let i₀ : Fin s := ⟨0, hs⟩
  let j₀ : Fin d := ⟨0, hd⟩
  let u : Fin s → ZMod p := fun i ↦ if i = i₀ then 1 else 0
  let uv : (Fin s → ZMod p) × (Fin s → ZMod p) := (u, 0)
  have hvalue :
      vinogradovPairCorrectionLinearMap p d s x y uv j₀ = 1 := by
    simp [vinogradovPairCorrectionLinearMap_apply,
      vinogradovRectangularPowerSumJacobian,
      Matrix.mulVec, dotProduct, uv, u, i₀, j₀]
  have hne : vinogradovPairCorrectionLinearMap p d s x y uv ≠ 0 := by
    intro hzero
    have := congrFun hzero j₀
    rw [hvalue] at this
    exact one_ne_zero this
  apply Submodule.one_le_finrank_iff.mpr
  intro hrange
  have hmem : vinogradovPairCorrectionLinearMap p d s x y uv ∈
      (vinogradovPairCorrectionLinearMap p d s x y).range := ⟨uv, rfl⟩
  rw [hrange, Submodule.mem_bot] at hmem
  exact hne hmem

/-- For a square system, an injective left residue tuple makes the pair
correction Jacobian surjective, hence of full rank. -/
theorem finrank_vinogradovPairCorrectionLinearMap_range_eq_of_left_injective
    (p d : ℕ) [Fact p.Prime] (hdp : d < p)
    (x y : Fin d → ZMod p) (hx : Function.Injective x) :
    Module.finrank (ZMod p)
      (vinogradovPairCorrectionLinearMap p d d x y).range = d := by
  have hsurjective : Function.Surjective
      (vinogradovPairCorrectionLinearMap p d d x y) := by
    intro target
    obtain ⟨u, hu, _hunique⟩ :=
      existsUnique_vinogradovPowerSumJacobian_zmod_mulVec_eq
        p d hdp x hx target
    refine ⟨(u, 0), ?_⟩
    ext j
    have huj := congrFun hu j
    simpa [vinogradovPairCorrectionLinearMap_apply,
      vinogradovRectangularPowerSumJacobian,
      vinogradovPowerSumJacobian, Matrix.mulVec, dotProduct] using huj
  rw [LinearMap.range_eq_top.mpr hsurjective, finrank_top,
    Module.finrank_pi]
  simp

/-- A finite fiber of an additive linear map has the same cardinality as its
zero fiber whenever it is nonempty. -/
theorem card_linearMap_fiber_eq_zero_fiber
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Fintype V]
    [AddCommMonoid W] [Module R W] [DecidableEq W]
    (f : V →ₗ[R] W) (y : W) (hy : y ∈ Set.range f) :
    (Finset.univ.filter fun v ↦ f v = y).card =
      (Finset.univ.filter fun v ↦ f v = 0).card := by
  exact AddMonoidHom.card_fiber_eq_of_mem_range f hy ⟨0, f.map_zero⟩

/-- The zero fiber of a finite linear map is its kernel, as a cardinality
identity. -/
theorem card_linearMap_zero_fiber_eq_card_ker
    {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [Fintype V]
    [AddCommMonoid W] [Module R W] [DecidableEq W]
    (f : V →ₗ[R] W) :
    (Finset.univ.filter fun v ↦ f v = 0).card = Nat.card f.ker := by
  let e : {v : V // f v = 0} ≃ f.ker := {
    toFun v := ⟨v, LinearMap.mem_ker.mpr v.property⟩
    invFun v := ⟨v, LinearMap.mem_ker.mp v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  calc
    (Finset.univ.filter fun v ↦ f v = 0).card =
        Fintype.card {v : V // f v = 0} := (Fintype.card_subtype _).symm
    _ = Nat.card {v : V // f v = 0} := Nat.card_eq_fintype_card.symm
    _ = Nat.card f.ker := Nat.card_congr e

/-- The finite-field correction fiber through one correction pair. -/
noncomputable def vinogradovPairCorrectionFiberSet
    (p d s : ℕ) [Fact p.Prime]
    (x y : Fin s → ZMod p)
    (uv : (Fin s → ZMod p) × (Fin s → ZMod p)) :
    Finset ((Fin s → ZMod p) × (Fin s → ZMod p)) :=
  Finset.univ.filter fun zw ↦
    vinogradovPairCorrectionLinearMap p d s x y zw =
      vinogradovPairCorrectionLinearMap p d s x y uv

theorem mem_vinogradovPairCorrectionFiberSet_iff
    (p d s : ℕ) [Fact p.Prime]
    (x y : Fin s → ZMod p)
    (uv zw : (Fin s → ZMod p) × (Fin s → ZMod p)) :
    zw ∈ vinogradovPairCorrectionFiberSet p d s x y uv ↔
      vinogradovPairCorrectionLinearMap p d s x y zw =
        vinogradovPairCorrectionLinearMap p d s x y uv := by
  simp [vinogradovPairCorrectionFiberSet]

/-- Every correction fiber through an actual pair has the cardinality of the
zero fiber of the pair Jacobian. -/
theorem card_vinogradovPairCorrectionFiberSet_eq_zero_fiber
    (p d s : ℕ) [Fact p.Prime]
    (x y : Fin s → ZMod p)
    (uv : (Fin s → ZMod p) × (Fin s → ZMod p)) :
    (vinogradovPairCorrectionFiberSet p d s x y uv).card =
      (Finset.univ.filter fun zw ↦
        vinogradovPairCorrectionLinearMap p d s x y zw = 0).card := by
  apply card_linearMap_fiber_eq_zero_fiber
  exact ⟨uv, rfl⟩

/-- The exact correction-fiber count is the kernel cardinality of the pair
Jacobian. -/
theorem card_vinogradovPairCorrectionFiberSet_eq_card_ker
    (p d s : ℕ) [Fact p.Prime]
    (x y : Fin s → ZMod p)
    (uv : (Fin s → ZMod p) × (Fin s → ZMod p)) :
    (vinogradovPairCorrectionFiberSet p d s x y uv).card =
      Nat.card (vinogradovPairCorrectionLinearMap p d s x y).ker := by
  rw [card_vinogradovPairCorrectionFiberSet_eq_zero_fiber,
    card_linearMap_zero_fiber_eq_card_ker]

/-- Rank-nullity gives the exact finite-field correction-fiber cardinality.
The exponent is the source dimension `2*s` minus the Jacobian rank. -/
theorem card_vinogradovPairCorrectionFiberSet_eq_pow_rankDefect
    (p d s : ℕ) [Fact p.Prime]
    (x y : Fin s → ZMod p)
    (uv : (Fin s → ZMod p) × (Fin s → ZMod p)) :
    (vinogradovPairCorrectionFiberSet p d s x y uv).card =
      p ^ (2 * s - Module.finrank (ZMod p)
        (vinogradovPairCorrectionLinearMap p d s x y).range) := by
  rw [card_vinogradovPairCorrectionFiberSet_eq_card_ker,
    Module.natCard_eq_pow_finrank
      (K := ZMod p)
      (V := (vinogradovPairCorrectionLinearMap p d s x y).ker),
    Nat.card_zmod]
  congr 1
  have hnullity :=
    (vinogradovPairCorrectionLinearMap p d s x y).finrank_range_add_finrank_ker
  have hsource :
      Module.finrank (ZMod p)
          ((Fin s → ZMod p) × (Fin s → ZMod p)) = 2 * s := by
    simp [Module.finrank_prod]
    omega
  omega

/-- Two correction pairs above the same base pair which both satisfy the
next-level power-sum equations lie in the same fiber of the finite-field
pair Jacobian. -/
theorem vinogradovPairCorrectionLinearMap_eq_of_affine_solutions
    (p d s n : ℕ) [Fact p.Prime]
    (x y u v u' v' : Fin s → ℤ)
    (hpower : ∀ j : Fin d,
      vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * u i) j ≡
        vinogradovPowerSumInt
          (fun i ↦ y i + (p : ℤ) ^ (n + 1) * v i) j
        [ZMOD (p : ℤ) ^ (n + 2)])
    (hpower' : ∀ j : Fin d,
      vinogradovPowerSumInt
          (fun i ↦ x i + (p : ℤ) ^ (n + 1) * u' i) j ≡
        vinogradovPowerSumInt
          (fun i ↦ y i + (p : ℤ) ^ (n + 1) * v' i) j
        [ZMOD (p : ℤ) ^ (n + 2)]) :
    vinogradovPairCorrectionLinearMap p d s
        (fun i ↦ (x i : ZMod p)) (fun i ↦ (y i : ZMod p))
        ((fun i ↦ (u i : ZMod p)), (fun i ↦ (v i : ZMod p))) =
      vinogradovPairCorrectionLinearMap p d s
        (fun i ↦ (x i : ZMod p)) (fun i ↦ (y i : ZMod p))
        ((fun i ↦ (u' i : ZMod p)), (fun i ↦ (v' i : ZMod p))) := by
  let q : ℤ := (p : ℤ) ^ (n + 1)
  have hq0 : q ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpq : (p : ℤ) ∣ q := by
    exact dvd_pow_self (p : ℤ) (Nat.succ_ne_zero n)
  have hmod : q * (p : ℤ) = (p : ℤ) ^ (n + 2) := by
    simp [q, pow_succ]
  funext j
  have hlinear :
      (vinogradovRectangularPowerSumJacobian x).mulVec u j -
          (vinogradovRectangularPowerSumJacobian y).mulVec v j ≡
        (vinogradovRectangularPowerSumJacobian x).mulVec u' j -
          (vinogradovRectangularPowerSumJacobian y).mulVec v' j
        [ZMOD (p : ℤ)] := by
    have hxu :=
      vinogradovPowerSumInt_affine_modEq_mul_of_dvd_rectangular
        q (p : ℤ) hpq x u j
    have hyv :=
      vinogradovPowerSumInt_affine_modEq_mul_of_dvd_rectangular
        q (p : ℤ) hpq y v j
    have hxu' :=
      vinogradovPowerSumInt_affine_modEq_mul_of_dvd_rectangular
        q (p : ℤ) hpq x u' j
    have hyv' :=
      vinogradovPowerSumInt_affine_modEq_mul_of_dvd_rectangular
        q (p : ℤ) hpq y v' j
    have hsol :
        vinogradovPowerSumInt x j +
              q * (vinogradovRectangularPowerSumJacobian x).mulVec u j ≡
          vinogradovPowerSumInt y j +
              q * (vinogradovRectangularPowerSumJacobian y).mulVec v j
          [ZMOD q * (p : ℤ)] := by
      have hpowerj :
          vinogradovPowerSumInt
                (fun i ↦ x i + (p : ℤ) ^ (n + 1) * u i) j ≡
            vinogradovPowerSumInt
                (fun i ↦ y i + (p : ℤ) ^ (n + 1) * v i) j
            [ZMOD q * (p : ℤ)] := by
        rw [hmod]
        exact hpower j
      exact hxu.symm.trans (hpowerj.trans hyv)
    have hsol' :
        vinogradovPowerSumInt x j +
              q * (vinogradovRectangularPowerSumJacobian x).mulVec u' j ≡
          vinogradovPowerSumInt y j +
              q * (vinogradovRectangularPowerSumJacobian y).mulVec v' j
          [ZMOD q * (p : ℤ)] := by
      have hpowerj :
          vinogradovPowerSumInt
                (fun i ↦ x i + (p : ℤ) ^ (n + 1) * u' i) j ≡
            vinogradovPowerSumInt
                (fun i ↦ y i + (p : ℤ) ^ (n + 1) * v' i) j
            [ZMOD q * (p : ℤ)] := by
        rw [hmod]
        exact hpower' j
      exact hxu'.symm.trans (hpowerj.trans hyv')
    have hdiff :
        q * ((vinogradovRectangularPowerSumJacobian x).mulVec u j -
            (vinogradovRectangularPowerSumJacobian y).mulVec v j) ≡
          vinogradovPowerSumInt y j - vinogradovPowerSumInt x j
          [ZMOD q * (p : ℤ)] := by
      convert
        ((hsol.add_left (-vinogradovPowerSumInt x j)).add_right
          (-q * (vinogradovRectangularPowerSumJacobian y).mulVec v j)) using 1 <;> ring
    have hdiff' :
        q * ((vinogradovRectangularPowerSumJacobian x).mulVec u' j -
            (vinogradovRectangularPowerSumJacobian y).mulVec v' j) ≡
          vinogradovPowerSumInt y j - vinogradovPowerSumInt x j
          [ZMOD q * (p : ℤ)] := by
      convert
        ((hsol'.add_left (-vinogradovPowerSumInt x j)).add_right
          (-q * (vinogradovRectangularPowerSumJacobian y).mulVec v' j)) using 1 <;> ring
    exact Int.ModEq.mul_left_cancel' hq0 (hdiff.trans hdiff'.symm)
  have hz := (ZMod.intCast_eq_intCast_iff
    ((vinogradovRectangularPowerSumJacobian x).mulVec u j -
      (vinogradovRectangularPowerSumJacobian y).mulVec v j)
    ((vinogradovRectangularPowerSumJacobian x).mulVec u' j -
      (vinogradovRectangularPowerSumJacobian y).mulVec v' j) p).mpr hlinear
  simpa [vinogradovPairCorrectionLinearMap_apply,
    vinogradovRectangularPowerSumJacobian, Matrix.mulVec, dotProduct] using hz

end

end ZeroFreeRegion.VinogradovKorobov
