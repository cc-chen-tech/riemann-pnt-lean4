import ZeroFreeRegion.VinogradovKorobov.VinogradovTaylor
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
