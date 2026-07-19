import ZeroFreeRegion.VinogradovKorobov.VinogradovTaylor
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Over a commutative ring, a square matrix whose determinant is a unit has
a unique solution to every right-hand side. -/
theorem existsUnique_mulVec_eq_of_isUnit_det
    {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hA : IsUnit A.det) (b : Fin n → R) :
    ∃! x, A.mulVec x = b := by
  classical
  refine ⟨A⁻¹.mulVec b, ?_, ?_⟩
  · change A.mulVec (A⁻¹.mulVec b) = b
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA,
      Matrix.one_mulVec]
  · intro y hy
    have h := congrArg (A⁻¹).mulVec hy
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA,
      Matrix.one_mulVec] using h

/-- Over a field, a square matrix with nonzero determinant has a unique
solution to every right-hand side. -/
theorem existsUnique_mulVec_eq_of_det_ne_zero
    {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : A.det ≠ 0) (b : Fin n → K) :
    ∃! x, A.mulVec x = b := by
  exact existsUnique_mulVec_eq_of_isUnit_det A (isUnit_iff_ne_zero.mpr hA) b

/-- A nonsingular power-sum Jacobian over `ZMod p` has a unique correction
vector for every prescribed first-order residue. -/
theorem existsUnique_vinogradovPowerSumJacobian_zmod_mulVec_eq
    (p k : ℕ) [Fact p.Prime] (hkp : k < p) (x : Fin k → ZMod p)
    (hx : Function.Injective x) (b : Fin k → ZMod p) :
    ∃! h, (vinogradovPowerSumJacobian x).mulVec h = b :=
  existsUnique_mulVec_eq_of_det_ne_zero (vinogradovPowerSumJacobian x)
    (det_vinogradovPowerSumJacobian_zmod_ne_zero p k hkp x hx) b

end

end ZeroFreeRegion.VinogradovKorobov
