import ZeroFreeRegion.VinogradovKorobov.VinogradovLinear
import Mathlib.LinearAlgebra.Vandermonde

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The Jacobian matrix of the first `k` power sums in `k` variables.  Row
`j` is the derivative of the power sum of degree `j+1`. -/
def vinogradovPowerSumJacobian {R : Type*} [CommRing R] {k : ℕ}
    (x : Fin k → R) : Matrix (Fin k) (Fin k) R :=
  fun j i ↦ (j.val + 1 : ℕ) * x i ^ j.val

/-- The power-sum Jacobian is a diagonal degree matrix times a transposed
Vandermonde matrix. -/
theorem vinogradovPowerSumJacobian_eq_diagonal_mul_vandermonde_transpose
    {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) :
    vinogradovPowerSumJacobian x =
      Matrix.diagonal (fun j : Fin k ↦ ((j.val + 1 : ℕ) : R)) *
        (Matrix.vandermonde x).transpose := by
  ext j i
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [vinogradovPowerSumJacobian, Matrix.vandermonde_apply]
  · intro b _ hbj
    rw [Matrix.diagonal_apply_ne _ hbj.symm]
    simp
  · simp

/-- Determinant formula for the power-sum Jacobian. -/
theorem det_vinogradovPowerSumJacobian
    {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) :
    (vinogradovPowerSumJacobian x).det =
      (∏ j : Fin k, ((j.val + 1 : ℕ) : R)) *
        (Matrix.vandermonde x).det := by
  rw [vinogradovPowerSumJacobian_eq_diagonal_mul_vandermonde_transpose,
    Matrix.det_mul, Matrix.det_diagonal]
  simp

/-- In a domain, distinct coordinates and nonzero degree factors make the
power-sum Jacobian nonsingular. -/
theorem det_vinogradovPowerSumJacobian_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] {k : ℕ} (x : Fin k → R)
    (hdegree : ∀ j : Fin k, ((j.val + 1 : ℕ) : R) ≠ 0)
    (hx : Function.Injective x) :
    (vinogradovPowerSumJacobian x).det ≠ 0 := by
  rw [det_vinogradovPowerSumJacobian]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hdegree j)
    (Matrix.det_vandermonde_ne_zero_iff.mpr hx)

/-- Over `ZMod p`, if `p` is prime and exceeds the degree, pairwise distinct
coordinates give a nonsingular power-sum Jacobian. -/
theorem det_vinogradovPowerSumJacobian_zmod_ne_zero
    (p k : ℕ) [Fact p.Prime] (hkp : k < p) (x : Fin k → ZMod p)
    (hx : Function.Injective x) :
    (vinogradovPowerSumJacobian x).det ≠ 0 := by
  apply det_vinogradovPowerSumJacobian_ne_zero x
  · intro j
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hp_le : p ≤ j.val + 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  · exact hx

end

end ZeroFreeRegion.VinogradovKorobov
