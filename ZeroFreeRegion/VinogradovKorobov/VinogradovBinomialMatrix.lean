import ZeroFreeRegion.VinogradovKorobov.VinogradovLinearLift
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Vandermonde

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The consecutive evaluation points occurring in Wooley's triangular
elimination.  They run from `k - r + 1` through `k`. -/
def vinogradovBinomialPoint (k r : ℕ) (i : Fin r) : ℕ :=
  k - r + i.val + 1

/-- The binomial-coefficient matrix used to eliminate the translated
high-degree congruences.  Rows are the consecutive degrees
`k-r+1, ..., k`, while columns are the unknown degrees `1, ..., r`. -/
def vinogradovBinomialMatrix (p k r : ℕ) : Matrix (Fin r) (Fin r) (ZMod p) :=
  fun i j ↦
    ((Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℕ) : ZMod p)

/-- The falling-factorial evaluation matrix with the common linear factor
removed from every row of `vinogradovBinomialMatrix`. -/
def vinogradovDescPochhammerMatrix (p k r : ℕ) :
    Matrix (Fin r) (Fin r) (ZMod p) :=
  Matrix.of fun i j ↦
    (descPochhammer (ZMod p) j.val).eval
      ((k - r + i.val : ℕ) : ZMod p)

/-- Multiplying the binomial columns by their factorial denominators turns
the matrix into a row-scaled falling-factorial evaluation matrix. -/
theorem vinogradovBinomialMatrix_mul_factorialDiagonal
    (p k r : ℕ) :
    vinogradovBinomialMatrix p k r *
        Matrix.diagonal (fun j : Fin r ↦ ((j.val + 1).factorial : ZMod p)) =
      Matrix.diagonal
          (fun i : Fin r ↦ (vinogradovBinomialPoint k r i : ZMod p)) *
        vinogradovDescPochhammerMatrix p k r := by
  classical
  ext i j
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp only [vinogradovBinomialMatrix, vinogradovBinomialPoint,
        vinogradovDescPochhammerMatrix, Matrix.diagonal_apply_eq,
        Matrix.of_apply]
      rw [descPochhammer_eval_eq_descFactorial]
      norm_cast
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose,
        Nat.succ_descFactorial_succ]
    · intro b _ hbi
      rw [Matrix.diagonal_apply_ne _ hbi.symm]
      simp
    · simp
  · intro b _ hbj
    rw [Matrix.diagonal_apply_ne _ hbj]
    simp
  · simp

/-- The falling-factorial evaluation matrix has the same determinant as the
Vandermonde matrix on the shifted consecutive points. -/
theorem det_vinogradovDescPochhammerMatrix
    (p k r : ℕ) [Fact p.Prime] :
    (vinogradovDescPochhammerMatrix p k r).det =
      (Matrix.vandermonde
        (fun i : Fin r ↦ ((k - r + i.val : ℕ) : ZMod p))).det := by
  symm
  exact Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i : Fin r ↦ ((k - r + i.val : ℕ) : ZMod p))
    (fun i : Fin r ↦ descPochhammer (ZMod p) i.val)
    (fun i ↦ descPochhammer_natDegree (ZMod p) i.val)
    (fun i ↦ monic_descPochhammer (ZMod p) i.val)

/-- Consecutive shifted natural numbers below `p` remain distinct in
`ZMod p`. -/
theorem injective_vinogradovBinomialBase_zmod
    (p k r : ℕ) (hrk : r ≤ k) (hkp : k < p) :
    Function.Injective
      (fun i : Fin r ↦ ((k - r + i.val : ℕ) : ZMod p)) := by
  intro i j hij
  have hi : k - r + i.val < p := by omega
  have hj : k - r + j.val < p := by omega
  have hval := congrArg ZMod.val hij
  rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hval
  apply Fin.ext
  omega

/-- The factorial column factors are nonzero modulo a prime larger than
`k`, provided `r ≤ k`. -/
theorem vinogradovFactorialDiagonal_ne_zero
    (p k r : ℕ) [Fact p.Prime] (hrk : r ≤ k) (hkp : k < p)
    (j : Fin r) :
    ((j.val + 1).factorial : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hp_le : p ≤ j.val + 1 :=
    (Fact.out : p.Prime).dvd_factorial.mp hdvd
  omega

/-- The consecutive row factors are nonzero modulo a prime larger than
`k`. -/
theorem vinogradovBinomialPoint_zmod_ne_zero
    (p k r : ℕ) [Fact p.Prime] (hrk : r ≤ k)
    (hkp : k < p) (i : Fin r) :
    (vinogradovBinomialPoint k r i : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hp_le : p ≤ vinogradovBinomialPoint k r i :=
    Nat.le_of_dvd (by simp only [vinogradovBinomialPoint]; omega) hdvd
  have hpoint_le : vinogradovBinomialPoint k r i ≤ k := by
    simp only [vinogradovBinomialPoint]
    omega
  omega

/-- Wooley's consecutive binomial matrix is nonsingular modulo every prime
`p > k`.  This is the algebraic invertibility needed by the translated
high-degree congruence elimination. -/
theorem det_vinogradovBinomialMatrix_zmod_ne_zero
    (p k r : ℕ) [Fact p.Prime] (hrk : r ≤ k)
    (hkp : k < p) :
    (vinogradovBinomialMatrix p k r).det ≠ 0 := by
  have hfactorial :
      (∏ j : Fin r, ((j.val + 1).factorial : ZMod p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦
      vinogradovFactorialDiagonal_ne_zero p k r hrk hkp j
  have hrow :
      (∏ i : Fin r, (vinogradovBinomialPoint k r i : ZMod p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦
      vinogradovBinomialPoint_zmod_ne_zero p k r hrk hkp i
  have heval : (vinogradovDescPochhammerMatrix p k r).det ≠ 0 := by
    rw [det_vinogradovDescPochhammerMatrix]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (injective_vinogradovBinomialBase_zmod p k r hrk hkp)
  have hdet := congrArg Matrix.det
    (vinogradovBinomialMatrix_mul_factorialDiagonal p k r)
  rw [Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_mul, Matrix.det_diagonal] at hdet
  intro hzero
  rw [hzero, zero_mul] at hdet
  exact (mul_ne_zero hrow heval) hdet.symm

/-- Every translated triangular residue vector therefore has a unique
correction vector modulo `p`. -/
theorem existsUnique_vinogradovBinomialMatrix_mulVec_eq
    (p k r : ℕ) [Fact p.Prime] (hrk : r ≤ k)
    (hkp : k < p) (b : Fin r → ZMod p) :
    ∃! x, (vinogradovBinomialMatrix p k r).mulVec x = b :=
  existsUnique_mulVec_eq_of_det_ne_zero (vinogradovBinomialMatrix p k r)
    (det_vinogradovBinomialMatrix_zmod_ne_zero p k r hrk hkp) b

/-- Reducing the prime-power binomial matrix modulo `p` gives the original
binomial matrix modulo `p`. -/
theorem map_vinogradovBinomialMatrix_primePower
    (p k r N : ℕ) (hN : 0 < N) :
    (vinogradovBinomialMatrix (p ^ N) k r).map
        (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) =
      vinogradovBinomialMatrix p k r := by
  ext i j
  simp [vinogradovBinomialMatrix]

/-- Nonsingularity modulo `p` lifts to a unit determinant modulo every
positive power `p^N`. -/
theorem isUnit_det_vinogradovBinomialMatrix_zmod_primePower
    (p k r N : ℕ) [Fact p.Prime] (hrk : r ≤ k) (hkp : k < p)
    (hN : 0 < N) :
    IsUnit (vinogradovBinomialMatrix (p ^ N) k r).det := by
  letI : NeZero (p ^ N) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let A := vinogradovBinomialMatrix (p ^ N) k r
  let reduce := ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)
  have hreduce :
      reduce A.det = (vinogradovBinomialMatrix p k r).det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det
      (map_vinogradovBinomialMatrix_primePower p k r N hN)
  have hnot : ¬ p ∣ A.det.val := by
    intro hdvd
    have hzero : reduce A.det = 0 := by
      rw [← ZMod.natCast_zmod_val A.det]
      simp only [map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have : (vinogradovBinomialMatrix p k r).det = 0 := by
      rw [← hreduce, hzero]
    exact (det_vinogradovBinomialMatrix_zmod_ne_zero p k r hrk hkp) this
  rw [← ZMod.natCast_zmod_val A.det]
  exact (ZMod.isUnit_iff_coprime _ _).mpr
    ((Fact.out : p.Prime).coprime_pow_of_not_dvd hnot)

/-- The translated binomial system has a unique solution modulo every
positive prime power. -/
theorem existsUnique_vinogradovBinomialMatrix_primePower_mulVec_eq
    (p k r N : ℕ) [Fact p.Prime] (hrk : r ≤ k) (hkp : k < p)
    (hN : 0 < N) (b : Fin r → ZMod (p ^ N)) :
    ∃! x, (vinogradovBinomialMatrix (p ^ N) k r).mulVec x = b :=
  existsUnique_mulVec_eq_of_isUnit_det
    (vinogradovBinomialMatrix (p ^ N) k r)
    (isUnit_det_vinogradovBinomialMatrix_zmod_primePower
      p k r N hrk hkp hN) b

end

end ZeroFreeRegion.VinogradovKorobov
