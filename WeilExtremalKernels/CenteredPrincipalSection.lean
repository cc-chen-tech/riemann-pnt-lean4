import WeilExtremalKernels.BasisChangeTransfer
import WeilExtremalKernels.ArchimedeanRankTwoTail

/-!
# Centered principal sections

For `M <= N`, the Fourier indices `-M, ..., M` occur as the centered
consecutive block inside `-N, ..., N`.  This module constructs that exact
coordinate injection and proves that positive semidefiniteness and strict
positivity pass from a full matrix to its centered principal section.

To apply the result to a family of analytically assembled Weil matrices, one
must separately prove that the matrix assembled at cutoff `M` is exactly this
principal section of the matrix assembled at cutoff `N`.
-/

namespace WeilExtremalKernels

/-- Matrix of a coordinate injection `f : Fin m -> Fin n`. -/
def injectionBasisMatrix {m n : Nat} (f : Fin m ↪ Fin n) :
    RectangularMatrix n m :=
  fun i j => if i = f j then 1 else 0

/-- The transpose coordinate selector is an exact left inverse of an
injection basis matrix. -/
def injectionBasisLeftInverseCertificate {m n : Nat}
    (f : Fin m ↪ Fin n) :
    LeftInverseCertificate (injectionBasisMatrix f) where
  leftInverse := fun j i => if i = f j then 1 else 0
  left_inverse := by
    intro x
    funext j
    simp [applyRectangularMatrix, injectionBasisMatrix, f.injective.eq_iff]

/-- Exact principal section selected by a coordinate injection. -/
def principalSection {m n : Nat}
    (A : FiniteMatrix n) (f : Fin m ↪ Fin n) : FiniteMatrix m :=
  congruenceMatrix A (injectionBasisMatrix f)

theorem quadraticForm_principalSection {m n : Nat}
    (A : FiniteMatrix n) (f : Fin m ↪ Fin n)
    (x : FiniteVector m) :
    quadraticForm (principalSection A f) x =
      quadraticForm A
        (applyRectangularMatrix (injectionBasisMatrix f) x) :=
  quadraticForm_congruenceMatrix A (injectionBasisMatrix f) x

theorem quadraticForm_principalSection_nonneg {m n : Nat}
    (A : FiniteMatrix n) (f : Fin m ↪ Fin n)
    (hA : forall x, 0 <= quadraticForm A x) :
    forall x, 0 <= quadraticForm (principalSection A f) x :=
  quadraticForm_congruenceMatrix_nonneg
    A (injectionBasisMatrix f) hA

theorem quadraticForm_principalSection_pos {m n : Nat}
    (A : FiniteMatrix n) (f : Fin m ↪ Fin n)
    (hA : forall x, x != 0 -> 0 < quadraticForm A x) :
    forall x, x != 0 -> 0 < quadraticForm (principalSection A f) x :=
  quadraticForm_congruenceMatrix_pos
    A (injectionBasisMatrix f)
    (injectionBasisLeftInverseCertificate f) hA

/-- Centered inclusion of Fourier rows `-M, ..., M` into `-N, ..., N`. -/
def centeredFinEmbedding {M N : Nat} (hMN : M <= N) :
    Fin (2 * M + 1) ↪ Fin (2 * N + 1) where
  toFun i :=
    ⟨i.val + (N - M), by
      have hi : i.val < 2 * M + 1 := i.isLt
      omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    dsimp at hij
    omega

/-- The centered inclusion preserves the integer Fourier coordinate exactly. -/
theorem centeredIndexCoordinate_centeredFinEmbedding
    {M N : Nat} (hMN : M <= N) (i : Fin (2 * M + 1)) :
    centeredIndexCoordinate N (centeredFinEmbedding hMN i) =
      centeredIndexCoordinate M i := by
  unfold centeredIndexCoordinate centeredFinEmbedding
  rw [Nat.cast_add, Nat.cast_sub hMN]
  ring

/-- The centered principal block of a `(2N+1)` matrix. -/
def centeredPrincipalSection {M N : Nat} (hMN : M <= N)
    (A : FiniteMatrix (2 * N + 1)) : FiniteMatrix (2 * M + 1) :=
  principalSection A (centeredFinEmbedding hMN)

theorem quadraticForm_centeredPrincipalSection_nonneg
    {M N : Nat} (hMN : M <= N)
    (A : FiniteMatrix (2 * N + 1))
    (hA : forall x, 0 <= quadraticForm A x) :
    forall x, 0 <= quadraticForm (centeredPrincipalSection hMN A) x :=
  quadraticForm_principalSection_nonneg
    A (centeredFinEmbedding hMN) hA

theorem quadraticForm_centeredPrincipalSection_pos
    {M N : Nat} (hMN : M <= N)
    (A : FiniteMatrix (2 * N + 1))
    (hA : forall x, x != 0 -> 0 < quadraticForm A x) :
    forall x, x != 0 ->
      0 < quadraticForm (centeredPrincipalSection hMN A) x :=
  quadraticForm_principalSection_pos
    A (centeredFinEmbedding hMN) hA

/-- If an assembled family is exactly nested by centered principal sections,
strict positivity at one cutoff transfers to every smaller cutoff. -/
theorem all_smaller_cutoffs_pos_of_centered_nested
    (Q : Nat -> (n : Nat) -> FiniteMatrix (2 * n + 1))
    (c N : Nat)
    (hnested :
      forall M (hMN : M <= N),
        Q c M = centeredPrincipalSection hMN (Q c N))
    (hN : forall x, x != 0 -> 0 < quadraticForm (Q c N) x) :
    forall M (hMN : M <= N) x, x != 0 ->
      0 < quadraticForm (Q c M) x := by
  intro M hMN x hx
  rw [hnested M hMN]
  exact quadraticForm_centeredPrincipalSection_pos
    hMN (Q c N) hN x hx

end WeilExtremalKernels
