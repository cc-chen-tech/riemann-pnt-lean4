import WeilExtremalKernels.ArchimedeanImproperTail
import WeilExtremalKernels.BasisChangeTransfer

/-!
# The registered full Fourier coordinate bridge

The interval assembly artifacts order their full matrix by the integer list

`-N, -N + 1, ..., N`.

The finite archimedean-tail formalization indexes the same list by
`Fin (2 * N + 1)`, assigning row `i` the real coordinate `i.val - N`.
Thus the full-matrix coordinate bridge is the identity matrix.  There is no
diagonal rescaling and no even-sector contraction in this bridge.

This module proves that identity exactly and supplies the corresponding
left-inverse certificate.  It does not identify the separate full-to-even
embedding.
-/

namespace WeilExtremalKernels

/-- Integer label of row `i` in the registered full Fourier order. -/
def registeredFullFourierIndex (N : ℕ) (i : Fin (2 * N + 1)) : ℤ :=
  (i.val : ℤ) - (N : ℤ)

/-- The registered integer row label, cast to `R`, is exactly the coordinate
used by the formalized archimedean tail. -/
theorem registeredFullFourierIndex_cast_eq_centeredIndexCoordinate
    (N : ℕ) (i : Fin (2 * N + 1)) :
    (registeredFullFourierIndex N i : ℝ) =
      centeredIndexCoordinate N i := by
  simp [registeredFullFourierIndex, centeredIndexCoordinate]

/-- The exact basis matrix connecting the registered full artifact order to
the Lean finite-tail order. -/
def fullFourierIdentityBasis (N : ℕ) :
    RectangularMatrix (2 * N + 1) (2 * N + 1) :=
  1

/-- Applying the full Fourier bridge changes no coordinate vector. -/
theorem applyRectangularMatrix_fullFourierIdentityBasis
    (N : ℕ) (x : FiniteVector (2 * N + 1)) :
    applyRectangularMatrix (fullFourierIdentityBasis N) x = x := by
  funext i
  simp [applyRectangularMatrix, fullFourierIdentityBasis]

/-- The identity bridge is its own exact left inverse. -/
def fullFourierIdentityLeftInverseCertificate (N : ℕ) :
    LeftInverseCertificate (fullFourierIdentityBasis N) where
  leftInverse := fullFourierIdentityBasis N
  left_inverse :=
    applyRectangularMatrix_fullFourierIdentityBasis N

/-- Congruence by the registered full Fourier bridge leaves every finite
matrix unchanged. -/
theorem congruenceMatrix_fullFourierIdentityBasis
    (N : ℕ) (A : FiniteMatrix (2 * N + 1)) :
    congruenceMatrix A (fullFourierIdentityBasis N) = A := by
  funext i j
  simp [congruenceMatrix, fullFourierIdentityBasis]

/-- The quadratic form represented by a full artifact matrix is unchanged by
the exact registered-coordinate bridge. -/
theorem quadraticForm_fullFourierIdentityBasis
    (N : ℕ) (A : FiniteMatrix (2 * N + 1))
    (x : FiniteVector (2 * N + 1)) :
    quadraticForm
        (congruenceMatrix A (fullFourierIdentityBasis N)) x =
      quadraticForm A x := by
  rw [congruenceMatrix_fullFourierIdentityBasis]

/-- The cutoff-free actual archimedean tail is already expressed in the
registered full Fourier coordinates. -/
theorem congruenceMatrix_paperActualArchimedeanRankTwoTail_fullFourierIdentity
    (N : ℕ) (L rho T : ℝ) :
    congruenceMatrix
        (paperActualArchimedeanRankTwoTail N L rho T)
        (fullFourierIdentityBasis N) =
      paperActualArchimedeanRankTwoTail N L rho T :=
  congruenceMatrix_fullFourierIdentityBasis N _

end WeilExtremalKernels
