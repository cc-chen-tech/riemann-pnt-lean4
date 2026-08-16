import WeilExtremalKernels.CenteredPrincipalSection
import WeilExtremalKernels.WeilCoordinateBridge

/-!
# Cutoff matrices of a global integer kernel

An analytic Weil entry formula has the natural shape

`K c m n`, with integer Fourier indices `m,n`.

The cutoff `N` should only restrict those global indices to `-N, ..., N`; it
must not change the value of an already present entry.  With this definition,
centered nesting is a theorem rather than an additional assumption.

This module supplies that theorem abstractly.  It does not formalize the
specific digamma, prime-power, or pole formulas used by the experiments.
-/

namespace WeilExtremalKernels

/-- A coordinate principal section has the expected entrywise value. -/
theorem principalSection_apply {m n : Nat}
    (A : FiniteMatrix n) (f : Fin m ↪ Fin n)
    (i j : Fin m) :
    principalSection A f i j = A (f i) (f j) := by
  simp [principalSection, congruenceMatrix, injectionBasisMatrix,
    f.injective.eq_iff]

/-- The centered embedding preserves the exact integer row label. -/
theorem registeredFullFourierIndex_centeredFinEmbedding
    {M N : Nat} (hMN : M <= N) (i : Fin (2 * M + 1)) :
    registeredFullFourierIndex N (centeredFinEmbedding hMN i) =
      registeredFullFourierIndex M i := by
  unfold registeredFullFourierIndex centeredFinEmbedding
  dsimp
  omega

/-- Restriction of a global integer kernel to Fourier rows `-N, ..., N`. -/
def integerKernelCutoffMatrix
    (K : Int -> Int -> Real) (N : Nat) :
    FiniteMatrix (2 * N + 1) :=
  fun i j =>
    K (registeredFullFourierIndex N i)
      (registeredFullFourierIndex N j)

/-- Cutoffs of one global integer kernel are exactly centered principal
sections of every larger cutoff. -/
theorem integerKernelCutoffMatrix_centered_nested
    (K : Int -> Int -> Real)
    {M N : Nat} (hMN : M <= N) :
    integerKernelCutoffMatrix K M =
      centeredPrincipalSection hMN (integerKernelCutoffMatrix K N) := by
  funext i j
  rw [principalSection_apply]
  unfold integerKernelCutoffMatrix
  rw [registeredFullFourierIndex_centeredFinEmbedding hMN i,
    registeredFullFourierIndex_centeredFinEmbedding hMN j]

/-- Strict positivity of one global-kernel cutoff passes to every smaller
cutoff without a separate nesting hypothesis. -/
theorem integerKernelCutoffMatrix_all_smaller_pos
    (K : Int -> Int -> Real) (N : Nat)
    (hN :
      forall x, x != 0 ->
        0 < quadraticForm (integerKernelCutoffMatrix K N) x) :
    forall M (hMN : M <= N) x, x != 0 ->
      0 < quadraticForm (integerKernelCutoffMatrix K M) x := by
  intro M hMN x hx
  rw [integerKernelCutoffMatrix_centered_nested K hMN]
  exact quadraticForm_centeredPrincipalSection_pos
    hMN (integerKernelCutoffMatrix K N) hN x hx

/-- Parameterized analytic kernels, such as `K c m n`, inherit the same
cutoff nesting at each fixed parameter `c`. -/
theorem parameterizedIntegerKernelCutoffMatrix_all_smaller_pos
    (K : Nat -> Int -> Int -> Real) (c N : Nat)
    (hN :
      forall x, x != 0 ->
        0 < quadraticForm (integerKernelCutoffMatrix (K c) N) x) :
    forall M (hMN : M <= N) x, x != 0 ->
      0 < quadraticForm (integerKernelCutoffMatrix (K c) M) x :=
  integerKernelCutoffMatrix_all_smaller_pos (K c) N hN

end WeilExtremalKernels
