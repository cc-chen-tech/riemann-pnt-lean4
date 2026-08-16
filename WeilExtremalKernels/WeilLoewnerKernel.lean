import WeilExtremalKernels.IntegerKernelCutoff

/-!
# The global Loewner plus rank-two Weil kernel

The CCM assembly has the global integer-indexed form

`L(p0, p0') + 2 c c^T - 2 s s^T`,

where off-diagonal entries of `L` are divided differences and diagonal
entries are supplied by a derivative formula.  This module formalizes that
structure independently of the special functions used to evaluate `p0`.

The auxiliary and CCM analytic routes still need a separate pointwise
identity theorem.  No numerical value or RH statement is introduced here.
-/

namespace WeilExtremalKernels

/-- Integer-indexed Loewner kernel with a separately supplied diagonal
derivative. -/
def integerLoewnerKernel
    (value derivative : Int -> Real) (m n : Int) : Real :=
  if m = n then derivative n
  else (value m - value n) / ((m - n : Int) : Real)

/-- A Loewner divided-difference kernel is symmetric. -/
theorem integerLoewnerKernel_symmetric
    (value derivative : Int -> Real) (m n : Int) :
    integerLoewnerKernel value derivative m n =
      integerLoewnerKernel value derivative n m := by
  by_cases hmn : m = n
  · subst n
    rfl
  · have hnm : n != m := by
      intro h
      exact hmn h.symm
    unfold integerLoewnerKernel
    rw [if_neg hmn, if_neg hnm]
    have hden :
        ((n - m : Int) : Real) = -((m - n : Int) : Real) := by
      push_cast
      ring
    rw [hden]
    ring

/-- Loewner kernels are additive in the value and derivative data. -/
theorem integerLoewnerKernel_add
    (a da p dp : Int -> Real) (m n : Int) :
    integerLoewnerKernel
        (fun k => a k + p k) (fun k => da k + dp k) m n =
      integerLoewnerKernel a da m n +
        integerLoewnerKernel p dp m n := by
  by_cases hmn : m = n
  · subst n
    simp [integerLoewnerKernel]
  · simp [integerLoewnerKernel, hmn]
    ring

/-- The pole contribution is a difference of two rank-one kernels. -/
def rankTwoPoleKernel
    (poleC poleS : Int -> Real) (m n : Int) : Real :=
  2 * (poleC m * poleC n - poleS m * poleS n)

theorem rankTwoPoleKernel_symmetric
    (poleC poleS : Int -> Real) (m n : Int) :
    rankTwoPoleKernel poleC poleS m n =
      rankTwoPoleKernel poleC poleS n m := by
  unfold rankTwoPoleKernel
  ring

/-- Global CCM kernel before choosing concrete special-function formulas. -/
def ccmIntegerKernel
    (p0 p0Derivative poleC poleS : Int -> Real)
    (m n : Int) : Real :=
  integerLoewnerKernel p0 p0Derivative m n +
    rankTwoPoleKernel poleC poleS m n

theorem ccmIntegerKernel_symmetric
    (p0 p0Derivative poleC poleS : Int -> Real) (m n : Int) :
    ccmIntegerKernel p0 p0Derivative poleC poleS m n =
      ccmIntegerKernel p0 p0Derivative poleC poleS n m := by
  unfold ccmIntegerKernel
  rw [integerLoewnerKernel_symmetric,
    rankTwoPoleKernel_symmetric]

/-- Exact decomposition into archimedean Loewner, prime Loewner, and pole
sources. -/
theorem ccmIntegerKernel_source_decomposition
    (arch archDerivative prime primeDerivative poleC poleS : Int -> Real)
    (m n : Int) :
    ccmIntegerKernel
        (fun k => arch k + prime k)
        (fun k => archDerivative k + primeDerivative k)
        poleC poleS m n =
      integerLoewnerKernel arch archDerivative m n +
        integerLoewnerKernel prime primeDerivative m n +
        rankTwoPoleKernel poleC poleS m n := by
  unfold ccmIntegerKernel
  rw [integerLoewnerKernel_add]

/-- Every cutoff of the global CCM kernel is symmetric. -/
theorem integerKernelCutoffMatrix_ccm_symmetric
    (p0 p0Derivative poleC poleS : Int -> Real)
    (N : Nat) (i j : Fin (2 * N + 1)) :
    integerKernelCutoffMatrix
        (ccmIntegerKernel p0 p0Derivative poleC poleS) N i j =
      integerKernelCutoffMatrix
        (ccmIntegerKernel p0 p0Derivative poleC poleS) N j i := by
  unfold integerKernelCutoffMatrix
  exact ccmIntegerKernel_symmetric
    p0 p0Derivative poleC poleS _ _

/-- Positivity of one CCM cutoff automatically passes to all smaller centered
cutoffs because the formula is one global integer kernel. -/
theorem ccmIntegerKernel_all_smaller_pos
    (p0 p0Derivative poleC poleS : Int -> Real)
    (N : Nat)
    (hN :
      forall x, x != 0 ->
        0 < quadraticForm
          (integerKernelCutoffMatrix
            (ccmIntegerKernel p0 p0Derivative poleC poleS) N) x) :
    forall M (hMN : M <= N) x, x != 0 ->
      0 < quadraticForm
        (integerKernelCutoffMatrix
          (ccmIntegerKernel p0 p0Derivative poleC poleS) M) x :=
  integerKernelCutoffMatrix_all_smaller_pos
    (ccmIntegerKernel p0 p0Derivative poleC poleS) N hN

/-- Pointwise equality of two global kernels implies equality of every finite
cutoff matrix.  This is the final algebraic interface for the auxiliary/CCM
analytic identity. -/
theorem integerKernelCutoffMatrix_eq_of_pointwise
    (K₁ K₂ : Int -> Int -> Real)
    (hK : forall m n, K₁ m n = K₂ m n)
    (N : Nat) :
    integerKernelCutoffMatrix K₁ N =
      integerKernelCutoffMatrix K₂ N := by
  funext i j
  unfold integerKernelCutoffMatrix
  exact hK _ _

end WeilExtremalKernels
