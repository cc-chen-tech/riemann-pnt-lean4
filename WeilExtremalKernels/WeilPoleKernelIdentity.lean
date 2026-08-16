import WeilExtremalKernels.WeilLoewnerKernel

/-!
# Expanded versus rank-two pole kernels

The auxiliary route emits one expanded rational expression in the two
Fourier indices.  The CCM route emits a difference of two outer products.
After extracting a square root of the positive logarithmic scale, the two
expressions are algebraically identical.

This module proves the identity over abstract real parameters.  It does not
use interval arithmetic or special functions.
-/

namespace WeilExtremalKernels

/-- Common denominator of the pole factors after clearing quarters. -/
def poleDenominator (L : Real) (n : Int) : Real :=
  L ^ 2 + 16 * Real.pi ^ 2 * (n : Real) ^ 2

/-- Algebraically normalized CCM cosine factor. -/
def normalizedPoleC
    (L root sinhQuarter : Real) (n : Int) : Real :=
  4 * L * root * sinhQuarter / poleDenominator L n

/-- Algebraically normalized CCM sine factor. -/
def normalizedPoleS
    (L root sinhQuarter : Real) (n : Int) : Real :=
  16 * Real.pi * root * (n : Real) * sinhQuarter /
    poleDenominator L n

/-- Expanded pole formula used by the direct auxiliary assembly. -/
def expandedPoleKernel
    (L sinhQuarter : Real) (m n : Int) : Real :=
  32 * L * sinhQuarter ^ 2 *
      (L ^ 2 -
        16 * Real.pi ^ 2 * (m : Real) * (n : Real)) /
    (poleDenominator L m * poleDenominator L n)

theorem poleDenominator_pos
    {L : Real} (hL : 0 < L) (n : Int) :
    0 < poleDenominator L n := by
  unfold poleDenominator
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  have hfrequency :
      0 <= 16 * Real.pi ^ 2 * (n : Real) ^ 2 := by
    positivity
  linarith

/-- The factorized rank-two formula equals the expanded rational formula
whenever `root^2 = L`. -/
theorem rankTwoPoleKernel_normalized_eq_expanded
    (L root sinhQuarter : Real) (m n : Int)
    (hroot : root ^ 2 = L)
    (hm : poleDenominator L m != 0)
    (hn : poleDenominator L n != 0) :
    rankTwoPoleKernel
        (normalizedPoleC L root sinhQuarter)
        (normalizedPoleS L root sinhQuarter) m n =
      expandedPoleKernel L sinhQuarter m n := by
  unfold rankTwoPoleKernel normalizedPoleC normalizedPoleS
    expandedPoleKernel
  calc
    2 *
        (4 * L * root * sinhQuarter / poleDenominator L m *
            (4 * L * root * sinhQuarter / poleDenominator L n) -
          16 * Real.pi * root * (m : Real) * sinhQuarter /
              poleDenominator L m *
            (16 * Real.pi * root * (n : Real) * sinhQuarter /
              poleDenominator L n)) =
        32 * root ^ 2 * sinhQuarter ^ 2 *
            (L ^ 2 -
              16 * Real.pi ^ 2 * (m : Real) * (n : Real)) /
          (poleDenominator L m * poleDenominator L n) := by
      field_simp [hm, hn]
      ring
    _ = 32 * L * sinhQuarter ^ 2 *
            (L ^ 2 -
              16 * Real.pi ^ 2 * (m : Real) * (n : Real)) /
          (poleDenominator L m * poleDenominator L n) := by
      rw [hroot]

/-- For a positive logarithmic scale, the canonical root is `sqrt L`, and
the normalized CCM pole factors equal the expanded auxiliary kernel at all
integer indices. -/
theorem rankTwoPoleKernel_sqrt_eq_expanded
    {L : Real} (hL : 0 < L)
    (sinhQuarter : Real) (m n : Int) :
    rankTwoPoleKernel
        (normalizedPoleC L (Real.sqrt L) sinhQuarter)
        (normalizedPoleS L (Real.sqrt L) sinhQuarter) m n =
      expandedPoleKernel L sinhQuarter m n := by
  apply rankTwoPoleKernel_normalized_eq_expanded
  · exact Real.sq_sqrt hL.le
  · exact (poleDenominator_pos hL m).ne'
  · exact (poleDenominator_pos hL n).ne'

end WeilExtremalKernels
