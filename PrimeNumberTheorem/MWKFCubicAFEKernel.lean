import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Pole-cancelled kernel for the cubic MWKF approximate functional equation

This file fixes the exact algebraic kernel from the paper proof.  It proves
all six prescribed zeros, its evenness, and its normalization at the origin.
No contour shift or asymptotic estimate is asserted here.
-/

/-- The point `1/2+it` on the critical line. -/
noncomputable def cubicCriticalPoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + I * t

/-- The polynomial part that cancels the four moving completed-zeta poles and
the two fixed half-boundary poles. -/
noncomputable def cubicAFEPoleCanceller (t : ℝ) (z : ℂ) : ℂ :=
  (1 - 4 * z ^ 2) *
    (1 - z ^ 2 / cubicCriticalPoint t ^ 2) *
    (1 - z ^ 2 / (1 - cubicCriticalPoint t) ^ 2)

/-- The complete even Gaussian AFE kernel `G_t(z)`. -/
noncomputable def cubicAFEKernelG (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z ^ 2) * cubicAFEPoleCanceller t z

theorem cubicCriticalPoint_ne_zero (t : ℝ) :
    cubicCriticalPoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [cubicCriticalPoint] at hre

theorem one_sub_cubicCriticalPoint_ne_zero (t : ℝ) :
    1 - cubicCriticalPoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [cubicCriticalPoint] at hre

theorem cubicAFEKernelG_zero (t : ℝ) :
    cubicAFEKernelG t 0 = 1 := by
  simp [cubicAFEKernelG, cubicAFEPoleCanceller]

theorem cubicAFEKernelG_neg (t : ℝ) (z : ℂ) :
    cubicAFEKernelG t (-z) = cubicAFEKernelG t z := by
  simp [cubicAFEKernelG, cubicAFEPoleCanceller]

theorem cubicAFEKernelG_at_criticalPoint (t : ℝ) :
    cubicAFEKernelG t (cubicCriticalPoint t) = 0 := by
  simp [cubicAFEKernelG, cubicAFEPoleCanceller,
    cubicCriticalPoint_ne_zero t]

theorem cubicAFEKernelG_at_neg_criticalPoint (t : ℝ) :
    cubicAFEKernelG t (-cubicCriticalPoint t) = 0 := by
  rw [cubicAFEKernelG_neg]
  exact cubicAFEKernelG_at_criticalPoint t

theorem cubicAFEKernelG_at_one_sub_criticalPoint (t : ℝ) :
    cubicAFEKernelG t (1 - cubicCriticalPoint t) = 0 := by
  simp [cubicAFEKernelG, cubicAFEPoleCanceller,
    one_sub_cubicCriticalPoint_ne_zero t]

theorem cubicAFEKernelG_at_criticalPoint_sub_one (t : ℝ) :
    cubicAFEKernelG t (cubicCriticalPoint t - 1) = 0 := by
  rw [show cubicCriticalPoint t - 1 = -(1 - cubicCriticalPoint t) by ring,
    cubicAFEKernelG_neg]
  exact cubicAFEKernelG_at_one_sub_criticalPoint t

theorem cubicAFEKernelG_at_half (t : ℝ) :
    cubicAFEKernelG t (1 / 2 : ℂ) = 0 := by
  have hhalf : (1 - 4 * (1 / 2 : ℂ) ^ 2) = 0 := by norm_num
  unfold cubicAFEKernelG cubicAFEPoleCanceller
  rw [hhalf]
  simp

theorem cubicAFEKernelG_at_neg_half (t : ℝ) :
    cubicAFEKernelG t (-1 / 2 : ℂ) = 0 := by
  calc
    cubicAFEKernelG t (-1 / 2 : ℂ) =
        cubicAFEKernelG t (-(1 / 2 : ℂ)) := by congr 1; ring
    _ = cubicAFEKernelG t (1 / 2 : ℂ) := cubicAFEKernelG_neg t _
    _ = 0 := cubicAFEKernelG_at_half t

end MWKFCubic
end PrimeNumberTheorem
