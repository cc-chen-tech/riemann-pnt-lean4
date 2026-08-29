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

/-- The explicit entire extension of
`G_t(z) Lambda(s_t+z) Lambda(1-s_t+z)`.  Each bracket is the numerator
obtained after inserting Mathlib's entire `completedRiemannZeta₀` and
clearing the two simple-pole denominators. -/
noncomputable def cubicAFECompletedExtension (t : ℝ) (z : ℂ) : ℂ :=
  let s := cubicCriticalPoint t
  let u := 1 - s
  Complex.exp (z ^ 2) * (1 - 4 * z ^ 2) / (s ^ 2 * u ^ 2) *
    (completedRiemannZeta₀ (s + z) * (s + z) * (u - z) -
      (u - z) - (s + z)) *
    (completedRiemannZeta₀ (u + z) * (u + z) * (s - z) -
      (s - z) - (u + z))

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

/-- The pole-cleared completed product is an entire function of the shift. -/
theorem differentiable_cubicAFECompletedExtension (t : ℝ) :
    Differentiable ℂ (cubicAFECompletedExtension t) := by
  have hcompleted : Differentiable ℂ completedRiemannZeta₀ :=
    differentiable_completedZeta₀
  unfold cubicAFECompletedExtension
  fun_prop

set_option maxRecDepth 10000 in
/-- Away from the original four poles, the explicit entire extension agrees
with the literal product of the kernel and the two completed zeta factors. -/
theorem cubicAFECompletedExtension_eq
    (t : ℝ) (z : ℂ)
    (hsplus : cubicCriticalPoint t + z ≠ 0)
    (husub : 1 - cubicCriticalPoint t - z ≠ 0)
    (huplus : 1 - cubicCriticalPoint t + z ≠ 0)
    (hssub : cubicCriticalPoint t - z ≠ 0) :
    cubicAFECompletedExtension t z =
      cubicAFEKernelG t z *
        completedRiemannZeta (cubicCriticalPoint t + z) *
        completedRiemannZeta (1 - cubicCriticalPoint t + z) := by
  have hs : cubicCriticalPoint t ≠ 0 := cubicCriticalPoint_ne_zero t
  have hu : 1 - cubicCriticalPoint t ≠ 0 :=
    one_sub_cubicCriticalPoint_ne_zero t
  have hLambdaLeft :
      completedRiemannZeta (cubicCriticalPoint t + z) =
        (completedRiemannZeta₀ (cubicCriticalPoint t + z) *
              (cubicCriticalPoint t + z) *
              (1 - cubicCriticalPoint t - z) -
            (1 - cubicCriticalPoint t - z) -
            (cubicCriticalPoint t + z)) /
          ((cubicCriticalPoint t + z) *
            (1 - cubicCriticalPoint t - z)) := by
    rw [completedRiemannZeta_eq]
    rw [show 1 - (cubicCriticalPoint t + z) =
      1 - cubicCriticalPoint t - z by ring]
    field_simp [hsplus, husub]
  have hLambdaRight :
      completedRiemannZeta (1 - cubicCriticalPoint t + z) =
        (completedRiemannZeta₀ (1 - cubicCriticalPoint t + z) *
              (1 - cubicCriticalPoint t + z) *
              (cubicCriticalPoint t - z) -
            (cubicCriticalPoint t - z) -
            (1 - cubicCriticalPoint t + z)) /
          ((1 - cubicCriticalPoint t + z) *
            (cubicCriticalPoint t - z)) := by
    rw [completedRiemannZeta_eq]
    rw [show 1 - (1 - cubicCriticalPoint t + z) =
      cubicCriticalPoint t - z by ring]
    field_simp [huplus, hssub]
  rw [hLambdaLeft, hLambdaRight]
  unfold cubicAFECompletedExtension cubicAFEKernelG cubicAFEPoleCanceller
  dsimp only
  field_simp [hs, hu, hsplus, husub, huplus, hssub]
  ring

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
