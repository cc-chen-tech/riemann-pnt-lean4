import MathlibAux.SlidingLagBudget
import MathlibAux.TriangleKernelFourier

/-!
# Cosine main terms in lag-integral budgets

This module combines the triangular lag-region identity with the Fourier
decay of the triangle kernel.  It is the reusable analytic step needed when
an autocorrelation is a cosine main term plus a uniformly controlled error.
-/

open MeasureTheory Set

namespace MathlibAux

/-- If a lag-section integrand is a cosine main term plus a uniformly bounded
error, then the full lag integral is bounded by the quadratic Fourier decay
of the cosine and one triangle-area error term. -/
theorem abs_lagIntegral_le_cosine_main_add_uniform_error
    {E : ℝ → ℝ → ℝ} (hE : Continuous (Function.uncurry E))
    {H K c epsilon : ℝ} (hH : 0 ≤ H) (hc : c ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ v tau : ℝ, |E v tau| ≤ epsilon) :
    |∫ tau in (-H)..H,
        ∫ v in max 0 (-tau)..min H (H - tau),
          (K * Real.cos (c * tau) + E v tau)| ≤
      |K| * (4 / c ^ 2) + epsilon * H ^ 2 := by
  let M : ℝ → ℝ := fun tau => K * Real.cos (c * tau)
  let errorIntegral : ℝ :=
    ∫ tau in (-H)..H,
      ∫ v in max 0 (-tau)..min H (H - tau), E v tau
  have hM : Continuous M := by
    dsimp only [M]
    fun_prop
  have hsplit := intervalIntegral_lagIntegral_add
    (M := M) (E := E) hM hE hH
  have herr : |errorIntegral| ≤ epsilon * H ^ 2 := by
    simpa only [errorIntegral] using
      abs_lagIntegral_le_of_forall_norm_le hE hH hepsilon hbound
  have hfactor :
      (∫ tau in (-H)..H, (H - |tau|) * M tau) =
        K * ∫ tau in (-H)..H,
          (H - |tau|) * Real.cos (c * tau) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro tau _htau
    dsimp only [M]
    ring
  have hmain :
      |∫ tau in (-H)..H, (H - |tau|) * M tau| ≤
        |K| * (4 / c ^ 2) := by
    rw [hfactor, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_triangleKernel_mul_cos_integral_le hH hc) (abs_nonneg K)
  calc
    |∫ tau in (-H)..H,
        ∫ v in max 0 (-tau)..min H (H - tau),
          (K * Real.cos (c * tau) + E v tau)| =
        |(∫ tau in (-H)..H, (H - |tau|) * M tau) +
          errorIntegral| := by
      rw [hsplit]
    _ ≤ |∫ tau in (-H)..H, (H - |tau|) * M tau| +
          |errorIntegral| := abs_add_le _ _
    _ ≤ |K| * (4 / c ^ 2) + epsilon * H ^ 2 :=
      add_le_add hmain herr

/-- Nonnegative-amplitude form of
`abs_lagIntegral_le_cosine_main_add_uniform_error`. -/
theorem abs_lagIntegral_le_cosine_main_add_uniform_error_of_nonneg
    {E : ℝ → ℝ → ℝ} (hE : Continuous (Function.uncurry E))
    {H K c epsilon : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (hc : c ≠ 0)
    (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ v tau : ℝ, |E v tau| ≤ epsilon) :
    |∫ tau in (-H)..H,
        ∫ v in max 0 (-tau)..min H (H - tau),
          (K * Real.cos (c * tau) + E v tau)| ≤
      K * (4 / c ^ 2) + epsilon * H ^ 2 := by
  simpa only [abs_of_nonneg hK] using
    abs_lagIntegral_le_cosine_main_add_uniform_error
      (K := K) hE hH hc hepsilon hbound

end MathlibAux
