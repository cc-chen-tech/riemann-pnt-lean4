import MathlibAux.SlidingLagBudget
import MathlibAux.TriangleKernelFourier
import MathlibAux.FejerTriangleKernel

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

/-- Square-window form of the cosine lag budget.  A jointly continuous
kernel uniformly close to `K * cos (c * (w-v))` has double integral bounded
by the triangle-kernel Fourier saving plus the square-area error. -/
theorem abs_squareIntegral_le_cosine_difference_main_add_uniform_error
    {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    {H K c epsilon : ℝ} (hH : 0 ≤ H) (hc : c ≠ 0)
    (hbound : ∀ v w : ℝ,
      |F v w - K * Real.cos (c * (w - v))| ≤ epsilon) :
    |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, F v w| ≤
      |K| * (4 / c ^ 2) + epsilon * H ^ 2 := by
  let main : ℝ → ℝ → ℝ := fun v w =>
    K * Real.cos (c * (w - v))
  let E : ℝ → ℝ → ℝ := fun v w => F v w - main v w
  have hmain : Continuous (Function.uncurry main) := by
    dsimp only [main, Function.uncurry]
    fun_prop
  have hE : Continuous (Function.uncurry E) := by
    exact hF.sub hmain
  have hinnerMain (v : ℝ) : IntervalIntegrable (main v) volume 0 H :=
    (hmain.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hinnerE (v : ℝ) : IntervalIntegrable (E v) volume 0 H :=
    (hE.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have houterMain : Continuous (fun v => ∫ w in (0 : ℝ)..H, main v w) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hmain 0 H
  have houterE : Continuous (fun v => ∫ w in (0 : ℝ)..H, E v w) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hE 0 H
  have hdecomp :
      (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, F v w) =
        (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, main v w) +
          ∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, E v w := by
    calc
      (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, F v w) =
          ∫ v in (0 : ℝ)..H,
            ((∫ w in (0 : ℝ)..H, main v w) +
              ∫ w in (0 : ℝ)..H, E v w) := by
        apply intervalIntegral.integral_congr
        intro v _hv
        change (∫ w in (0 : ℝ)..H, F v w) =
          (∫ w in (0 : ℝ)..H, main v w) +
            ∫ w in (0 : ℝ)..H, E v w
        rw [← intervalIntegral.integral_add (hinnerMain v) (hinnerE v)]
        apply intervalIntegral.integral_congr
        intro w _hw
        dsimp only [E]
        ring
      _ = (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, main v w) +
          ∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, E v w :=
        intervalIntegral.integral_add
          (houterMain.intervalIntegrable _ _)
          (houterE.intervalIntegrable _ _)
  have hmainBound :
      |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, main v w| ≤
        |K| * (4 / c ^ 2) := by
    have htriangle := intervalIntegral_pair_sub_eq_triangle_kernel
      (f := fun tau => K * Real.cos (c * tau))
      (by fun_prop) hH
    have hfactor :
        (∫ tau in (-H)..H,
          (H - |tau|) * (K * Real.cos (c * tau))) =
          K * ∫ tau in (-H)..H,
            (H - |tau|) * Real.cos (c * tau) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro tau _htau
      ring
    rw [show (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, main v w) =
        ∫ tau in (-H)..H,
          (H - |tau|) * (K * Real.cos (c * tau)) by
      simpa only [main] using htriangle]
    rw [hfactor, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_triangleKernel_mul_cos_integral_le hH hc) (abs_nonneg K)
  have herrorBound :
      |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, E v w| ≤
        epsilon * H ^ 2 := by
    have hinner : ∀ v ∈ Icc (0 : ℝ) H,
        |∫ w in (0 : ℝ)..H, E v w| ≤ epsilon * H := by
      intro v _hv
      calc
        |∫ w in (0 : ℝ)..H, E v w| ≤
            ∫ w in (0 : ℝ)..H, |E v w| :=
          intervalIntegral.abs_integral_le_integral_abs hH
        _ ≤ ∫ _w in (0 : ℝ)..H, epsilon :=
          intervalIntegral.integral_mono_on hH
            ((hE.comp (continuous_const.prodMk continuous_id)).abs
              |>.intervalIntegrable _ _)
            intervalIntegrable_const
            (fun w _hw => by simpa only [E] using hbound v w)
        _ = epsilon * H := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
    calc
      |∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, E v w| ≤
          ∫ v in (0 : ℝ)..H, |∫ w in (0 : ℝ)..H, E v w| :=
        intervalIntegral.abs_integral_le_integral_abs hH
      _ ≤ ∫ _v in (0 : ℝ)..H, epsilon * H :=
        intervalIntegral.integral_mono_on hH
          (houterE.abs.intervalIntegrable _ _)
          intervalIntegrable_const hinner
      _ = epsilon * H ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hmainBound herrorBound)

end MathlibAux
