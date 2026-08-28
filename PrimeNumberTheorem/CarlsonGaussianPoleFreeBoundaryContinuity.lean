import PrimeNumberTheorem.CarlsonGaussianPoleFreeHadamard
import MathlibAux.HadamardBoundaryLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Boundary continuity for the Carlson Gaussian `L²` map

The totalized map need not be continuous from outside its artificial strip.
For Hadamard, only the one-sided behavior from the controlled closed strip is
needed.  A single integrable polynomial-Gaussian majorant gives continuity of
the norm square on the whole real interval `1/2 ≤ x ≤ 4`.
-/

open Complex Set MeasureTheory Filter Function
open scoped ENNReal MeasureTheory Topology

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The squared Gaussian sections on the entire real Carlson strip admit one
integrable majorant, uniform in the horizontal parameter. -/
theorem exists_integrable_carlsonGaussianPoleFreeSection_sq_bound_on_half_four
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ∃ bound : ℝ → ℝ, Integrable bound ∧
      ∀ x ∈ Icc (1 / 2 : ℝ) 4, ∀ t : ℝ,
        ‖carlsonGaussianHilbertSection Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (x : ℂ) t‖ ^ 2 ≤
            bound t := by
  rcases
      exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
        hY0 hY01 with ⟨C, hC, hgrowth⟩
  let D : ℝ := |w| + 3
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [abs_nonneg w]
  let bound : ℝ → ℝ := fun t =>
    (Real.exp (16 / Delta ^ 2) * (C * D ^ 10)) *
      ((1 + |t - w|) ^ 10 *
        Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2))
  have hb : 0 < (1 / Delta ^ 2 : ℝ) := by positivity
  have hpoly : Integrable (fun t : ℝ =>
      (1 + |t|) ^ 10 * Real.exp (-(1 / Delta ^ 2) * t ^ 2)) :=
    integrable_one_add_abs_pow_mul_exp_neg_mul_sq hb 10
  have hpolyCentered : Integrable (fun t : ℝ =>
      (1 + |t - w|) ^ 10 *
        Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2)) :=
    hpoly.comp_sub_right w
  have hboundInt : Integrable bound :=
    hpolyCentered.const_mul
      (Real.exp (16 / Delta ^ 2) * (C * D ^ 10))
  refine ⟨bound, hboundInt, ?_⟩
  intro x hx t
  have hxSq : x ^ 2 ≤ (16 : ℝ) := by nlinarith [hx.1, hx.2]
  have hExp :
      Real.exp (x ^ 2 / Delta ^ 2) ≤ Real.exp (16 / Delta ^ 2) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right hxSq (sq_nonneg Delta)
  have hraw := hgrowth
    (s := (x : ℂ) + I * (t : ℂ)) (by simpa using hx)
  have htLinear : |t| + 3 ≤ D * (1 + |t - w|) := by
    have habs : |t| ≤ |t - w| + |w| := by
      calc
        |t| = |(t - w) + w| := by ring_nf
        _ ≤ |t - w| + |w| := abs_add_le _ _
    have hmul : |t - w| ≤ D * |t - w| :=
      le_mul_of_one_le_left (abs_nonneg (t - w)) hD
    dsimp [D]
    nlinarith
  have htPow : (|t| + 3) ^ 10 ≤
      (D * (1 + |t - w|)) ^ 10 :=
    pow_le_pow_left₀ (by positivity) htLinear 10
  have hH :
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          ((x : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        (C * D ^ 10) * (1 + |t - w|) ^ 10 := by
    calc
      ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
          ((x : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
          C * (|t| + 3) ^ 10 := by simpa using hraw
      _ ≤ C * (D * (1 + |t - w|)) ^ 10 :=
        mul_le_mul_of_nonneg_left htPow hC
      _ = (C * D ^ 10) * (1 + |t - w|) ^ 10 := by ring
  have hweight :
      carlsonGaussianWeight Delta w t =
        Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2) := by
    unfold carlsonGaussianWeight
    congr 1
    field_simp [pow_ne_zero 2 hDelta.ne']
  rw [norm_sq_carlsonGaussianHilbertSection_real hDelta.ne'
    (poleFreeTwoScaleMollifiedZetaError Y0 Y1) x t]
  dsimp [bound]
  rw [hweight]
  calc
    Real.exp (x ^ 2 / Delta ^ 2) *
          Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2) *
          ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
            ((x : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        Real.exp (16 / Delta ^ 2) *
          Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2) *
          ((C * D ^ 10) * (1 + |t - w|) ^ 10) := by
      gcongr
    _ = (Real.exp (16 / Delta ^ 2) * (C * D ^ 10)) *
          ((1 + |t - w|) ^ 10 *
            Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2)) := by ring

/-- The squared `L²` norm is continuous all the way to both real boundary
points when approached inside the controlled strip. -/
theorem continuousOn_norm_sq_carlsonGaussianPoleFreeLpValueTotal_real
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ContinuousOn
      (fun x : ℝ =>
        ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
          hDelta hY0 hY01 (x : ℂ)‖ ^ 2)
      (Icc (1 / 2 : ℝ) 4) := by
  rcases
      exists_integrable_carlsonGaussianPoleFreeSection_sq_bound_on_half_four
        (w := w) hDelta hY0 hY01 with ⟨bound, hboundInt, hbound⟩
  let H : ℂ → ℂ := poleFreeTwoScaleMollifiedZetaError Y0 Y1
  let G : ℝ → ℝ → ℝ := fun x t =>
    ‖carlsonGaussianHilbertSection Delta w H (x : ℂ) t‖ ^ 2
  have hnormIntegral : ∀ x ∈ Icc (1 / 2 : ℝ) 4,
      ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 = ∫ t : ℝ, G x t := by
    intro x hx
    rw [carlsonGaussianPoleFreeLpValueTotal_eq hDelta hY0 hY01
      (by simpa using hx)]
    simpa [G, H] using
      norm_sq_carlsonGaussianPoleFreeLpValue hDelta hY0 hY01
        (by simpa using hx : ((x : ℝ) : ℂ).re ∈ Icc (1 / 2 : ℝ) 4)
  intro x hx
  have hmeas : ∀ᶠ y in 𝓝[Icc (1 / 2 : ℝ) 4] x,
      AEStronglyMeasurable (G y) volume := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact
      (memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
        (Delta := Delta) (w := w) (z := (y : ℂ))
        hDelta hY0 hY01 (by simpa using hy)).aestronglyMeasurable.norm.pow 2
  have hdominated : ∀ᶠ y in 𝓝[Icc (1 / 2 : ℝ) 4] x,
      ∀ᵐ t ∂volume, ‖G y t‖ ≤ bound t := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa [G, H] using hbound y hy t
  have hpointwise : ∀ᵐ t ∂volume,
      Tendsto (fun y : ℝ => G y t)
        (𝓝[Icc (1 / 2 : ℝ) 4] x) (𝓝 (G x t)) := by
    filter_upwards with t
    let point : ℝ → ℂ := fun y => (y : ℂ) + I * (t : ℂ)
    have hpoint : ContinuousAt point x := by
      dsimp [point]
      fun_prop
    have hre : 0 < (point x).re := by
      dsimp [point]
      simp only [ofReal_re, mul_re, I_re, ofReal_im, I_im,
        zero_mul, one_mul, sub_self, add_zero]
      linarith [hx.1]
    have hHcont : ContinuousAt (fun y : ℝ => H (point y)) x := by
      have hanalytic : AnalyticAt ℂ H (point x) := by
        dsimp [H]
        exact analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
          (theta := 0) le_rfl Y0 Y1 (point x) hre
      exact hanalytic.continuousAt.comp hpoint
    have hsection : ContinuousAt
        (fun y : ℝ =>
          carlsonGaussianHilbertSection Delta w H (y : ℂ) t) x := by
      unfold carlsonGaussianHilbertSection
      change ContinuousAt (fun y : ℝ =>
        Complex.exp
            ((point y - I * (w : ℂ)) ^ 2 /
              (2 * (Delta : ℂ) ^ 2)) *
          H (point y)) x
      have hq : ContinuousAt (fun y : ℝ =>
          (point y - I * (w : ℂ)) ^ 2 /
            (2 * (Delta : ℂ) ^ 2)) x := by
        exact ((hpoint.sub continuousAt_const).pow 2).div_const _
      exact (Complex.continuous_exp.continuousAt.comp hq).mul hHcont
    exact (hsection.norm.pow 2).tendsto.mono_left nhdsWithin_le_nhds
  have hraw := tendsto_integral_filter_of_dominated_convergence
    (F := G) (f := G x) bound hmeas hdominated hboundInt hpointwise
  rw [← hnormIntegral x hx] at hraw
  exact hraw.congr' <| by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hnormIntegral y hy).symm

/-- Exact squared-norm Hadamard interpolation on the closed Carlson strip.
The artificial totalization is never used from outside the strip: the result
is the limit of the already proved inner-strip inequalities. -/
theorem norm_sq_carlsonGaussianPoleFreeLpValueTotal_le_interp_on_closed_strip
    {Delta w x : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hx : x ∈ Icc (1 / 2 : ℝ) 4) :
    ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 ≤
      (‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
          hDelta hY0 hY01 ((1 / 2 : ℝ) : ℂ)‖ ^ 2) ^
            (1 - (x - 1 / 2) / (4 - 1 / 2)) *
        (‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
          hDelta hY0 hY01 (4 : ℂ)‖ ^ 2) ^
            ((x - 1 / 2) / (4 - 1 / 2)) := by
  let f : ℝ → ℝ := fun y =>
    ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
      hDelta hY0 hY01 (y : ℂ)‖ ^ 2
  apply MathlibAux.le_endpoint_interp_of_continuousOn_of_inner_interp
    (f := f) (l := (1 / 2 : ℝ)) (u := 4) (x := x)
    (by norm_num) hx
    (continuousOn_norm_sq_carlsonGaussianPoleFreeLpValueTotal_real
      hDelta hY0 hY01)
  intro l u hl hu hlu hxu
  exact
    norm_sq_carlsonGaussianPoleFreeLpValueTotal_le_interp_on_inner_strip
      hDelta hY0 hY01 hl hu hlu hxu
      (sq_nonneg _) (sq_nonneg _) le_rfl le_rfl

/-- Endpoint second-moment estimates can be inserted directly into the closed
strip interpolation inequality. -/
theorem norm_sq_carlsonGaussianPoleFreeLpValueTotal_le_of_endpoint_bounds
    {Delta w x A B : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hx : x ∈ Icc (1 / 2 : ℝ) 4)
    (hA : ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 ((1 / 2 : ℝ) : ℂ)‖ ^ 2 ≤ A)
    (hB : ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (4 : ℂ)‖ ^ 2 ≤ B) :
    ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 ≤
      A ^ (1 - (x - 1 / 2) / (4 - 1 / 2)) *
        B ^ ((x - 1 / 2) / (4 - 1 / 2)) := by
  let p : ℝ := 1 - (x - 1 / 2) / (4 - 1 / 2)
  let q : ℝ := (x - 1 / 2) / (4 - 1 / 2)
  have hA0 : 0 ≤ A := (sq_nonneg _).trans hA
  have hp : 0 ≤ p := by
    dsimp [p]
    norm_num
    linarith [hx.2]
  have hq : 0 ≤ q := by
    dsimp [q]
    norm_num
    linarith [hx.1]
  have hleft := Real.rpow_le_rpow (sq_nonneg _) hA hp
  have hright := Real.rpow_le_rpow (sq_nonneg _) hB hq
  calc
    ‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
        hDelta hY0 hY01 (x : ℂ)‖ ^ 2 ≤
      (‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
          hDelta hY0 hY01 ((1 / 2 : ℝ) : ℂ)‖ ^ 2) ^ p *
        (‖carlsonGaussianPoleFreeLpValueTotal Delta w Y0 Y1
          hDelta hY0 hY01 (4 : ℂ)‖ ^ 2) ^ q := by
      simpa [p, q] using
        norm_sq_carlsonGaussianPoleFreeLpValueTotal_le_interp_on_closed_strip
          hDelta hY0 hY01 hx
    _ ≤ A ^ p * B ^ q :=
      mul_le_mul hleft hright (Real.rpow_nonneg (sq_nonneg _) q)
        (Real.rpow_nonneg hA0 p)
    _ = A ^ (1 - (x - 1 / 2) / (4 - 1 / 2)) *
        B ^ ((x - 1 / 2) / (4 - 1 / 2)) := by rfl

end CarlsonZeroDensity
end PrimeNumberTheorem
