import PrimeNumberTheorem.CarlsonGaussianHilbertSection
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gaussian domination for the Carlson Hilbert section

This file isolates the real-variable step that promotes a pointwise Gaussian
strip section to an element of `L²(ℝ)`.  The hypothesis is an explicit
sub-Gaussian bound; no strip analyticity or mean-square estimate is assumed.
-/

open Complex MeasureTheory
open scoped ENNReal MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Every fixed natural power of `1 + |t|` remains integrable against a
nondegenerate Gaussian. -/
theorem integrable_one_add_abs_pow_mul_exp_neg_mul_sq
    {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun t : ℝ =>
      (1 + |t|) ^ n * Real.exp (-b * t ^ 2)) := by
  have hzero : Integrable (fun t : ℝ => Real.exp (-b * t ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hpowRaw :
      Integrable (fun t : ℝ =>
        t ^ (n : ℝ) * Real.exp (-b * t ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  have hpow :
      Integrable (fun t : ℝ =>
        |t| ^ n * Real.exp (-b * t ^ 2)) := by
    convert hpowRaw.norm using 1
    funext t
    simp [Real.rpow_natCast, abs_of_nonneg (Real.exp_pos _).le]
  have hmajor :
      Integrable (fun t : ℝ =>
        (2 : ℝ) ^ (n - 1) *
          (Real.exp (-b * t ^ 2) +
            |t| ^ n * Real.exp (-b * t ^ 2))) :=
    (hzero.add hpow).const_mul ((2 : ℝ) ^ (n - 1))
  apply Integrable.mono_nonneg hmajor
  · fun_prop
  · exact Filter.Eventually.of_forall fun t =>
      mul_nonneg (pow_nonneg (by positivity) n) (Real.exp_pos _).le
  · exact Filter.Eventually.of_forall fun t => by
      calc
        (1 + |t|) ^ n * Real.exp (-b * t ^ 2)
            ≤ (2 : ℝ) ^ (n - 1) * (1 ^ n + |t| ^ n) *
                Real.exp (-b * t ^ 2) := by
              gcongr
              exact add_pow_le (by positivity) (abs_nonneg t) n
        _ = (2 : ℝ) ^ (n - 1) *
              (Real.exp (-b * t ^ 2) +
                |t| ^ n * Real.exp (-b * t ^ 2)) := by
              simp only [one_pow]
              ring

/-- A continuous vertical section with square norm bounded by an exponential
of rate strictly below the Gaussian rate belongs to `L²(ℝ)`.

This is the exact `MemLp` interface needed before constructing the
`L²(ℝ)`-valued map in the Carlson three-lines argument. -/
theorem memLp_carlsonGaussianHilbertSection_of_exp_sq_bound
    {Delta w x C c : ℝ} (hDelta : 0 < Delta)
    (hc : c < 1 / Delta ^ 2) (H : ℂ → ℂ)
    (hHcont : Continuous fun t : ℝ => H ((x : ℂ) + I * (t : ℂ)))
    (hHbound : ∀ t : ℝ,
      ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        C * Real.exp (c * (t - w) ^ 2)) :
    MemLp (carlsonGaussianHilbertSection Delta w H (x : ℂ)) 2 volume := by
  have hDelta0 : Delta ≠ 0 := ne_of_gt hDelta
  let d : ℝ := 1 / Delta ^ 2 - c
  have hd : 0 < d := sub_pos.mpr hc
  have hsection :
      Continuous (carlsonGaussianHilbertSection Delta w H (x : ℂ)) := by
    unfold carlsonGaussianHilbertSection
    apply Continuous.mul
    · fun_prop
    · exact hHcont
  rw [memLp_two_iff_integrable_sq_norm hsection.aestronglyMeasurable]
  have hgaussian :
      Integrable (fun t : ℝ => Real.exp (-d * (t - w) ^ 2)) := by
    exact Integrable.comp_sub_right (integrable_exp_neg_mul_sq hd) w
  have hmajor :
      Integrable (fun t : ℝ =>
        (Real.exp (x ^ 2 / Delta ^ 2) * C) *
          Real.exp (-d * (t - w) ^ 2)) :=
    hgaussian.const_mul (Real.exp (x ^ 2 / Delta ^ 2) * C)
  apply Integrable.mono_nonneg hmajor
  · exact hsection.norm.pow 2 |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_sq_carlsonGaussianHilbertSection_real hDelta0 H x t]
      have hweight : 0 ≤ carlsonGaussianWeight Delta w t := by
        exact Real.exp_pos _ |>.le
      calc
        Real.exp (x ^ 2 / Delta ^ 2) *
              carlsonGaussianWeight Delta w t *
              ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2
            ≤ Real.exp (x ^ 2 / Delta ^ 2) *
                carlsonGaussianWeight Delta w t *
                (C * Real.exp (c * (t - w) ^ 2)) := by
              gcongr
              exact hHbound t
        _ = (Real.exp (x ^ 2 / Delta ^ 2) * C) *
              Real.exp (-d * (t - w) ^ 2) := by
              have hexp :
                  carlsonGaussianWeight Delta w t *
                      Real.exp (c * (t - w) ^ 2) =
                    Real.exp (-d * (t - w) ^ 2) := by
                rw [carlsonGaussianWeight, ← Real.exp_add]
                congr 1
                dsimp [d]
                field_simp [pow_ne_zero 2 hDelta0]
                ring
              rw [← hexp]
              ring

/-- Polynomial square growth on a vertical line is sufficient for the
Gaussian strip section to define an element of `L²(ℝ)`. -/
theorem memLp_carlsonGaussianHilbertSection_of_polynomial_sq_bound
    {Delta w x C : ℝ} (hDelta : 0 < Delta) (n : ℕ)
    (H : ℂ → ℂ)
    (hHcont : Continuous fun t : ℝ => H ((x : ℂ) + I * (t : ℂ)))
    (hHbound : ∀ t : ℝ,
      ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
        C * (1 + |t - w|) ^ n) :
    MemLp (carlsonGaussianHilbertSection Delta w H (x : ℂ)) 2 volume := by
  have hDelta0 : Delta ≠ 0 := ne_of_gt hDelta
  have hb : 0 < 1 / Delta ^ 2 := by positivity
  have hsection :
      Continuous (carlsonGaussianHilbertSection Delta w H (x : ℂ)) := by
    unfold carlsonGaussianHilbertSection
    apply Continuous.mul
    · fun_prop
    · exact hHcont
  rw [memLp_two_iff_integrable_sq_norm hsection.aestronglyMeasurable]
  have hpoly :
      Integrable (fun t : ℝ =>
        (1 + |t|) ^ n * Real.exp (-(1 / Delta ^ 2) * t ^ 2)) :=
    integrable_one_add_abs_pow_mul_exp_neg_mul_sq hb n
  have hpolyCentered :
      Integrable (fun t : ℝ =>
        (1 + |t - w|) ^ n *
          Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2)) :=
    Integrable.comp_sub_right hpoly w
  have hmajor :
      Integrable (fun t : ℝ =>
        (Real.exp (x ^ 2 / Delta ^ 2) * C) *
          ((1 + |t - w|) ^ n *
            Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2))) :=
    hpolyCentered.const_mul (Real.exp (x ^ 2 / Delta ^ 2) * C)
  apply Integrable.mono_nonneg hmajor
  · exact hsection.norm.pow 2 |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_sq_carlsonGaussianHilbertSection_real hDelta0 H x t]
      have hweight : 0 ≤ carlsonGaussianWeight Delta w t :=
        Real.exp_pos _ |>.le
      have hweightEq :
          carlsonGaussianWeight Delta w t =
            Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2) := by
        apply congrArg Real.exp
        field_simp [pow_ne_zero 2 hDelta0]
      calc
        Real.exp (x ^ 2 / Delta ^ 2) *
              carlsonGaussianWeight Delta w t *
              ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2
            ≤ Real.exp (x ^ 2 / Delta ^ 2) *
                carlsonGaussianWeight Delta w t *
                (C * (1 + |t - w|) ^ n) := by
              gcongr
              exact hHbound t
        _ = (Real.exp (x ^ 2 / Delta ^ 2) * C) *
              ((1 + |t - w|) ^ n *
                Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2)) := by
              rw [hweightEq]
              ring

/-- The polynomial-growth `L²` criterion at an arbitrary complex strip
parameter.  The Gaussian center is shifted by `z.im`, exactly as dictated by
the pointwise norm formula. -/
theorem memLp_carlsonGaussianHilbertSection_of_complex_polynomial_sq_bound
    {Delta w C : ℝ} {z : ℂ} (hDelta : 0 < Delta) (n : ℕ)
    (H : ℂ → ℂ)
    (hHcont : Continuous fun t : ℝ => H (z + I * (t : ℂ)))
    (hHbound : ∀ t : ℝ,
      ‖H (z + I * (t : ℂ))‖ ^ 2 ≤
        C * (1 + |z.im + t - w|) ^ n) :
    MemLp (carlsonGaussianHilbertSection Delta w H z) 2 volume := by
  have hDelta0 : Delta ≠ 0 := ne_of_gt hDelta
  have hb : 0 < 1 / Delta ^ 2 := by positivity
  have hsection :
      Continuous (carlsonGaussianHilbertSection Delta w H z) := by
    unfold carlsonGaussianHilbertSection
    apply Continuous.mul
    · fun_prop
    · exact hHcont
  rw [memLp_two_iff_integrable_sq_norm hsection.aestronglyMeasurable]
  have hpoly :
      Integrable (fun t : ℝ =>
        (1 + |t|) ^ n * Real.exp (-(1 / Delta ^ 2) * t ^ 2)) :=
    integrable_one_add_abs_pow_mul_exp_neg_mul_sq hb n
  have hpolyShifted :
      Integrable (fun t : ℝ =>
        (1 + |z.im + t - w|) ^ n *
          Real.exp (-(1 / Delta ^ 2) * (z.im + t - w) ^ 2)) := by
    convert Integrable.comp_sub_right hpoly (w - z.im) using 1
    funext t
    congr 2 <;> ring
  have hmajor :
      Integrable (fun t : ℝ =>
        (Real.exp (z.re ^ 2 / Delta ^ 2) * C) *
          ((1 + |z.im + t - w|) ^ n *
            Real.exp (-(1 / Delta ^ 2) * (z.im + t - w) ^ 2))) :=
    hpolyShifted.const_mul (Real.exp (z.re ^ 2 / Delta ^ 2) * C)
  apply Integrable.mono_nonneg hmajor
  · exact hsection.norm.pow 2 |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_sq_carlsonGaussianHilbertSection hDelta0 H z t]
      have hexp :
          Real.exp
              ((z.re ^ 2 - (z.im + t - w) ^ 2) / Delta ^ 2) =
            Real.exp (z.re ^ 2 / Delta ^ 2) *
              Real.exp (-(1 / Delta ^ 2) * (z.im + t - w) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        field_simp [pow_ne_zero 2 hDelta0]
        ring
      rw [hexp]
      calc
        Real.exp (z.re ^ 2 / Delta ^ 2) *
              Real.exp (-(1 / Delta ^ 2) * (z.im + t - w) ^ 2) *
              ‖H (z + I * (t : ℂ))‖ ^ 2
            ≤ Real.exp (z.re ^ 2 / Delta ^ 2) *
                Real.exp (-(1 / Delta ^ 2) * (z.im + t - w) ^ 2) *
                (C * (1 + |z.im + t - w|) ^ n) := by
              gcongr
              exact hHbound t
        _ = (Real.exp (z.re ^ 2 / Delta ^ 2) * C) *
              ((1 + |z.im + t - w|) ^ n *
                Real.exp (-(1 / Delta ^ 2) * (z.im + t - w) ^ 2)) := by
              ring

end CarlsonZeroDensity
end PrimeNumberTheorem
