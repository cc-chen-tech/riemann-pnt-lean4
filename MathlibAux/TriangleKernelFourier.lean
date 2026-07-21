import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fourier transform of the triangle kernel

The triangle kernel `t ↦ (H - |t|)₊` on `[-H, H]` has the classical
positive, quadratically decaying Fourier transform

```
∫_{t in -H..H} (H - |t|) * cos (c * t) dt = 2 * (1 - cos (c * H)) / c^2
```

for `c ≠ 0`.  In particular its transform is bounded by `4 / c^2`: any
autocorrelation whose lag dependence is oscillatory with frequency `c`
contributes at most `4 / c^2` times its amplitude to the lag integral.  This
is the `sinc^2` decay mechanism for the Selberg short-window second moment at
window `H = A / log T` with phase frequency `c ≍ log T`.
-/

open MeasureTheory Set

namespace MathlibAux

/-- The Fourier transform of the triangle kernel at nonzero frequency. -/
theorem integral_triangleKernel_mul_cos_eq
    {H c : ℝ} (hH : 0 ≤ H) (hc : c ≠ 0) :
    (∫ τ in (-H)..H, (H - |τ|) * Real.cos (c * τ)) =
      2 * (1 - Real.cos (c * H)) / c ^ 2 := by
  classical
  have hcpos : (0 : ℝ) < c ^ 2 := sq_pos_of_ne_zero hc
  -- The integrand is even; collapse to twice the right half.
  have heven : ∀ τ : ℝ, (H - |-τ|) * Real.cos (c * -τ) = (H - |τ|) * Real.cos (c * τ) := by
    intro τ
    rw [abs_neg, mul_neg, Real.cos_neg]
  have hsplit :
      (∫ τ in (-H)..H, (H - |τ|) * Real.cos (c * τ)) =
        2 * ∫ τ in (0 : ℝ)..H, (H - τ) * Real.cos (c * τ) := by
    have hint : ∀ a b : ℝ, IntervalIntegrable
        (fun τ => (H - |τ|) * Real.cos (c * τ)) MeasureTheory.volume a b :=
      fun a b => (((continuous_const.sub continuous_id.abs).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
        ).intervalIntegrable _ _
    have h1 := intervalIntegral.integral_interval_sub_left (hint (-H) H) (hint (-H) 0)
    have hneg :
        (∫ τ in (-H)..(0 : ℝ), (H - |τ|) * Real.cos (c * τ)) =
          ∫ τ in (0 : ℝ)..H, (H - τ) * Real.cos (c * τ) := by
      have h2 : (∫ τ in (-H)..(0 : ℝ), (H - |τ|) * Real.cos (c * τ)) =
          ∫ τ in (-H)..(0 : ℝ), (H - |-τ|) * Real.cos (c * -τ) := by
        apply intervalIntegral.integral_congr
        intro τ _hτ
        exact (heven τ).symm
      rw [h2]
      have h3 := intervalIntegral.integral_comp_neg
        (f := fun τ => (H - |τ|) * Real.cos (c * τ)) (a := -H) (b := (0 : ℝ))
      rw [neg_zero, neg_neg] at h3
      rw [h3]
      apply intervalIntegral.integral_congr
      intro τ hτ
      have hτ0 : (0 : ℝ) ≤ τ := by
        rw [uIcc_of_le hH] at hτ
        exact (mem_Icc.mp hτ).1
      show (H - |τ|) * Real.cos (c * τ) = (H - τ) * Real.cos (c * τ)
      rw [abs_of_nonneg hτ0]
    have hright :
        (∫ τ in (0 : ℝ)..H, (H - |τ|) * Real.cos (c * τ)) =
          ∫ τ in (0 : ℝ)..H, (H - τ) * Real.cos (c * τ) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      have hτ0 : (0 : ℝ) ≤ τ := by
        rw [uIcc_of_le hH] at hτ
        exact (mem_Icc.mp hτ).1
      show (H - |τ|) * Real.cos (c * τ) = (H - τ) * Real.cos (c * τ)
      rw [abs_of_nonneg hτ0]
    rw [hneg, hright] at h1
    linarith
  -- One integration by parts on the right half.
  have hhalf :
      (∫ τ in (0 : ℝ)..H, (H - τ) * Real.cos (c * τ)) =
        (1 - Real.cos (c * H)) / c ^ 2 := by
    have hv : ∀ x : ℝ, HasDerivAt (fun τ => c⁻¹ * Real.sin (c * τ))
        (Real.cos (c * x)) x := by
      intro x
      have h1 : HasDerivAt (fun τ : ℝ => Real.sin (c * τ))
          (c * Real.cos (c * x)) x := by
        have h := (Real.hasDerivAt_sin (c * x)).comp x
          ((hasDerivAt_id x).const_mul c)
        rwa [Function.comp_def, mul_one, mul_comm (Real.cos (c * x)) c] at h
      have h2 := h1.const_mul c⁻¹
      rwa [show c⁻¹ * (c * Real.cos (c * x)) = Real.cos (c * x) from by
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]] at h2
    have hsum := intervalIntegral.integral_deriv_mul_eq_sub
      (u := fun τ => H - τ) (u' := fun _ => -1)
      (v := fun τ => c⁻¹ * Real.sin (c * τ)) (v' := fun τ => Real.cos (c * τ))
      (fun x _hx => by simpa using (hasDerivAt_id' x).const_sub H)
      (fun x _hx => hv x)
      (intervalIntegrable_const (a := (0 : ℝ)) (b := H))
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id))
        |>.intervalIntegrable (0 : ℝ) H)
    have hsplit_int :
        (∫ τ in (0 : ℝ)..H, (-1) * (c⁻¹ * Real.sin (c * τ)) +
            (H - τ) * Real.cos (c * τ)) =
          (∫ τ in (0 : ℝ)..H, (-1) * (c⁻¹ * Real.sin (c * τ))) +
            ∫ τ in (0 : ℝ)..H, (H - τ) * Real.cos (c * τ) :=
      intervalIntegral.integral_add
        ((by fun_prop : Continuous fun τ => (-1 : ℝ) * (c⁻¹ * Real.sin (c * τ))
          ).intervalIntegrable (0 : ℝ) H)
        ((by fun_prop : Continuous fun τ => (H - τ) * Real.cos (c * τ)
          ).intervalIntegrable (0 : ℝ) H)
    have hbnd : (H - H) * (c⁻¹ * Real.sin (c * H)) - (H - 0) * (c⁻¹ * Real.sin (c * 0)) = 0 := by
      simp
    dsimp only at hsum
    rw [hsplit_int, hbnd] at hsum
    -- ∫ (H - τ) cos = ∫ c⁻¹ sin (c τ)
    have hsin : (∫ τ in (0 : ℝ)..H, (-1) * (c⁻¹ * Real.sin (c * τ))) =
        -(1 - Real.cos (c * H)) / c ^ 2 := by
      have hcomp : (∫ τ in (0 : ℝ)..H, Real.sin (c * τ)) =
          c⁻¹ * (Real.cos (c * 0) - Real.cos (c * H)) := by
        rw [intervalIntegral.integral_comp_mul_left (f := Real.sin)
            (a := (0 : ℝ)) (b := H) hc, integral_sin, smul_eq_mul]
      have hneg : (∫ τ in (0 : ℝ)..H, (-1) * (c⁻¹ * Real.sin (c * τ))) =
          -c⁻¹ * ∫ τ in (0 : ℝ)..H, Real.sin (c * τ) := by
        rw [show (fun τ => (-1 : ℝ) * (c⁻¹ * Real.sin (c * τ))) =
            (fun τ => (-c⁻¹) * Real.sin (c * τ)) from funext fun τ => by ring]
        rw [intervalIntegral.integral_const_mul]
      rw [hneg, hcomp, mul_zero, Real.cos_zero]
      field_simp [hc]
    rw [hsin] at hsum
    have hz : (0 : ℝ) < c ^ 2 := hcpos
    field_simp [hc] at hsum ⊢
    linarith
  rw [hsplit, hhalf]
  ring

/-- The triangle-kernel transform decays quadratically in the frequency. -/
theorem abs_triangleKernel_mul_cos_integral_le
    {H c : ℝ} (hH : 0 ≤ H) (hc : c ≠ 0) :
    |∫ τ in (-H)..H, (H - |τ|) * Real.cos (c * τ)| ≤ 4 / c ^ 2 := by
  rw [integral_triangleKernel_mul_cos_eq hH hc]
  have hcpos : (0 : ℝ) < c ^ 2 := sq_pos_of_ne_zero hc
  have hcos1 : (0 : ℝ) ≤ 1 - Real.cos (c * H) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hcos2 : 1 - Real.cos (c * H) ≤ 2 := by
    have := Real.neg_one_le_cos (c * H)
    linarith
  rw [abs_of_nonneg (by positivity)]
  have h : 2 * (1 - Real.cos (c * H)) / c ^ 2 ≤ 2 * 2 / c ^ 2 := by
    gcongr
  calc
    2 * (1 - Real.cos (c * H)) / c ^ 2 ≤ 2 * 2 / c ^ 2 := h
    _ = 4 / c ^ 2 := by ring

end MathlibAux
