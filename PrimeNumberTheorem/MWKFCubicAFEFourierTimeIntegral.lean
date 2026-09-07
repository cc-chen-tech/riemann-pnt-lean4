import PrimeNumberTheorem.MWKFCubicAFEJointKernel
import Mathlib.MeasureTheory.Integral.Prod

open Complex MeasureTheory
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Physical time integration at each Fourier frequency

Joint compact support and continuity discharge Fubini for the literal kernel.
This does not interchange an infinite frequency sum with the time integral.
-/

theorem integrable_cubicAFEProgressionCutoffFourier_joint
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) (ξ : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      Complex.exp (((-2 * Real.pi * p.2 * ξ : ℝ) : ℂ) * I) *
        cubicAFEProgressionCutoffSummand W T X V χ p.1 p.2)
      (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ ↦
      Complex.exp (((-2 * Real.pi * p.2 * ξ : ℝ) : ℂ) * I)) := by fun_prop
  exact (hc.mul (continuous_cubicAFEProgressionCutoffSummand_joint W T X V hd he χ hX)).integrable_of_hasCompactSupport
      ((hasCompactSupport_cubicAFEProgressionCutoffSummand_joint W hT X V χ).mul_left)

/-- Fourier transformation commutes with the actual physical time integral
at every real frequency, including zero. No abstract integrability input. -/
theorem integral_fourier_cubicAFEProgressionCutoffSummand
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) (ξ : ℝ) :
    (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t) ξ) =
      𝓕 (fun x : ℝ ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x) ξ := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [integral_integral_swap
    (integrable_cubicAFEProgressionCutoffFourier_joint W hT hX V hd he χ ξ)]
  apply integral_congr_ae
  filter_upwards [] with x
  exact integral_const_mul _ _

end PrimeNumberTheorem.MWKFCubic
