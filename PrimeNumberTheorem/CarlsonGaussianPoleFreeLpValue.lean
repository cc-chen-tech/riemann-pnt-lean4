import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorGrowth

/-!
# The concrete `L²(ℝ)` value in the Carlson Gaussian argument

This file packages the proved `MemLp` section as an actual `Lp` element and
records its a.e. representative and exact norm-square integral.
-/

open Complex Set MeasureTheory
open scoped ENNReal MeasureTheory ComplexConjugate

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Exact norm-square formula for the `Lp` element attached to a complex
`L²` function. -/
theorem norm_sq_toLp_eq_integral_norm_sq
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    {f : alpha → ℂ} (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂mu := by
  let F : Lp ℂ 2 mu := hf.toLp f
  have hinner :
      inner ℂ F F = Complex.ofReal (∫ x, ‖f x‖ ^ 2 ∂mu) := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ x, inner ℂ (F x) (F x) ∂mu) =
          ∫ x, Complex.ofReal (‖f x‖ ^ 2) ∂mu := by
            apply integral_congr_ae
            filter_upwards [hf.coeFn_toLp] with x hx
            dsimp [F] at hx ⊢
            rw [hx]
            simpa using Complex.mul_conj' (f x)
      _ = Complex.ofReal (∫ x, ‖f x‖ ^ 2 ∂mu) := integral_ofReal
  calc
    ‖hf.toLp f‖ ^ 2 = (inner ℂ F F).re := by
      dsimp [F]
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = ∫ x, ‖f x‖ ^ 2 ∂mu := by rw [hinner]; simp

/-- The concrete pole-free Gaussian section as an element of `L²(ℝ)` on
the finite strip `1/2 ≤ Re(z) ≤ 4`. -/
noncomputable def carlsonGaussianPoleFreeLpValue
    (Delta w : ℝ) (Y0 Y1 : ℕ)
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (z : ℂ) (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  let hmem :=
    memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
      (Delta := Delta) (w := w) (z := z) hDelta hY0 hY01 hzre
  hmem.toLp
    (carlsonGaussianHilbertSection Delta w
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z)

/-- The chosen `Lp` representative agrees a.e. with the original Gaussian
section. -/
theorem coeFn_carlsonGaussianPoleFreeLpValue_ae_eq
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    (carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
      hDelta hY0 hY01 z hzre : ℝ → ℂ) =ᵐ[volume]
      carlsonGaussianHilbertSection Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z := by
  simpa [carlsonGaussianPoleFreeLpValue] using
    (memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
      (Delta := Delta) (w := w) (z := z) hDelta hY0 hY01 hzre).coeFn_toLp

/-- Exact integral expression for the norm square of the concrete Carlson
Gaussian `Lp` value. -/
theorem norm_sq_carlsonGaussianPoleFreeLpValue
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (1 / 2 : ℝ) 4) :
    ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 z hzre‖ ^ 2 =
      ∫ t : ℝ,
        ‖carlsonGaussianHilbertSection Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t‖ ^ 2 := by
  simpa [carlsonGaussianPoleFreeLpValue] using
    norm_sq_toLp_eq_integral_norm_sq
      (memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
        (Delta := Delta) (w := w) (z := z) hDelta hY0 hY01 hzre)

end CarlsonZeroDensity
end PrimeNumberTheorem
