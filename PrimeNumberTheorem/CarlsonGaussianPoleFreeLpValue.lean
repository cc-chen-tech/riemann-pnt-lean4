import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorGrowth
import PrimeNumberTheorem.CarlsonTwoScaleFarRight

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

/-- Exact mass of the unnormalized Carlson Gaussian weight. -/
theorem integral_carlsonGaussianWeight
    {Delta w : ℝ} (hDelta : 0 < Delta) :
    (∫ t : ℝ, carlsonGaussianWeight Delta w t) =
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
  have hb : 0 < (1 / Delta ^ 2 : ℝ) := by positivity
  have hfun :
      (fun t : ℝ => carlsonGaussianWeight Delta w t) =
        fun t : ℝ => Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2) := by
    funext t
    unfold carlsonGaussianWeight
    congr 1
    field_simp [pow_ne_zero 2 hDelta.ne']
  rw [hfun]
  have hshift :
      (∫ t : ℝ, Real.exp (-(1 / Delta ^ 2) * (t - w) ^ 2)) =
        ∫ t : ℝ, Real.exp (-(1 / Delta ^ 2) * t ^ 2) := by
    convert integral_sub_right_eq_self
      (μ := volume)
      (f := fun t : ℝ => Real.exp (-(1 / Delta ^ 2) * t ^ 2)) w using 1
  rw [hshift, integral_gaussian]

/-- The exact inverse-cube right-edge cancellation promoted to the Gaussian
`L²` boundary norm at `Re(z)=4`. -/
theorem norm_sq_carlsonGaussianPoleFreeLpValue_four_le
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) :
    ‖carlsonGaussianPoleFreeLpValue Delta w Y0 Y1
        hDelta hY0 hY01 (4 : ℂ)
          (by norm_num : (4 : ℂ).re ∈ Icc (1 / 2 : ℝ) 4)‖ ^ 2 ≤
      Real.exp (16 / Delta ^ 2) *
        ((10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3)) ^ 2 *
          Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
  let H : ℂ → ℂ := poleFreeTwoScaleMollifiedZetaError Y0 Y1
  let phi : ℝ → ℂ :=
    carlsonGaussianHilbertSection Delta w H (4 : ℂ)
  let C : ℝ := (10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3)
  have hmem : MemLp phi 2 volume := by
    exact memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
      (Delta := Delta) (w := w) (z := (4 : ℂ))
      hDelta hY0 hY01
        (by norm_num : (4 : ℂ).re ∈ Icc (1 / 2 : ℝ) 4)
  have hsectionInt : Integrable (fun t => ‖phi t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  have hb : 0 < (1 / Delta ^ 2 : ℝ) := by positivity
  have hweightInt : Integrable (carlsonGaussianWeight Delta w) := by
    have hbase := integrable_exp_neg_mul_sq hb
    have hshift := hbase.comp_sub_right w
    convert hshift using 1
    funext t
    unfold carlsonGaussianWeight
    congr 1
    field_simp [pow_ne_zero 2 hDelta.ne']
  have hmajorInt : Integrable (fun t : ℝ =>
      (Real.exp (16 / Delta ^ 2) * C ^ 2) *
        carlsonGaussianWeight Delta w t) :=
    hweightInt.const_mul (Real.exp (16 / Delta ^ 2) * C ^ 2)
  have hpoint (t : ℝ) :
      ‖phi t‖ ^ 2 ≤
        (Real.exp (16 / Delta ^ 2) * C ^ 2) *
          carlsonGaussianWeight Delta w t := by
    have hH : ‖H ((4 : ℂ) + I * (t : ℂ))‖ ≤ C := by
      exact norm_poleFreeTwoScaleMollifiedZetaError_le_ten_div_three_mul_inv_cube
        hY0 hY01 (by norm_num)
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hHsq : ‖H ((4 : ℂ) + I * (t : ℂ))‖ ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hC).2 hH
    dsimp [phi]
    change ‖carlsonGaussianHilbertSection Delta w H ((4 : ℝ) : ℂ) t‖ ^ 2 ≤ _
    rw [norm_sq_carlsonGaussianHilbertSection_real
      (Delta := Delta) (w := w) hDelta.ne' H 4 t]
    calc
      Real.exp (4 ^ 2 / Delta ^ 2) *
            carlsonGaussianWeight Delta w t *
            ‖H ((4 : ℂ) + I * (t : ℂ))‖ ^ 2 ≤
          Real.exp (4 ^ 2 / Delta ^ 2) *
            carlsonGaussianWeight Delta w t * C ^ 2 := by
        exact mul_le_mul_of_nonneg_left hHsq
          (mul_nonneg (Real.exp_pos _).le (by
            unfold carlsonGaussianWeight
            positivity))
      _ = (Real.exp (16 / Delta ^ 2) * C ^ 2) *
            carlsonGaussianWeight Delta w t := by ring
  rw [norm_sq_carlsonGaussianPoleFreeLpValue
    hDelta hY0 hY01
      (by norm_num : (4 : ℂ).re ∈ Icc (1 / 2 : ℝ) 4)]
  change (∫ t : ℝ, ‖phi t‖ ^ 2) ≤ _
  calc
    (∫ t : ℝ, ‖phi t‖ ^ 2) ≤
        ∫ t : ℝ, (Real.exp (16 / Delta ^ 2) * C ^ 2) *
          carlsonGaussianWeight Delta w t :=
      integral_mono hsectionInt hmajorInt
        hpoint
    _ = (Real.exp (16 / Delta ^ 2) * C ^ 2) *
          Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
      rw [integral_const_mul, integral_carlsonGaussianWeight hDelta]
    _ = Real.exp (16 / Delta ^ 2) *
        ((10 / 3 : ℝ) * (1 / (Y0 : ℝ) ^ 3)) ^ 2 *
          Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
      dsimp [C]

end CarlsonZeroDensity
end PrimeNumberTheorem
