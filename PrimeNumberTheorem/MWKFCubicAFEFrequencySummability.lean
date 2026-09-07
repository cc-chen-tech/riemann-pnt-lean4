import PrimeNumberTheorem.MWKFCubicAFEFrequencyMoment

open Complex Filter MeasureTheory
open scoped FourierTransform SchwartzMap

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Absolute convergence of the actual integrated frequency series

The actual integrated kernel is Schwartz. Its Fourier transform remains
Schwartz after a nonzero dilation, so its integer samples are summable.
The full inverse-residue phase has norm one. These are fixed-parameter
summability statements, not estimates uniform over dyadic boxes or T.
-/

private theorem summable_schwartz_int (F : 𝓢(ℝ, ℂ)) :
    Summable (fun h : ℤ ↦ F (h : ℝ)) := by
  apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
  simpa only [Real.norm_eq_abs, Function.comp_def] using
    (F.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite

private theorem summable_schwartz_fourier_dilate (F : 𝓢(ℝ, ℂ)) {s : ℝ} (hs : s ≠ 0) :
    Summable (fun h : ℤ ↦ 𝓕 (F : ℝ → ℂ) ((h : ℝ) / s)) := by
  let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ s⁻¹ (inv_ne_zero hs)).toContinuousLinearEquiv
  let G : 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (𝓕 F)
  have hg := summable_schwartz_int G
  have heq : (fun h : ℤ ↦ G (h : ℝ)) = fun h : ℤ ↦ 𝓕 (F : ℝ → ℂ) ((h : ℝ) / s) := by
    funext h
    change (𝓕 F) (s⁻¹ * (h : ℝ)) = _
    rw [mul_comm, ← div_eq_mul_inv]
    rfl
  rwa [heq] at hg

theorem summable_integral_cubicAFEProgressionFourier
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) {δ : ℤ}
    (χ : CubicProgressionCutoff d e δ) {s : ℝ} (hs : s ≠ 0) :
    Summable (fun h : ℤ ↦ ∫ t : ℝ,
      𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t) ((h : ℝ) / s)) := by
  simp_rw [integral_fourier_cubicAFEProgressionCutoffSummand W hT hX V hd he χ]
  exact summable_schwartz_fourier_dilate
    (cubicAFEIntegratedProgressionSchwartz W hT hX V hd he χ) hs

/-- A full physical Fourier coefficient, before the outer 1/s Jacobian. -/
noncomputable def cubicAFEFrequencyCoefficient
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) (h : ℤ) : ℂ :=
  (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V
    (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t)
      ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ))) *
  Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
    (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
      ((e / Nat.gcd d e : ℕ) : ℂ))

theorem norm_cubicAFEFrequencyCoefficient
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) (h : ℤ) :
    ‖cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h‖ =
    ‖∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t)
        ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ))‖ := by
  unfold cubicAFEFrequencyCoefficient
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, Complex.div_re]

theorem summable_norm_cubicAFEFrequencyCoefficient
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    Summable (fun h : ℤ ↦ ‖cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h‖) := by
  have hq : 0 < Nat.gcd d e := by
    simpa only [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left d he
  have hsN : e / Nat.gcd d e ≠ 0 := by
    intro hz
    have heq := (gcd_extraction hq.ne').2.1
    rw [hz, mul_zero] at heq
    exact he.ne' heq
  have hs : ((e / Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hsN
  simp_rw [norm_cubicAFEFrequencyCoefficient]
  exact (summable_integral_cubicAFEProgressionFourier W hT hX V hd he
    (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) hs).norm

theorem summable_cubicAFEFrequencyCoefficient
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    Summable (cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk) :=
  (summable_norm_cubicAFEFrequencyCoefficient W hT hX V hd he δ jk).of_norm

end PrimeNumberTheorem.MWKFCubic
