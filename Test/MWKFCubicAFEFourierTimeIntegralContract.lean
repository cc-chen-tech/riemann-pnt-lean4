import PrimeNumberTheorem.MWKFCubicAFEFourierTimeIntegral

open PrimeNumberTheorem.MWKFCubic

#check integral_fourier_cubicAFEProgressionCutoffSummand

open Complex MeasureTheory
open scoped FourierTransform

#check (@integral_fourier_cubicAFEProgressionCutoffSummand :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, 0 < d → 0 < e → ∀ {δ : ℤ}
      (χ : CubicProgressionCutoff d e δ) (ξ : ℝ),
    (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t) ξ) =
      𝓕 (fun x : ℝ ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x) ξ)

-- Zero frequency and a negative shift are included without gcd exclusions.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) (χ : CubicProgressionCutoff 1 1 (-3)) :
    (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t) 0) =
      𝓕 (fun x : ℝ ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x) 0 :=
  integral_fourier_cubicAFEProgressionCutoffSummand W hT hX V (by norm_num) (by norm_num) χ 0

-- The actual product-space integrand and Fourier sign are tested directly.
#check (@integrable_cubicAFEProgressionCutoffFourier_joint :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, 0 < d → 0 < e → ∀ {δ : ℤ}
      (χ : CubicProgressionCutoff d e δ) (ξ : ℝ),
    Integrable (fun p : ℝ × ℝ ↦
      Complex.exp (((-2 * Real.pi * p.2 * ξ : ℝ) : ℂ) * I) *
        cubicAFEProgressionCutoffSummand W T X V χ p.1 p.2) (volume.prod volume))
