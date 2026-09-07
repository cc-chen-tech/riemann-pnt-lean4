import PrimeNumberTheorem.MWKFCubicAFEIntegratedPoisson

open PrimeNumberTheorem.MWKFCubic

#check cubicAFEIntegratedProgression_poisson
#check integral_cubicAFEDyadicPoissonTerm_eq_frequencySum

open Complex MeasureTheory
open scoped FourierTransform

-- The frequency sum is outside the time integral; all normalization and
-- inverse-residue phases are literal. No frequency majorant is an input.
#check (@integral_cubicAFEDyadicPoissonTerm_eq_frequencySum :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, 0 < d → ∀ he : 0 < e, ∀ (δ : ℤ) (jk : ℕ × ℕ),
    (∫ t : ℝ, cubicAFEDyadicPoissonTerm (d := d) W T X V he δ jk t) =
      (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
        (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V
          (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t)
            ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ))) *
        Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
          (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
            ((e / Nat.gcd d e : ℕ) : ℂ)))

-- No positivity of the shift or coprimality between shift and modulus.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) (χ : CubicProgressionCutoff 2 4 (-6)) :
    (∑' m : cubicAFEProgression 2 4 (-6), ∫ t : ℝ,
      cubicAFEProgressionCutoffSummand W T X V χ t m.val) =
    (((4 / Nat.gcd 2 4 : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
      𝓕 (fun x : ℝ ↦ ∫ t : ℝ, cubicAFEProgressionCutoffSummand W T X V χ t x)
        ((h : ℝ) / ((4 / Nat.gcd 2 4 : ℕ) : ℝ)) *
      Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (-6 : ℂ) *
        (Nat.gcdA (2 / Nat.gcd 2 4) (4 / Nat.gcd 2 4) : ℂ) /
          ((4 / Nat.gcd 2 4 : ℕ) : ℂ)) := by
  simpa only [Int.cast_neg, Int.cast_ofNat] using
    cubicAFEIntegratedProgression_poisson W hT hX V (by norm_num) (by norm_num) χ
