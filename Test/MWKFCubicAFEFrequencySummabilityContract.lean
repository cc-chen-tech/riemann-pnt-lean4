import PrimeNumberTheorem.MWKFCubicAFEFrequencySummability

open PrimeNumberTheorem.MWKFCubic

#check summable_integral_cubicAFEProgressionFourier
#check summable_norm_cubicAFEFrequencyCoefficient
#check summable_cubicAFEFrequencyCoefficient

open Complex MeasureTheory
open scoped FourierTransform

#check (@summable_norm_cubicAFEFrequencyCoefficient :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, 0 < d → ∀ he : 0 < e, ∀ (δ : ℤ) (jk : ℕ × ℕ),
    Summable (fun h : ℤ ↦ ‖cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h‖))

-- Negative dilation, negative shift and modulus one require no new input.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) (χ : CubicProgressionCutoff 1 1 (-3)) :
    Summable (fun h : ℤ ↦ ∫ t : ℝ,
      𝓕 (cubicAFEProgressionCutoffSummand W T X V χ t) ((h : ℝ) / (-1))) :=
  summable_integral_cubicAFEProgressionFourier W hT hX V (by norm_num) (by norm_num) χ (by norm_num)
