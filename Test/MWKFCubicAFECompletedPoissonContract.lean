import PrimeNumberTheorem.MWKFCubicAFECompletedPoisson

open PrimeNumberTheorem.MWKFCubic Complex MeasureTheory
open scoped FourierTransform

#check summable_cubicAFECompletedFrequencyCoefficient
#check cubicAFECompletedFrequencyBox_eq_progression
#check cubicAFECompletedFrequencyCoefficient_zero
#check cubicAFECompletedFrequencyBox_eq_zero_add_nonzero
#check cubicAFECompletedFrequencyBox_lower_scale
#check cubicAFECompletedLowerScale_zero_add_nonzero
#check cubicAFECompletedFrequencyCoefficient_shift

-- This is a zero/nonzero pairing, NOT separate vanishing of the modes.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ)
    {J : ℕ} {jk : ℕ × ℕ} (hjk : jk.1 < J ∨ jk.2 < J) :
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) *
      (∫ t : ℝ, ∫ x : ℝ, cubicAFEProgressionCutoffSummand W T X V
        (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) t x) +
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) *
      (∑' h : {h : ℤ // h ≠ 0}, cubicAFECompletedFrequencyCoefficient (d := d)
        W T X V he δ J jk h.val) = 0 :=
  cubicAFECompletedLowerScale_zero_add_nonzero W hT hX V hd he δ hjk
