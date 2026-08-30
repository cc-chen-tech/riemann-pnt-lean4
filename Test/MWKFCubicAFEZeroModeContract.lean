import PrimeNumberTheorem.MWKFCubicAFEZeroMode

open PrimeNumberTheorem.MWKFCubic

#check cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero
#check cubicAFEZeroModeBoxFinite_eq_physicalIntegral

open MeasureTheory

-- The nonzero mode retains *both* frequency signs and the exact Jacobian.
example (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) :
    cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk =
      (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : {h : ℤ // h ≠ 0},
        cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h.val := rfl

#check (@cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero :
  ∀ (W : CubicTestWeight) {T : ℝ}, T ≠ 0 → ∀ {X : ℝ}, 1 / 2 < X →
    ∀ (V : ℝ) {d e : ℕ}, 0 < d → ∀ he : 0 < e, ∀ (δ : ℤ) (jk : ℕ × ℕ),
    cubicAFEFrequencyBoxFinite (d := d) W T X V he δ jk =
      cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk +
      cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk)

-- Zero Fourier frequency is not delta=0: the original shift-dependent
-- physical phase remains in this actual double integral even for delta=-6.
example (W : CubicTestWeight) (T X V : ℝ) (he : 0 < 4) (jk : ℕ × ℕ) :
    cubicAFEZeroModeBoxFinite (d := 2) W T X V he (-6) jk =
      (((4 / Nat.gcd 2 4 : ℕ) : ℂ)⁻¹) * ∫ t : ℝ, ∫ x : ℝ,
        (cubicAFEProgressionDyadicCutoff (d := 2) he (-6) jk.1 jk.2 x : ℂ) *
          cubicAFEProgressionPhysicalSummand W T X V 2 4 (-6) t x :=
  cubicAFEZeroModeBoxFinite_eq_physicalIntegral W T X V he (-6) jk
