import PrimeNumberTheorem.MWKFCubicAFEZeroModeReassembly

open PrimeNumberTheorem.MWKFCubic MeasureTheory

-- Infinite real-space dyadic reassembly retains both lower-boundary weights.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) :
    HasSum (fun jk : ℕ × ℕ ↦ cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk)
      ((((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∫ t : ℝ, ∫ x : ℝ,
        ((cubicAFEDyadicLowerWeight x *
          cubicAFEDyadicLowerWeight (cubicAFEProgressionRealSecond d e δ x) : ℝ) : ℂ) *
            cubicAFEProgressionPhysicalSummand W T X V d e δ t x) :=
  hasSum_cubicAFEZeroModeBoxFinite W hT hX V hd he δ

#check integrable_cubicAFEBoundaryPhysicalKernel
#check summable_integral_norm_cubicAFEProgressionDyadicKernel
#check summable_cubicAFENonzeroModeBoxFinite
#check tsum_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero

-- No nonnegative-height, positive-shift or coprime d/e hypothesis is hidden.
example (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) :
    Summable (fun jk : ℕ × ℕ ↦
      cubicAFENonzeroModeBoxFinite (d := 2) W T 1 (-3) (by norm_num : 0 < 4) (-6) jk) :=
  summable_cubicAFENonzeroModeBoxFinite W hT (by norm_num) (-3) (by norm_num) (by norm_num) (-6)
