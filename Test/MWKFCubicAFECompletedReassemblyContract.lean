import PrimeNumberTheorem.MWKFCubicAFECompletedReassembly

open PrimeNumberTheorem.MWKFCubic

#check hasSum_cubicAFECompletedZeroModeBox
#check hasSum_cubicAFECompletedNonzeroModeBox
#check cubicAFECompletedBoundary_zero_add_nonzero
#check cubicAFEDyadicCompletionCorrection_eq_finiteSum
#check integral_cubicAFEDyadicCompletionCorrection_eq_zeroModes
#check tsum_cubicAFECompletedModes_eq_original

open Complex MeasureTheory

-- Literal physical correction, with no assumed convergence or interchange.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J L : ℕ)
    (hL : 2 * (2 : ℝ)^J * cubicAFECompletedBoundarySize d e δ < (2 : ℝ)^L) :
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) *
      (∫ t : ℝ, ∫ x : ℝ, cubicAFEDyadicCompletionCorrection W T X V d e δ J t x) =
      ∑ jk ∈ cubicAFECompletedLowerScaleBoxes J L,
        cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk :=
  integral_cubicAFEDyadicCompletionCorrection_eq_zeroModes W hT hX V hd he δ J L hL

-- Any finite depth, all shifts, no assumed zero-mode vanishing.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) :
    (∑' jk : ℕ × ℕ, cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk) +
      (∑' jk : ℕ × ℕ, cubicAFECompletedNonzeroModeBox (d := d) W T X V he δ J jk) =
    (∑' jk : ℕ × ℕ, cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk) +
      (∑' jk : ℕ × ℕ, cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk) :=
  tsum_cubicAFECompletedModes_eq_original W hT hX V hd he δ J
