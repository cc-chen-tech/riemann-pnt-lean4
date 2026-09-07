import PrimeNumberTheorem.MWKFCubicAFEShiftReassembly

open PrimeNumberTheorem.MWKFCubic MeasureTheory

-- All integer shifts, not only a finite truncation.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Summable (fun δ : ℤ ↦ ∫ p : ℝ × ℝ,
      ‖cubicAFEBoundaryPhysicalKernel W T X V d e δ p.1 p.2‖) :=
  summable_integral_norm_cubicAFEBoundaryPhysicalKernel W hT hX V hd he

#check summable_shift_cubicAFEZeroModeBoxFinite
#check summable_shift_cubicAFENonzeroModeBoxFinite
#check tsum_shift_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero

-- Modulus one, negative finite height, and every signed nonzero shift.
example (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) :
    Summable (fun δ : {δ : ℤ // δ ≠ 0} ↦ ∑' jk : ℕ × ℕ,
      cubicAFENonzeroModeBoxFinite (d := 1) W T 1 (-2)
        (by norm_num : 0 < 1) δ.val jk) :=
  summable_shift_cubicAFENonzeroModeBoxFinite W hT (by norm_num) (-2) (by norm_num) (by norm_num)
