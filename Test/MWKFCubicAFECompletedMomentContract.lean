import PrimeNumberTheorem.MWKFCubicAFECompletedMoment

open PrimeNumberTheorem.MWKFCubic

#check integrable_cubicAFECompletedBoundaryPhysicalKernel
#check hasSum_cubicAFECompletedZeroModeBox_physical
#check cubicAFEMollifiedMomentFinite_eq_diagonal_add_completed
#check tendsto_cubicAFEDiagonal_add_completed

open Complex Filter MeasureTheory
open scoped Topology

-- The literal completed lower weights stay inside the physical zero mode.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) :
    HasSum (cubicAFECompletedZeroModeBox (d := d) W T X V he δ J)
      ((((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∫ t : ℝ, ∫ x : ℝ,
        (cubicAFEDyadicCompletionWeight J x (cubicAFEProgressionRealSecond d e δ x) : ℂ) *
          cubicAFEProgressionPhysicalSummand W T X V d e δ t x) :=
  hasSum_cubicAFECompletedZeroModeBox_physical W hT hX V hd he δ J

-- The depth may vary with height, but only the RECOMBINED expression has a limit here.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X) (J : ℝ → ℕ) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFECompletedMomentFinite W T X V (J V))
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) :=
  tendsto_cubicAFEDiagonal_add_completed W hT hX J
