import PrimeNumberTheorem.MWKFCubicAFESeparatedMoment

open PrimeNumberTheorem.MWKFCubic

#check cubicAFEFrequencyMomentFinite_eq_zero_add_nonzero
#check cubicAFEMollifiedMomentFinite_eq_diagonal_zero_nonzero
#check tendsto_cubicAFEDiagonal_zero_nonzero

-- The only limit asserted here is of the recombined expression.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X) :
    Filter.Tendsto (fun V : ℝ ↦
      (cubicAFEDiagonalMomentFinite W T X V + cubicAFEZeroModeMomentFinite W T X V) +
        cubicAFENonzeroModeMomentFinite W T X V)
      Filter.atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) :=
  tendsto_cubicAFEDiagonal_zero_nonzero W hT hX
