import PrimeNumberTheorem.MWKFCubicAFEQuadraticEndpoint

open PrimeNumberTheorem.MWKFCubic

#check integrableOn_cubicAFERealProductWeightVertical_quadratic

-- A negative shift starts the physical domain at x=1, not x=0.
example (t : ℝ) : MeasureTheory.IntegrableOn (fun x : ℝ ↦
    (((x * (-1 + x)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      cubicAFERealProductWeightVertical t (3 / 4) (x * (-1 + x)))
    {x : ℝ | 0 < x ∧ 0 < -1 + x} := by
  simpa using integrableOn_cubicAFERealProductWeightVertical_quadratic t
    (X := 3 / 4) (r := 1) (s := 1) (δ := -1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
