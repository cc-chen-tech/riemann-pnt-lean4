import PrimeNumberTheorem.SmoothedErrorTransfer

open Complex

example (approx : ℝ → ℝ → ℂ) (error : ℝ → ℝ → ℝ)
    {x h T : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hxError : ‖approx x T - (PrimeNumberTheorem.smoothedChebyshevPsi x : ℂ)‖ ≤
      error x T)
    (hyError : ‖approx (x + h) T -
      (PrimeNumberTheorem.smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        error (x + h) T) :
    PrimeNumberTheorem.chebyshevPsi x ≤
        ((approx (x + h) T).re - (approx x T).re +
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ∧
      ((approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ≤
        PrimeNumberTheorem.chebyshevPsi (x + h) :=
  PrimeNumberTheorem.chebyshevPsi_bounds_of_smoothedApproximation
    approx error hx hh hxError hyError
