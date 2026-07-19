import PrimeNumberTheorem.SmoothedErrorTransfer

open Complex Set
open scoped BigOperators Interval

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

example {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h) (ha : 0 < a)
    (hac : a < c) (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX polesY : Finset ℂ) (residueX residueY : ℂ → ℂ),
      ‖((∑ p ∈ polesX, residueX p) -
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
            x a c W) -
          (PrimeNumberTheorem.smoothedChebyshevPsi x : ℂ)‖ ≤
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError x c W ∧
      ‖((∑ p ∈ polesY, residueY p) -
          PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
            (x + h) a c W) -
          (PrimeNumberTheorem.smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
          (x + h) c W ∧
      PrimeNumberTheorem.chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x a c W)).re +
            (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError x c W +
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
                (x + h) c W)) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderContourRemainder
                  x a c W)).re -
            (PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError x c W +
              PrimeNumberTheorem.ExplicitFormulaResidues.secondOrderPerronError
                (x + h) c W)) /
              Real.log ((x + h) / x) ≤
          PrimeNumberTheorem.chebyshevPsi (x + h) := by
  rcases
      PrimeNumberTheorem.ExplicitFormulaResidues.exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula
        hx hh ha hac hc hW hboundary with
    ⟨polesX, residueX, polesY, residueY, _hpolesX, _hclassX, _hresidueX,
      _hpolesY, _hclassY, _hresidueY, hxError, hyError, hbounds⟩
  exact ⟨polesX, polesY, residueX, residueY, hxError, hyError, hbounds⟩
