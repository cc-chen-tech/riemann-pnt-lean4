import PrimeNumberTheorem.VKEdgeDesmoothedLeftDerivative

open Complex Metric

#check PrimeNumberTheorem.exists_dynamicCubicLeftBoundary_zeroFree_closedBall

example :
    ∃ b T0 : ℝ, 0 < b ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := PrimeNumberTheorem.ExplicitFormulaResidues.dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 2 ∧
          ∀ t : ℝ, T0 + 1 ≤ |t| → |t| + 1 ≤ H →
            ∀ z ∈ closedBall ((a : ℂ) + I * t) (a / 2),
              riemannZeta z ≠ 0 :=
  PrimeNumberTheorem.exists_dynamicCubicLeftBoundary_zeroFree_closedBall

#check PrimeNumberTheorem.exists_dynamicCubicLeftBoundary_closedBall_logDeriv_le_log_sq

example :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := PrimeNumberTheorem.ExplicitFormulaResidues.dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 3 ∧
          ∀ t : ℝ, T0 + 1 ≤ |t| → |t| + 1 ≤ H →
            ∀ z ∈ closedBall ((a : ℂ) + I * t) (a / 2),
              z ≠ 1 ∧ riemannZeta z ≠ 0 ∧
                ‖logDeriv riemannZeta z‖ ≤
                  C * (1 + Real.log (H + 6)) ^ 2 :=
  PrimeNumberTheorem.exists_dynamicCubicLeftBoundary_closedBall_logDeriv_le_log_sq

#check PrimeNumberTheorem.exists_dynamicCubicLeftBoundary_deriv_logDeriv_le_log_cube

example :
    ∃ b D T0 : ℝ, 0 < b ∧ 0 ≤ D ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := PrimeNumberTheorem.ExplicitFormulaResidues.dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 3 ∧
          ∀ t : ℝ, T0 + 1 ≤ |t| → |t| + 1 ≤ H →
            ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤
              D * (1 + Real.log (H + 6)) ^ 3 :=
  PrimeNumberTheorem.exists_dynamicCubicLeftBoundary_deriv_logDeriv_le_log_cube
