import HardyTheorem.SelbergSqrtZetaLocal

open scoped BigOperators
open HardyTheorem

noncomputable section

example : PowerSeries ℝ := selbergSqrtZetaEulerFactor

example (k : ℕ) : ℝ := selbergSqrtZetaLocalCoeff k

example : selbergSqrtZetaLocalCoeff 0 = 1 :=
  selbergSqrtZetaLocalCoeff_zero

example : selbergSqrtZetaLocalCoeff 1 = -(1 / 2 : ℝ) :=
  selbergSqrtZetaLocalCoeff_one

example :
    selbergSqrtZetaEulerFactor * selbergSqrtZetaEulerFactor =
      1 - PowerSeries.X :=
  selbergSqrtZetaEulerFactor_sq

example (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        selbergSqrtZetaLocalCoeff ij.1 *
          selbergSqrtZetaLocalCoeff ij.2) =
      if k = 0 then 1 else if k = 1 then -1 else 0 :=
  sum_antidiagonal_selbergSqrtZetaLocalCoeff_mul k

example : PowerSeries ℝ := selbergSqrtZetaEulerWeightedDerivative

example :
    selbergSqrtZetaEulerFactor *
        PowerSeries.derivative ℝ selbergSqrtZetaEulerFactor =
      -PowerSeries.C (1 / 2 : ℝ) :=
  selbergSqrtZetaEulerFactor_mul_derivative

example (k : ℕ) :
    PowerSeries.coeff k selbergSqrtZetaEulerWeightedDerivative =
      (k : ℝ) * selbergSqrtZetaLocalCoeff k :=
  coeff_selbergSqrtZetaEulerWeightedDerivative k

example :
    PowerSeries.C (4 : ℝ) *
        ((1 - PowerSeries.X) *
          (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ))) =
      PowerSeries.X ^ (2 : ℕ) :=
  selbergSqrtZetaEulerWeightedDerivative_sq_identity

example (k : ℕ) :
    4 * (PowerSeries.coeff k
          (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ)) -
        if 1 ≤ k then
          PowerSeries.coeff (k - 1)
            (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ))
        else 0) =
      if k = 2 then 1 else 0 :=
  coeff_selbergSqrtZetaEulerWeightedDerivative_sq_recurrence k

example (k : ℕ) :
    PowerSeries.coeff k
        (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ)) =
      if 2 ≤ k then (1 / 4 : ℝ) else 0 :=
  coeff_selbergSqrtZetaEulerWeightedDerivative_sq k

example (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        (ij.1 : ℝ) * selbergSqrtZetaLocalCoeff ij.1 *
          ((ij.2 : ℝ) * selbergSqrtZetaLocalCoeff ij.2)) =
      if 2 ≤ k then (1 / 4 : ℝ) else 0 :=
  sum_antidiagonal_mul_selbergSqrtZetaLocalCoeff_mul k

example (L : ℝ) (k : ℕ) : ℝ :=
  selbergSqrtZetaLocalTaperedCoeff L k

example (L : ℝ) (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        selbergSqrtZetaLocalTaperedCoeff L ij.1 *
          selbergSqrtZetaLocalTaperedCoeff L ij.2) =
      if k = 0 then 1
      else if k = 1 then -1 + L
      else L ^ 2 / 4 :=
  sum_antidiagonal_selbergSqrtZetaLocalTaperedCoeff_mul L k

example (L : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
        if k = 0 then 1
        else if k = 1 then -1 + L
        else L ^ 2 / 4) =
      L + (n : ℝ) * L ^ 2 / 4 :=
  sum_range_selbergSqrtZetaLocalTaperedConvolution L n
