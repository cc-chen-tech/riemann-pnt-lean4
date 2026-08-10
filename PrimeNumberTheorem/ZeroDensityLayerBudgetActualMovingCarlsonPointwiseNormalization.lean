import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonBudgetFromCount

namespace PrimeNumberTheorem

/-- Carlson's balanced intermediate polynomial-height exponent at a moving
real boundary. -/
noncomputable def carlsonMovingBalancedCut
    (alpha : ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  carlsonTwoHeightBalancedCut (1 - 2 * delta m) alpha

/-- Exact expansion of the public pointwise Carlson count budget after
substitution of a polynomial height. -/
theorem carlsonPointwiseCountBudget_polynomialHeight_eq
    {A sigma alpha x : ℝ} (hx : 0 < x) :
    carlsonPointwiseCountBudget A sigma
        (carlsonPolynomialHeight alpha x) =
      (125 * CarlsonZeroDensity.carlsonFinalCoefficient A sigma *
          alpha ^ (4 : ℕ)) *
        (x ^ (alpha * (4 * sigma * (1 - sigma))) *
          (Real.log x) ^ (4 : ℕ)) := by
  unfold carlsonPointwiseCountBudget carlsonPolynomialHeight
  rw [← Real.rpow_mul hx.le]
  rw [Real.log_rpow hx alpha]
  ring

/-- Exact low-height normalization before choosing the balanced cut. -/
theorem actualMovingCarlsonLowPointwiseMajorant_eq
    {A x delta gamma : ℝ} (hx : 0 < x) :
    ((x ^ (-delta) / (1 - 2 * delta)) *
        carlsonPointwiseCountBudget A (1 - 2 * delta)
          (carlsonPolynomialHeight gamma x)) =
      (125 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
          gamma ^ (4 : ℕ) / (1 - 2 * delta)) *
        (x ^ (-delta +
            gamma * (4 * (1 - 2 * delta) * (1 - (1 - 2 * delta)))) *
          (Real.log x) ^ (4 : ℕ)) := by
  rw [carlsonPointwiseCountBudget_polynomialHeight_eq hx]
  calc
    _ = (125 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
            gamma ^ (4 : ℕ) / (1 - 2 * delta)) *
          ((x ^ (-delta) *
              x ^ (gamma *
                (4 * (1 - 2 * delta) * (1 - (1 - 2 * delta))))) *
            (Real.log x) ^ (4 : ℕ)) := by ring
    _ = _ := by rw [← Real.rpow_add hx]

/-- Exact high-height normalization before choosing the balanced cut. -/
theorem actualMovingCarlsonHighPointwiseMajorant_eq
    {A alpha x delta gamma : ℝ} (hx : 0 < x) :
    polynomialOrdinateRectangleKernel (1 - delta) gamma x *
        carlsonPointwiseCountBudget A (1 - 2 * delta)
          (carlsonPolynomialHeight alpha x) =
      (125 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
          alpha ^ (4 : ℕ)) *
        (x ^ (-delta - gamma +
            alpha * (4 * (1 - 2 * delta) * (1 - (1 - 2 * delta)))) *
          (Real.log x) ^ (4 : ℕ)) := by
  rw [carlsonPointwiseCountBudget_polynomialHeight_eq hx]
  unfold polynomialOrdinateRectangleKernel
  have hexponent : 1 - delta - 1 = -delta := by ring
  rw [hexponent]
  calc
    _ = (125 * CarlsonZeroDensity.carlsonFinalCoefficient A (1 - 2 * delta) *
            alpha ^ (4 : ℕ)) *
          (((x ^ (-delta) / x ^ gamma) *
              x ^ (alpha *
                (4 * (1 - 2 * delta) * (1 - (1 - 2 * delta))))) *
            (Real.log x) ^ (4 : ℕ)) := by ring
    _ = _ := by
      rw [← Real.rpow_sub hx, ← Real.rpow_add hx]

end PrimeNumberTheorem
