import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonCertificate
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingTwoHeightCountCertificate

namespace PrimeNumberTheorem

open Filter

/-- Low-height actual kernel budget after replacing the zero count by the
uniform pointwise Carlson majorant. -/
noncomputable def actualMovingCarlsonLowPointwiseMajorant
    (A : ℝ) (delta gamma : ℕ → ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) ^ (-delta m) / (1 - 2 * delta m)) *
    carlsonPointwiseCountBudget A (1 - 2 * delta m)
      (carlsonPolynomialHeight (gamma m) (m : ℝ))

/-- High-height actual kernel budget after replacing the zero count by the
uniform pointwise Carlson majorant. -/
noncomputable def actualMovingCarlsonHighPointwiseMajorant
    (A alpha : ℝ) (delta gamma : ℕ → ℝ) (m : ℕ) : ℝ :=
  polynomialOrdinateRectangleKernel
      (1 - delta m) (gamma m) (m : ℝ) *
    carlsonPointwiseCountBudget A (1 - 2 * delta m)
      (carlsonPolynomialHeight alpha (m : ℝ))

/-- The complete pointwise majorant produced by the actual two-height count
certificate before power and logarithm normalization. -/
noncomputable def actualMovingCarlsonTwoHeightPointwiseMajorant
    (A alpha : ℝ) (delta gamma : ℕ → ℝ) (m : ℕ) : ℝ :=
  actualMovingCarlsonLowPointwiseMajorant A delta gamma m +
    actualMovingCarlsonHighPointwiseMajorant A alpha delta gamma m

/-- Actual Carlson low/high budgets are bounded by the corresponding
pointwise majorants. -/
theorem actualMovingCarlsonTwoHeightBudget_le_pointwiseMajorant
    {A alpha : ℝ} {delta gamma : ℕ → ℝ}
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m ∧ delta m ≤ 1 / 8)
    (hcount :
      IsActualMovingCarlsonTwoHeightCountCertificate A alpha delta gamma) :
    ∀ᶠ m : ℕ in atTop,
      actualCarlsonTwoHeightLowBudget
          (1 - 2 * delta m) (1 - delta m) (gamma m) (m : ℝ) +
        actualCarlsonTwoHeightHighBudget
          (1 - 2 * delta m) (1 - delta m) alpha (gamma m) (m : ℝ) ≤
      actualMovingCarlsonTwoHeightPointwiseMajorant
        A alpha delta gamma m := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), hdelta, hcount] with
      m hm hdm hNm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := zero_le_one.trans hmReal
  have hsigma : 0 < 1 - 2 * delta m := by linarith
  have hlowFactor :
      0 ≤ (m : ℝ) ^ (-delta m) / (1 - 2 * delta m) := by
    exact div_nonneg (Real.rpow_nonneg hmNonneg _) hsigma.le
  have hhighFactor :
      0 ≤ polynomialOrdinateRectangleKernel
        (1 - delta m) (gamma m) (m : ℝ) := by
    unfold polynomialOrdinateRectangleKernel
    exact div_nonneg (Real.rpow_nonneg hmNonneg _)
      (Real.rpow_nonneg hmNonneg _)
  unfold actualMovingCarlsonTwoHeightPointwiseMajorant
    actualMovingCarlsonLowPointwiseMajorant
    actualMovingCarlsonHighPointwiseMajorant
    actualCarlsonTwoHeightLowBudget
    actualCarlsonTwoHeightHighBudget
  have hlow := mul_le_mul_of_nonneg_left hNm.1 hlowFactor
  have hhigh := mul_le_mul_of_nonneg_left hNm.2 hhighFactor
  have hexponent : 1 - delta m - 1 = -delta m := by ring
  rw [hexponent]
  exact add_le_add hlow hhigh

end PrimeNumberTheorem
