import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingTwoHeightPointwiseCount
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonPolynomialHeightComposition

namespace PrimeNumberTheorem

open Filter

/-- Actual zeta counts at both moving polynomial heights satisfy the public
pointwise Carlson majorants. -/
def IsActualMovingCarlsonTwoHeightCountCertificate
    (A alpha : ℝ) (delta gamma : ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    (ZeroDensity.zeroDensityCount (1 - 2 * delta m)
        (carlsonPolynomialHeight (gamma m) (m : ℝ)) : ℝ) ≤
      carlsonPointwiseCountBudget A (1 - 2 * delta m)
        (carlsonPolynomialHeight (gamma m) (m : ℝ)) ∧
    (ZeroDensity.zeroDensityCount (1 - 2 * delta m)
        (carlsonPolynomialHeight alpha (m : ℝ)) : ℝ) ≤
      carlsonPointwiseCountBudget A (1 - 2 * delta m)
        (carlsonPolynomialHeight alpha (m : ℝ))

/-- The uniform Carlson contour theorem automatically supplies the actual
two-height count certificate once its explicit height conditions hold
eventually.  No fixed-`sigma` asymptotic threshold occurs. -/
theorem exists_actualMovingCarlsonTwoHeightCountCertificate
    {alpha : ℝ} {delta gamma : ℕ → ℝ}
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m < 1 / 4) :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ((∀ᶠ m : ℕ in atTop,
          CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta m)
              (carlsonPolynomialHeight (gamma m) (m : ℝ)) ∧
            CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta m)
              (carlsonPolynomialHeight alpha (m : ℝ))) →
        IsActualMovingCarlsonTwoHeightCountCertificate
          A alpha delta gamma) := by
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hpointwise⟩ :=
    exists_carlson_moving_twoHeight_pointwise_count_certificate
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro hconditions
  filter_upwards [hdelta, hconditions] with m hdm hm
  exact hpointwise hdm.1 hdm.2 hm.1 hm.2

end PrimeNumberTheorem
