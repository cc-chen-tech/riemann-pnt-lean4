import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonAutomaticDecay

namespace PrimeNumberTheorem

open Filter Topology

/-- Carlson's uniform contour certificate, evaluated at the balanced
intermediate height and the final polynomial height, forces the actual moving
zeta strip mass to decay.  The remaining assumptions are explicit arithmetic
height conditions and the honest logarithmic gap. -/
theorem exists_actualMovingCarlsonContourAutomaticDecay
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    ∃ A C₁ C₂ : ℝ, 0 ≤ A ∧ 1 ≤ C₁ ∧ 1 ≤ C₂ ∧
      ((∀ᶠ m : ℕ in atTop,
          CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta m)
              (carlsonPolynomialHeight
                (carlsonMovingBalancedCut alpha delta m) (m : ℝ)) ∧
            CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * delta m)
              (carlsonPolynomialHeight alpha (m : ℝ))) →
        Tendsto
          (actualMovingCarlsonStripMass alpha delta)
          atTop (nhds 0)) := by
  have hdeltaQuarter :
      ∀ᶠ m : ℕ in atTop, 0 < delta m ∧ delta m < 1 / 4 := by
    filter_upwards [hdelta] with m hm
    exact ⟨hm.1, hm.2.1.trans_lt (by norm_num)⟩
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hcount⟩ :=
    exists_actualMovingCarlsonTwoHeightCountCertificate
      (alpha := alpha) (delta := delta)
      (gamma := carlsonMovingBalancedCut alpha delta)
      hdeltaQuarter
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  intro hconditions
  exact
    tendsto_actualMovingCarlsonStripMass_zero_of_pointwiseCount
      hA halpha hdelta hgap (hcount hconditions)

end PrimeNumberTheorem
