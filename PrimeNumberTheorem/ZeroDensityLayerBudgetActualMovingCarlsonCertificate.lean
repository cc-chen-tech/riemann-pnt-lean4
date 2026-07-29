import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualTwoHeightSplit
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingCoefficientGrowth

/-!
# Pointwise moving Carlson certificates for an actual zeta strip

This is the honest interface between the moving coefficient analysis and the
actual multiplicity-weighted zeta kernel.  It asks for pointwise low/high
Carlson count budgets; it does not infer them by substituting a moving
`sigma` into a fixed-`sigma` `IsBigO` theorem.
-/

open Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Actual relative PNT zero mass in the nondegenerate moving strip
`(1 - 2 delta, 1 - delta]`. -/
noncomputable def actualMovingCarlsonStripMass
    (alpha : ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ rho ∈ actualPositiveCarlsonStrip
      (1 - 2 * delta m) (1 - delta m)
      (carlsonPolynomialHeight alpha (m : ℝ)),
    ‖pntRelativeZeroContribution (m : ℝ) rho‖

/-- A pointwise moving Carlson certificate at two heights.

The certificate records exactly the input not supplied by the current
fixed-`sigma` Carlson theorem: a moving intermediate exponent and a bound for
the sum of its low/high actual count budgets. -/
def IsActualMovingCarlsonTwoHeightCertificate
    (alpha C : ℝ) (delta gamma : ℕ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    gamma m ≤ alpha ∧
      actualCarlsonTwoHeightLowBudget
          (1 - 2 * delta m) (1 - delta m) (gamma m) (m : ℝ) +
        actualCarlsonTwoHeightHighBudget
          (1 - 2 * delta m) (1 - delta m) alpha (gamma m) (m : ℝ) ≤
        carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingQuadraticLogEnvelope C delta) m

/-- The pointwise two-height certificate bounds the actual moving zeta strip
mass by the quadratic-coefficient balanced ratio. -/
theorem actualMovingCarlsonStripMass_le_quadraticRatio
    {alpha C : ℝ} {delta gamma : ℕ → ℝ}
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m ∧ delta m ≤ 1 / 8)
    (hcertificate :
      IsActualMovingCarlsonTwoHeightCertificate alpha C delta gamma) :
    ∀ᶠ m : ℕ in atTop,
      actualMovingCarlsonStripMass alpha delta m ≤
        carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingQuadraticLogEnvelope C delta) m := by
  filter_upwards [eventually_ge_atTop (1 : ℕ), hdelta, hcertificate] with
      m hm hdm hcert
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsigma : 0 < 1 - 2 * delta m := by linarith
  exact
    (sum_norm_actualPositiveCarlsonStrip_le_twoHeightBudget
      hmReal hsigma hcert.1).trans hcert.2

theorem actualMovingCarlsonStripMass_nonneg
    (alpha : ℝ) (delta : ℕ → ℝ) (m : ℕ) :
    0 ≤ actualMovingCarlsonStripMass alpha delta m := by
  unfold actualMovingCarlsonStripMass
  positivity

/-- A pointwise moving Carlson certificate plus the quadratic logarithmic gap
forces the actual multiplicity-weighted zeta strip mass to vanish. -/
theorem tendsto_actualMovingCarlsonStripMass_zero
    {alpha C : ℝ} {delta gamma : ℕ → ℝ}
    (halpha : 0 ≤ alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogGap delta)
    (hcertificate :
      IsActualMovingCarlsonTwoHeightCertificate alpha C delta gamma) :
    Tendsto (actualMovingCarlsonStripMass alpha delta) atTop (nhds 0) := by
  have hdeltaCoefficient : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 2 ∧
        128 * alpha * delta m ≤ 1 := by
    filter_upwards [hdelta] with m hm
    exact ⟨hm.1, hm.2.1.trans (by norm_num), hm.2.2⟩
  apply tendsto_zero_of_le_carlsonMovingBalancedCoefficientRatio
    halpha hdeltaCoefficient
      (carlsonMovingQuadraticLogEnvelope_admissible hgap)
  · filter_upwards with m
    exact actualMovingCarlsonStripMass_nonneg alpha delta m
  · apply actualMovingCarlsonStripMass_le_quadraticRatio
    · filter_upwards [hdelta] with m hm
      exact ⟨hm.1, hm.2.1⟩
    · exact hcertificate

end PrimeNumberTheorem
