import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonLogPowerRatio

namespace PrimeNumberTheorem

open Filter Topology

/-- The actual moving zeta strip mass is bounded by the honest balanced
log-power ratio once the two pointwise Carlson counts are available. -/
theorem actualMovingCarlsonStripMass_le_logPowerRatio
    {A alpha : ℝ} {delta : ℕ → ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8)
    (hcount :
      IsActualMovingCarlsonTwoHeightCountCertificate
        A alpha delta (carlsonMovingBalancedCut alpha delta)) :
    ∀ᶠ m : ℕ in atTop,
      actualMovingCarlsonStripMass alpha delta m ≤
        carlsonMovingBalancedCoefficientRatio alpha delta
          (carlsonMovingQuadraticLogPowerEnvelope
            (actualMovingCarlsonBalancedPositiveConstant A alpha) delta) m := by
  have hbudget :=
    actualMovingCarlsonTwoHeightBudget_le_pointwiseMajorant
      hdelta hcount
  filter_upwards [eventually_ge_atTop (2 : ℕ), hdelta, hbudget] with
      m hm hdm hbudgetm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (le_trans (by norm_num) hm)
  have hsigma : 0 < 1 - 2 * delta m := by linarith
  have hquarter : delta m < 1 / 4 :=
    hdm.2.trans_lt (by norm_num)
  have hcutAlpha :
      carlsonMovingBalancedCut alpha delta m ≤ alpha := by
    unfold carlsonMovingBalancedCut
    exact
      (carlsonMovingBalancedCut_lt_alpha
        hdm.1 hquarter halpha).le
  have hratio :=
    actualMovingCarlsonTwoHeightPointwiseMajorant_le_logPowerRatio
      hA halpha hm hdm.1 hdm.2
  unfold actualMovingCarlsonStripMass
  exact
    (sum_norm_actualPositiveCarlsonStrip_le_twoHeightBudget
      hmReal hsigma hcutAlpha).trans
        (hbudgetm.trans hratio)

/-- The actual moving zeta strip mass tends to zero under the pointwise
two-height Carlson count certificate and the complete logarithmic gap. -/
theorem tendsto_actualMovingCarlsonStripMass_zero_of_pointwiseCount
    {A alpha : ℝ} {delta : ℕ → ℝ}
    (hA : 0 ≤ A) (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcount :
      IsActualMovingCarlsonTwoHeightCountCertificate
        A alpha delta (carlsonMovingBalancedCut alpha delta)) :
    Tendsto
      (actualMovingCarlsonStripMass alpha delta)
      atTop (nhds 0) := by
  have hratio :=
    tendsto_carlsonMovingQuadraticLogPowerCoefficientRatio_zero
      (C := actualMovingCarlsonBalancedPositiveConstant A alpha)
      halpha.le
      (by
        filter_upwards [hdelta] with m hm
        exact ⟨hm.1, hm.2.1.trans (by norm_num), hm.2.2⟩)
      hgap
  refine squeeze_zero' ?_ ?_ hratio
  · filter_upwards with m
    exact actualMovingCarlsonStripMass_nonneg alpha delta m
  · apply actualMovingCarlsonStripMass_le_logPowerRatio hA halpha
    · filter_upwards [hdelta] with m hm
      exact ⟨hm.1, hm.2.1⟩
    · exact hcount

end PrimeNumberTheorem
