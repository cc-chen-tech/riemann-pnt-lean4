import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedGoodHeightUniqueness

/-!
# Characterization of the optimal selected good height

This module supplies the reverse direction missing from selected-good-height
uniqueness.  For positive polynomial exponents, asymptotic equivalence of two
selected schedules forces equality of their exponents.  Consequently, the
optimal physical-margin certificate is equivalent to asymptotic equivalence
with the actual weighted-balanced good-height schedule.
-/

open Filter

namespace PrimeNumberTheorem

/-- Two selected polynomial good-height schedules with positive exponents have
ratio tending to one exactly when their exponents agree. -/
theorem selectedUniformGoodHeight_ratio_tendsto_one_iff_exponent_eq
    {alpha gamma : ℝ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (selection₁ selection₂ : UniformNaturalPointGoodHeightSelection) :
    Tendsto
        (fun x : ℝ =>
          selectedUniformGoodHeight alpha selection₁ x /
            selectedUniformGoodHeight gamma selection₂ x)
        atTop (nhds 1) ↔
      alpha = gamma := by
  constructor
  · intro hratio
    have hlogRatio :
        Tendsto
            (fun x : ℝ =>
              Real.log
                (selectedUniformGoodHeight alpha selection₁ x /
                  selectedUniformGoodHeight gamma selection₂ x))
            atTop (nhds 0) := by
      simpa [Function.comp_def] using
        ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
          hratio)
    have hsmall :
        Tendsto
            (fun x : ℝ =>
              Real.log
                    (selectedUniformGoodHeight alpha selection₁ x /
                      selectedUniformGoodHeight gamma selection₂ x) /
                Real.log x)
            atTop (nhds 0) :=
      hlogRatio.div_atTop Real.tendsto_log_atTop
    have hsmallDiff :
        Tendsto
            (fun x : ℝ =>
              Real.log (selectedUniformGoodHeight alpha selection₁ x) /
                  Real.log x -
                Real.log (selectedUniformGoodHeight gamma selection₂ x) /
                  Real.log x)
            atTop (nhds 0) := by
      apply hsmall.congr'
      filter_upwards
        [eventually_selectedUniformGoodHeight_mem halpha selection₁,
          eventually_selectedUniformGoodHeight_mem hgamma selection₂,
          eventually_gt_atTop (1 : ℝ)] with x hfirst hsecond hx
      have hfirstPos :
          0 < selectedUniformGoodHeight alpha selection₁ x := by
        have hpower : 1 < x ^ alpha := Real.one_lt_rpow hx halpha
        exact (sub_pos.mpr hpower).trans_le hfirst.1
      have hsecondPos :
          0 < selectedUniformGoodHeight gamma selection₂ x := by
        have hpower : 1 < x ^ gamma := Real.one_lt_rpow hx hgamma
        exact (sub_pos.mpr hpower).trans_le hsecond.1
      rw [Real.log_div hfirstPos.ne' hsecondPos.ne']
      ring
    have hdiff :
        Tendsto
            (fun x : ℝ =>
              Real.log (selectedUniformGoodHeight alpha selection₁ x) /
                  Real.log x -
                Real.log (selectedUniformGoodHeight gamma selection₂ x) /
                  Real.log x)
            atTop (nhds (alpha - gamma)) :=
      (selectedUniformGoodHeight_log_div_log_tendsto halpha selection₁).sub
        (selectedUniformGoodHeight_log_div_log_tendsto hgamma selection₂)
    exact sub_eq_zero.mp (tendsto_nhds_unique hdiff hsmallDiff)
  · rintro rfl
    exact
      selectedUniformGoodHeight_div_selectedUniformGoodHeight_tendsto_one
        halpha selection₁ selection₂

/-- A positive candidate selected schedule realizes the optimal physical margin
exactly when it is asymptotic to the actual weighted-balanced selected
good-height schedule. -/
theorem
    actualSelectedHeightFiniteStrip_optimalMarginCertificate_iff_goodHeightRatio_tendsto_one
    {beta alpha : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (halpha : 0 < alpha)
    (candidateSelection referenceSelection :
      UniformNaturalPointGoodHeightSelection) :
    ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha
        (actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau) ↔
      Tendsto
        (fun x : ℝ =>
          selectedUniformGoodHeight alpha candidateSelection x /
            actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau referenceSelection x)
        atTop (nhds 1) := by
  constructor
  · intro certificate
    exact
      selectedUniformGoodHeight_optimalMargin_div_actualWeightedBalanced_tendsto_one
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
        candidateSelection referenceSelection certificate
  · intro hratio
    have hspec :=
      actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
    have hoptimalPos :
        0 <
          actualSelectedHeightFiniteStripWeightedBalancedExponent
            beta sigma tau :=
      hspec.2.1
    have hratio' :
        Tendsto
            (fun x : ℝ =>
              selectedUniformGoodHeight alpha candidateSelection x /
                selectedUniformGoodHeight
                  (actualSelectedHeightFiniteStripWeightedBalancedExponent
                    beta sigma tau)
                  referenceSelection x)
            atTop (nhds 1) := by
      simpa [actualSelectedHeightFiniteStripWeightedBalancedGoodHeight] using
        hratio
    have halphaEq :
        alpha =
          actualSelectedHeightFiniteStripWeightedBalancedExponent
            beta sigma tau :=
      (selectedUniformGoodHeight_ratio_tendsto_one_iff_exponent_eq
        halpha hoptimalPos candidateSelection referenceSelection).mp hratio'
    exact
      (actualSelectedHeightFiniteStrip_optimalMarginCertificate_iff
        sigma tau hsigma hsigmaOne).2 halphaEq

end PrimeNumberTheorem
