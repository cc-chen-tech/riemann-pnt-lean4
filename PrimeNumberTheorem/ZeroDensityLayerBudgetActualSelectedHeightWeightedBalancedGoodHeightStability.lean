import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedGoodHeightCharacterization
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedExponentStability

/-!
# Quantitative stability of the actual selected good height

The exponent difference between two positive polynomial selected-height
schedules is exactly the limiting logarithmic distortion of their actual
heights.  Combining this identity with the finite-strip near-optimality theorem
turns an abstract physical-margin certificate into a quantitative statement
about the selected truncation height itself.
-/

open Filter

namespace PrimeNumberTheorem

/-- The normalized logarithm of the ratio of two positive-exponent selected
good-height schedules tends to the difference of their exponents. -/
theorem selectedUniformGoodHeight_log_ratio_div_log_tendsto
    {alpha gamma : ℝ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (selection₁ selection₂ : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun x : ℝ =>
        Real.log
              (selectedUniformGoodHeight alpha selection₁ x /
                selectedUniformGoodHeight gamma selection₂ x) /
          Real.log x)
      atTop (nhds (alpha - gamma)) := by
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
  apply hdiff.congr'
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

/-- Relative to the actual weighted-balanced schedule, the limiting
logarithmic height distortion is the candidate exponent minus the unique
weighted-balanced exponent. -/
theorem
    selectedUniformGoodHeight_log_ratio_actualWeightedBalanced_div_log_tendsto
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
    Tendsto
      (fun x : ℝ =>
        Real.log
              (selectedUniformGoodHeight alpha candidateSelection x /
                actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                  beta sigma tau referenceSelection x) /
          Real.log x)
      atTop
      (nhds
        (alpha -
          actualSelectedHeightFiniteStripWeightedBalancedExponent
            beta sigma tau)) := by
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have hoptimalPos :
      0 <
        actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau :=
    hspec.2.1
  simpa [actualSelectedHeightFiniteStripWeightedBalancedGoodHeight] using
    selectedUniformGoodHeight_log_ratio_div_log_tendsto
      halpha hoptimalPos candidateSelection referenceSelection

/-- A near-optimal physical-margin certificate bounds the actual asymptotic
logarithmic distortion of the candidate selected height.  The upper bound is
weighted by the Carlson slope of a bottleneck strip. -/
theorem
    exists_bottleneck_nearOptimalGoodHeight_logRatio_limit_bounds
    {beta alpha delta epsilon : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (halpha : 0 < alpha)
    (hnear :
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau -
          epsilon ≤
        delta)
    (certificate :
      ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha delta)
    (candidateSelection referenceSelection :
      UniformNaturalPointGoodHeightSelection) :
    ∃ i d,
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau =
          actualSelectedHeightStripBalancedPhysicalMargin
            beta (sigma i) (tau i) ∧
        -epsilon ≤ d ∧
        actualSelectedHeightStripCarlsonSlope (sigma i) * d ≤ epsilon ∧
        Tendsto
          (fun x : ℝ =>
            Real.log
                  (selectedUniformGoodHeight alpha candidateSelection x /
                    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                      beta sigma tau referenceSelection x) /
              Real.log x)
          atTop (nhds d) := by
  obtain ⟨i, hi, hlower, hscaled⟩ :=
    exists_bottleneck_nearOptimalExponent_bounds
      sigma tau hsigma hsigmaOne hnear certificate
  let d :=
    alpha -
      actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  refine ⟨i, d, hi, ?_, ?_, ?_⟩
  · dsimp [d]
    linarith
  · simpa [d] using hscaled
  · simpa [d] using
      selectedUniformGoodHeight_log_ratio_actualWeightedBalanced_div_log_tendsto
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold halpha
        candidateSelection referenceSelection

end PrimeNumberTheorem
