import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedExponentUniqueness
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightOptimality

/-!
# Asymptotic uniqueness of the weighted-balanced good height

The optimal polynomial exponent is unique.  The actual good-height selector
still makes a bounded additive choice inside a unit interval, so literal
pointwise uniqueness is neither expected nor useful.

This module proves the correct height-level rigidity statement.  Any two
uniform good-height selectors at the same positive exponent have ratio tending
to one.  Consequently every selected schedule carrying an optimal-margin
certificate is asymptotic to the actual weighted-balanced schedule, even when
the two schedules use different global selectors.
-/

open Filter Topology

noncomputable section

namespace PrimeNumberTheorem

/-- Uniform good-height selection is asymptotically independent of the chosen
global selector at a fixed positive polynomial exponent. -/
theorem selectedUniformGoodHeight_div_selectedUniformGoodHeight_tendsto_one
    {alpha : ℝ}
    (halpha : 0 < alpha)
    (selection₁ selection₂ : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun x : ℝ =>
        selectedUniformGoodHeight alpha selection₁ x /
          selectedUniformGoodHeight alpha selection₂ x)
      atTop
      (nhds 1) := by
  have h₁ :=
    selectedUniformGoodHeight_div_rpow_tendsto_one halpha selection₁
  have h₂ :=
    selectedUniformGoodHeight_div_rpow_tendsto_one halpha selection₂
  have hratio :=
    h₁.div h₂ (by norm_num : (1 : ℝ) ≠ 0)
  have hratioOne :
      Tendsto
        ((fun x : ℝ =>
            selectedUniformGoodHeight alpha selection₁ x / x ^ alpha) /
          fun x : ℝ =>
            selectedUniformGoodHeight alpha selection₂ x / x ^ alpha)
        atTop
        (nhds 1) := by
    simpa using hratio
  apply hratioOne.congr'
  filter_upwards
      [eventually_selectedUniformGoodHeight_mem halpha selection₂,
        eventually_gt_atTop (1 : ℝ)] with x hheight hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hpowerPos : 0 < x ^ alpha :=
    Real.rpow_pos_of_pos hxpos _
  have hpowerOne : 1 < x ^ alpha :=
    Real.one_lt_rpow hx halpha
  have hheightPos :
      0 < selectedUniformGoodHeight alpha selection₂ x :=
    (sub_pos.mpr hpowerOne).trans_le hheight.1
  change
    (selectedUniformGoodHeight alpha selection₁ x / x ^ alpha) /
        (selectedUniformGoodHeight alpha selection₂ x / x ^ alpha) =
      selectedUniformGoodHeight alpha selection₁ x /
        selectedUniformGoodHeight alpha selection₂ x
  field_simp [hpowerPos.ne', hheightPos.ne']

/-- Every selected uniform good-height schedule carrying the optimal common
physical margin is asymptotic to the actual weighted-balanced schedule.

The candidate and reference schedules may use different global selectors.
-/
theorem
    selectedUniformGoodHeight_optimalMargin_div_actualWeightedBalanced_tendsto_one
    {beta alpha : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (candidateSelection referenceSelection :
      UniformNaturalPointGoodHeightSelection)
    (certificate :
      ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha
        (actualSelectedHeightFiniteStripOptimalPhysicalMargin
          beta sigma tau)) :
    Tendsto
      (fun x : ℝ =>
        selectedUniformGoodHeight alpha candidateSelection x /
          actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau referenceSelection x)
      atTop
      (nhds 1) := by
  have halpha :
      alpha =
        actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_unique
      sigma tau hsigma hsigmaOne certificate
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have hoptimalPos :
      0 <
        actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau :=
    hspec.2.1
  subst alpha
  simpa [actualSelectedHeightFiniteStripWeightedBalancedGoodHeight] using
    selectedUniformGoodHeight_div_selectedUniformGoodHeight_tendsto_one
      hoptimalPos candidateSelection referenceSelection

end PrimeNumberTheorem
