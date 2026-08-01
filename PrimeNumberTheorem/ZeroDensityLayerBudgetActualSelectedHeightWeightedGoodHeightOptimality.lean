import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightNaturalTransfer

/-!
# Asymptotic optimality of the selected weighted good height

A selected good height lies in the unit interval immediately below its raw
polynomial scale.  For every positive exponent this additive perturbation is
asymptotically invisible, both multiplicatively and on the logarithmic growth
scale.

Specializing to the slope-weighted balanced exponent proves that the actual
height used simultaneously by Carlson density and the explicit formula has
the optimizer's certified growth exponent.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- A uniform good height selected immediately below `x ^ alpha` is
asymptotic to that polynomial scale. -/
theorem selectedUniformGoodHeight_div_rpow_tendsto_one
    {alpha : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun x : ℝ =>
        selectedUniformGoodHeight alpha selection x / x ^ alpha)
      atTop (nhds 1) := by
  have hpower :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hinv :
      Tendsto (fun x : ℝ => (x ^ alpha)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hpower
  have hheight :=
    eventually_selectedUniformGoodHeight_mem halpha selection
  have hgap :
      Tendsto
        (fun x : ℝ =>
          1 - selectedUniformGoodHeight alpha selection x / x ^ alpha)
        atTop (nhds 0) := by
    refine squeeze_zero' (g := fun x : ℝ => 1 / x ^ alpha) ?_ ?_ ?_
    · filter_upwards [hheight, eventually_gt_atTop (1 : ℝ)] with x hH hx
      have hPpos : 0 < x ^ alpha := Real.rpow_pos_of_pos (by linarith) _
      exact sub_nonneg.mpr
        ((div_le_iff₀ hPpos).2 (by simpa using hH.2))
    · filter_upwards [hheight, eventually_gt_atTop (1 : ℝ)] with x hH hx
      have hPpos : 0 < x ^ alpha := Real.rpow_pos_of_pos (by linarith) _
      have hdivLower :
          1 - 1 / x ^ alpha ≤
            selectedUniformGoodHeight alpha selection x / x ^ alpha := by
        calc
          1 - 1 / x ^ alpha =
              (x ^ alpha - 1) / x ^ alpha := by
                field_simp [hPpos.ne']
          _ ≤ selectedUniformGoodHeight alpha selection x / x ^ alpha :=
            (div_le_div_iff_of_pos_right hPpos).2 hH.1
      linarith
    · simpa [one_div] using hinv
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using
    (hone.sub hgap)

/-- The logarithmic growth exponent of a selected polynomial good height is
the underlying exponent `alpha`. -/
theorem selectedUniformGoodHeight_log_div_log_tendsto
    {alpha : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun x : ℝ =>
        Real.log (selectedUniformGoodHeight alpha selection x) /
          Real.log x)
      atTop (nhds alpha) := by
  have hratio :=
    selectedUniformGoodHeight_div_rpow_tendsto_one halpha selection
  have hlogRatio :
      Tendsto
        (fun x : ℝ =>
          Real.log
            (selectedUniformGoodHeight alpha selection x / x ^ alpha))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        hratio)
  have hsmall :
      Tendsto
        (fun x : ℝ =>
          Real.log
              (selectedUniformGoodHeight alpha selection x / x ^ alpha) /
            Real.log x)
        atTop (nhds 0) :=
    hlogRatio.div_atTop Real.tendsto_log_atTop
  have hsum :
      Tendsto
        (fun x : ℝ =>
          Real.log
              (selectedUniformGoodHeight alpha selection x / x ^ alpha) /
              Real.log x +
            alpha)
        atTop (nhds alpha) := by
    simpa using hsmall.add
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => alpha) atTop (nhds alpha))
  apply hsum.congr'
  filter_upwards
      [eventually_selectedUniformGoodHeight_mem halpha selection,
        eventually_gt_atTop (1 : ℝ)] with x hH hx
  have hxpos : 0 < x := by linarith
  have hPpos : 0 < x ^ alpha := Real.rpow_pos_of_pos hxpos _
  have hPone : 1 < x ^ alpha := Real.one_lt_rpow hx halpha
  have hHpos :
      0 < selectedUniformGoodHeight alpha selection x :=
    (sub_pos.mpr hPone).trans_le hH.1
  rw [Real.log_div hHpos.ne' hPpos.ne', Real.log_rpow hxpos alpha]
  field_simp [ne_of_gt (Real.log_pos hx)]
  ring

/-- The actual weighted balanced good height is asymptotic to its certified
optimal raw polynomial scale. -/
theorem
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_div_optimalScale_tendsto_one
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun x : ℝ =>
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x /
          x ^ actualSelectedHeightFiniteStripWeightedBalancedExponent
            beta sigma tau)
      atTop (nhds 1) := by
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  simpa [actualSelectedHeightFiniteStripWeightedBalancedGoodHeight] using
    selectedUniformGoodHeight_div_rpow_tendsto_one hspec.2.1 selection

/-- The actual selected good height realizes the slope-weighted optimizer's
logarithmic growth exponent. -/
theorem
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_logGrowth_tendsto_optimalExponent
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun x : ℝ =>
        Real.log
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection x) /
          Real.log x)
      atTop
      (nhds
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau)) := by
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  simpa [actualSelectedHeightFiniteStripWeightedBalancedGoodHeight] using
    selectedUniformGoodHeight_log_div_log_tendsto hspec.2.1 selection

end PrimeNumberTheorem
