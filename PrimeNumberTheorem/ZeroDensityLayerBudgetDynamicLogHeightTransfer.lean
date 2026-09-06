import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightOptimality
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonLogAbsorption

/-!
# Dynamic logarithmic-height transfer

Carlson strip arithmetic is usually evaluated at the exact polynomial height
`x ^ alpha`.  This module shows that exact equality is unnecessary.  Any
positive-scale height whose logarithmic growth tends to `alpha` has the same
strict exponent transfer: if the limiting normalized exponent is negative,
the resulting exponential majorant, including a fourth logarithmic power,
tends to zero.

The selected explicit-formula good heights therefore inherit every strict
Carlson strip margin from their polynomial reference exponent.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Exponential strip majorant associated with a genuinely dynamic height.
The constants `p` and `q` encode respectively the base power and the
height-density slope. -/
noncomputable def dynamicLogHeightMajorant
    (height : ℝ → ℝ) (p q x : ℝ) : ℝ :=
  Real.exp
      (p * Real.log x + q * Real.log (height x)) *
    Real.log x ^ (4 : ℕ)

/-- A negative limiting logarithmic exponent absorbs the fourth logarithmic
power for an arbitrary dynamic height. -/
theorem tendsto_dynamicLogHeightMajorant_zero_of_normalizedExponent
    {height : ℝ → ℝ} {p q exponent : ℝ}
    (hnormalized :
      Tendsto
        (fun x : ℝ =>
          (p * Real.log x + q * Real.log (height x)) /
            Real.log x)
        atTop (nhds exponent))
    (hexponent : exponent < 0) :
    Tendsto
      (dynamicLogHeightMajorant height p q)
      atTop (nhds 0) := by
  have hnormalizedUpper :
      ∀ᶠ x : ℝ in atTop,
        (p * Real.log x + q * Real.log (height x)) /
            Real.log x <
          exponent / 2 :=
    (tendsto_order.1 hnormalized).2 _ (by linarith)
  have hepsilon : 0 < -exponent / 4 := by linarith
  have hstrict : exponent / 2 + (-exponent / 4) < 0 := by
    linarith
  have hupper :
      Tendsto
        (fun x : ℝ => x ^ (exponent / 2) * Real.log x ^ (4 : ℕ))
        atTop (nhds 0) :=
    tendsto_rpow_mul_log_four_atTop_nhds_zero hepsilon hstrict
  have hdominated :
      ∀ᶠ x : ℝ in atTop,
        dynamicLogHeightMajorant height p q x ≤
          x ^ (exponent / 2) * Real.log x ^ (4 : ℕ) := by
    filter_upwards
      [hnormalizedUpper, eventually_gt_atTop (1 : ℝ)] with x hxNormalized hx
    have hlogPos : 0 < Real.log x := Real.log_pos hx
    have hlogNe : Real.log x ≠ 0 := hlogPos.ne'
    have hexponentBound :
        p * Real.log x + q * Real.log (height x) ≤
          (exponent / 2) * Real.log x := by
      calc
        p * Real.log x + q * Real.log (height x) =
            ((p * Real.log x + q * Real.log (height x)) /
                Real.log x) *
              Real.log x := by
                field_simp [hlogNe]
        _ ≤ (exponent / 2) * Real.log x :=
          (mul_lt_mul_of_pos_right hxNormalized hlogPos).le
    unfold dynamicLogHeightMajorant
    calc
      Real.exp
            (p * Real.log x + q * Real.log (height x)) *
          Real.log x ^ (4 : ℕ)
          ≤
        Real.exp ((exponent / 2) * Real.log x) *
          Real.log x ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr hexponentBound) (by positivity)
      _ =
          x ^ (exponent / 2) * Real.log x ^ (4 : ℕ) := by
        rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hx)]
        congr 2
        ring
  exact
    squeeze_zero'
      (Filter.Eventually.of_forall fun x => by
        unfold dynamicLogHeightMajorant
        positivity)
      hdominated hupper

/-- Logarithmic height growth converts the normalized dynamic exponent to the
linear value `p + q * alpha`. -/
theorem tendsto_dynamicLogHeightMajorant_zero_of_logGrowth
    {height : ℝ → ℝ} {alpha p q : ℝ}
    (hlogGrowth :
      Tendsto
        (fun x : ℝ => Real.log (height x) / Real.log x)
        atTop (nhds alpha))
    (hmargin : p + q * alpha < 0) :
    Tendsto
      (dynamicLogHeightMajorant height p q)
      atTop (nhds 0) := by
  apply
    tendsto_dynamicLogHeightMajorant_zero_of_normalizedExponent
      (exponent := p + q * alpha) _ hmargin
  have hlinear :
      Tendsto
        (fun x : ℝ =>
          p + q * (Real.log (height x) / Real.log x))
        atTop (nhds (p + q * alpha)) :=
    (hlogGrowth.const_mul q).const_add p
  apply hlinear.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlogNe : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp [hlogNe]

/-- A selected good height immediately below `x ^ alpha` satisfies every
strict dynamic logarithmic-height margin valid at exponent `alpha`. -/
theorem tendsto_selectedUniformGoodHeight_dynamicLogHeightMajorant_zero
    {alpha p q : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hmargin : p + q * alpha < 0) :
    Tendsto
      (dynamicLogHeightMajorant
        (selectedUniformGoodHeight alpha selection) p q)
      atTop (nhds 0) :=
  tendsto_dynamicLogHeightMajorant_zero_of_logGrowth
    (selectedUniformGoodHeight_log_div_log_tendsto halpha selection)
    hmargin

/-- Carlson strip specialization: `tau - beta` is the target-normalized base
power and `actualSelectedHeightStripCarlsonSlope sigma` is the height slope. -/
theorem
    tendsto_selectedUniformGoodHeight_carlsonStripLogMajorant_zero
    {beta sigma tau alpha : ℝ} (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hmargin :
      tau - beta +
          actualSelectedHeightStripCarlsonSlope sigma * alpha <
        0) :
    Tendsto
      (dynamicLogHeightMajorant
        (selectedUniformGoodHeight alpha selection)
        (tau - beta) (actualSelectedHeightStripCarlsonSlope sigma))
      atTop (nhds 0) :=
  tendsto_selectedUniformGoodHeight_dynamicLogHeightMajorant_zero
    halpha selection hmargin

/-- At the actual weighted-balanced selected height, every certified finite
Carlson strip has a vanishing dynamic logarithmic majorant.  The strict margin
is extracted automatically from the optimizer specification. -/
theorem
    tendsto_actualWeightedBalancedGoodHeight_carlsonStripLogMajorant_zero
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (i : Fin (n + 1)) :
    Tendsto
      (dynamicLogHeightMajorant
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)
        (tau i - beta)
        (actualSelectedHeightStripCarlsonSlope (sigma i)))
      atTop (nhds 0) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have halpha : 0 < alpha := by
    simpa [alpha] using hspec.2.1
  have hraw :=
    hspec.2.2.2.2 i
  have hmargin :
      tau i - beta +
          actualSelectedHeightStripCarlsonSlope (sigma i) * alpha <
        0 := by
    rw [show
      tau i - beta +
            actualSelectedHeightStripCarlsonSlope (sigma i) * alpha =
          targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) by
        simp [targetAmplitudeStripEndpointExponent,
          carlsonClassicalPolynomialDensityExponent,
          carlsonPolynomialHeightDensityExponent,
          actualSelectedHeightStripCarlsonSlope]
        ring]
    simpa [alpha] using hraw
  change
    Tendsto
      (dynamicLogHeightMajorant
        (selectedUniformGoodHeight alpha selection)
        (tau i - beta)
        (actualSelectedHeightStripCarlsonSlope (sigma i)))
      atTop (nhds 0)
  exact tendsto_selectedUniformGoodHeight_carlsonStripLogMajorant_zero
    halpha selection hmargin

/-- Weighted finite aggregation of dynamic Carlson strip majorants.  Fixed
strip constants may encode density, kernel, or multiplicity coefficients. -/
noncomputable def dynamicFiniteStripLogMajorant
    {n : ℕ} (height : ℝ → ℝ) (beta : ℝ)
    (sigma tau coefficient : Fin (n + 1) → ℝ)
    (x : ℝ) : ℝ :=
  ∑ i,
    coefficient i *
      dynamicLogHeightMajorant height
        (tau i - beta)
        (actualSelectedHeightStripCarlsonSlope (sigma i)) x

/-- Every strict strip margin survives finite weighted aggregation along an
arbitrary height with logarithmic growth exponent `alpha`. -/
theorem tendsto_dynamicFiniteStripLogMajorant_zero_of_logGrowth
    {n : ℕ} {height : ℝ → ℝ} {beta alpha : ℝ}
    (sigma tau coefficient : Fin (n + 1) → ℝ)
    (hlogGrowth :
      Tendsto
        (fun x : ℝ => Real.log (height x) / Real.log x)
        atTop (nhds alpha))
    (hmargin :
      ∀ i,
        tau i - beta +
            actualSelectedHeightStripCarlsonSlope (sigma i) * alpha <
          0) :
    Tendsto
      (dynamicFiniteStripLogMajorant
        height beta sigma tau coefficient)
      atTop (nhds 0) := by
  unfold dynamicFiniteStripLogMajorant
  simpa only [mul_zero, Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ fun i _ =>
      (tendsto_dynamicLogHeightMajorant_zero_of_logGrowth
        hlogGrowth (hmargin i)).const_mul (coefficient i)

/-- The weighted-balanced optimizer automatically makes the complete finite
weighted dynamic strip majorant tend to zero at the actual selected good
height. -/
theorem
    tendsto_actualWeightedBalancedGoodHeight_dynamicFiniteStripLogMajorant_zero
    {beta : ℝ} {n : ℕ}
    (sigma tau coefficient : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (dynamicFiniteStripLogMajorant
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)
        beta sigma tau coefficient)
      atTop (nhds 0) := by
  unfold dynamicFiniteStripLogMajorant
  simpa only [mul_zero, Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ fun i _ =>
      (tendsto_actualWeightedBalancedGoodHeight_carlsonStripLogMajorant_zero
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection i).const_mul
          (coefficient i)

end PrimeNumberTheorem
