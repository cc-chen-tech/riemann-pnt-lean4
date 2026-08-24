import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonMovingTail

/-!
# Concrete dyadic cuts for the actual cubic two-height tail

The low detector height `Y = x^gammaLow` and the outer contour height
`H = x^alpha` determine dyadic block indices by taking the natural floor of
their base-two logarithms.  Positive height exponents make both cuts cofinal,
and `gammaLow <= alpha` gives the eventual ordering required by a two-height
split.

The final two theorems compose these concrete cuts with the existing
summable-tail result.  Their coefficient scale `x` remains fixed: uniform
control when that coefficient scale also varies is a separate analytic
majorant problem and is not claimed here.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Dyadic block index attached to the polynomial height `x^gamma`. -/
noncomputable def actualCubicDyadicPolynomialCut
    (gamma : ℝ) (m : ℕ) : ℕ :=
  Nat.floor
    (Real.log (carlsonPolynomialHeight gamma (m : ℝ)) / Real.log 2)

/-- Low detector cut attached to `Y = x^gammaLow`. -/
noncomputable def actualCubicLowDyadicCut
    (gammaLow : ℝ) (m : ℕ) : ℕ :=
  actualCubicDyadicPolynomialCut gammaLow m

/-- Outer contour cut attached to `H = x^alpha`. -/
noncomputable def actualCubicOuterDyadicCut
    (alpha : ℝ) (m : ℕ) : ℕ :=
  actualCubicDyadicPolynomialCut alpha m

/-- Every positive polynomial-height exponent produces a cofinal dyadic
block index. -/
theorem tendsto_actualCubicDyadicPolynomialCut_atTop
    {gamma : ℝ} (hgamma : 0 < gamma) :
    Tendsto (actualCubicDyadicPolynomialCut gamma) atTop atTop := by
  have hheight :
      Tendsto
        (fun m : ℕ => carlsonPolynomialHeight gamma (m : ℝ))
        atTop atTop := by
    exact (tendsto_rpow_atTop hgamma).comp tendsto_natCast_atTop_atTop
  have hlogHeight :
      Tendsto
        (fun m : ℕ =>
          Real.log (carlsonPolynomialHeight gamma (m : ℝ)))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hheight
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled :
      Tendsto
        (fun m : ℕ =>
          Real.log (carlsonPolynomialHeight gamma (m : ℝ)) /
            Real.log 2)
        atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      hlogHeight.const_mul_atTop (inv_pos.mpr hlogTwo)
  exact tendsto_nat_floor_atTop.comp hscaled

theorem tendsto_actualCubicLowDyadicCut_atTop
    {gammaLow : ℝ} (hgammaLow : 0 < gammaLow) :
    Tendsto (actualCubicLowDyadicCut gammaLow) atTop atTop := by
  change Tendsto (actualCubicDyadicPolynomialCut gammaLow) atTop atTop
  exact tendsto_actualCubicDyadicPolynomialCut_atTop hgammaLow

theorem tendsto_actualCubicOuterDyadicCut_atTop
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (actualCubicOuterDyadicCut alpha) atTop atTop := by
  change Tendsto (actualCubicDyadicPolynomialCut alpha) atTop atTop
  exact tendsto_actualCubicDyadicPolynomialCut_atTop halpha

/-- If the detector exponent does not exceed the contour exponent, then its
dyadic cut is eventually no larger than the contour cut. -/
theorem eventually_actualCubicLowDyadicCut_le_outer
    {gammaLow alpha : ℝ} (hgammaLowAlpha : gammaLow ≤ alpha) :
    ∀ᶠ m : ℕ in atTop,
      actualCubicLowDyadicCut gammaLow m ≤
        actualCubicOuterDyadicCut alpha m := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hmPos : (0 : ℝ) < (m : ℝ) := zero_lt_one.trans_le hmReal
  have hlowHeightPos :
      0 < carlsonPolynomialHeight gammaLow (m : ℝ) := by
    unfold carlsonPolynomialHeight
    exact Real.rpow_pos_of_pos hmPos _
  have hheight :
      carlsonPolynomialHeight gammaLow (m : ℝ) ≤
        carlsonPolynomialHeight alpha (m : ℝ) := by
    unfold carlsonPolynomialHeight
    exact Real.rpow_le_rpow_of_exponent_le hmReal hgammaLowAlpha
  have hlogHeight :
      Real.log (carlsonPolynomialHeight gammaLow (m : ℝ)) ≤
        Real.log (carlsonPolynomialHeight alpha (m : ℝ)) :=
    Real.log_le_log hlowHeightPos hheight
  unfold actualCubicLowDyadicCut actualCubicOuterDyadicCut
    actualCubicDyadicPolynomialCut
  exact Nat.floor_mono
    ((div_le_div_iff₀ hlogTwo hlogTwo).2
      (mul_le_mul_of_nonneg_right hlogHeight hlogTwo.le))

/-- The concrete low cut sends every fixed-coefficient actual cubic Carlson
tail to zero. -/
theorem CarlsonEventualMajorant.tendsto_actualCubicTail_at_lowDyadicCut_zero
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau gammaLow : ℝ} (hx : 1 ≤ x) (hgammaLow : 0 < gammaLow)
    (S : Finset ℂ) :
    Tendsto
      (fun m : ℕ =>
        actualCubicDyadicStripSquareCapacityExcludingTail
          x sigma tau S (actualCubicLowDyadicCut gammaLow m))
      atTop (nhds 0) := by
  exact
    certificate.tendsto_actualCubicDyadicStripSquareCapacityExcludingTail_comp_zero
      hx S (tendsto_actualCubicLowDyadicCut_atTop hgammaLow)

/-- The concrete outer cut sends every fixed-coefficient actual cubic
Carlson tail to zero. -/
theorem CarlsonEventualMajorant.tendsto_actualCubicTail_at_outerDyadicCut_zero
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau alpha : ℝ} (hx : 1 ≤ x) (halpha : 0 < alpha)
    (S : Finset ℂ) :
    Tendsto
      (fun m : ℕ =>
        actualCubicDyadicStripSquareCapacityExcludingTail
          x sigma tau S (actualCubicOuterDyadicCut alpha m))
      atTop (nhds 0) := by
  exact
    certificate.tendsto_actualCubicDyadicStripSquareCapacityExcludingTail_comp_zero
      hx S (tendsto_actualCubicOuterDyadicCut_atTop halpha)

end PrimeNumberTheorem
