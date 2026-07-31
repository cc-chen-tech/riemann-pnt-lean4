import PrimeNumberTheorem.ZeroDensityLayerBudgetActualStrictMarginFiniteZeroMajorant

/-!
# Actual strict-margin finite-grid full PNT envelope

The actual finite zero sum and actual contour remainder are controlled at the
same certified grid height. Their competing rates are then optimized by the
finite-grid `1 / q` transfer from the strict-margin module.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Polynomial coefficient of the contour exponential. -/
noncomputable def actualStrictMarginContourCoeff
    (grid : ActualPintzCarlsonGoodHeightRateGrid) (m : ℕ) : ℝ :=
  26 * grid.selection.constant * pntSqrtLog m ^ 4

/-- Polynomial coefficient of the finite-zero exponential. -/
noncomputable def actualStrictMarginFiniteZeroCoeff
    (C : ℝ) (m : ℕ) : ℝ :=
  9 * C * pntSqrtLog m ^ 2

/-- Terms independent of the selected grid rate. -/
noncomputable def actualStrictMarginRateIndependentResidual
    (m : ℕ) : ℝ :=
  2 * cofinalPNTZeroDepthTailConstant * pntSqrtLog m / (m : ℝ) +
    classicalClosedLogRelativeMajorant m +
    |actualPNTClosedRealAxisRelativeTerm (m : ℝ)|

/-- Complete same-height analytic majorant for one actual grid rate. -/
noncomputable def actualStrictMarginRateFullPNTErrorMajorant
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (C theta b k : ℝ) (m : ℕ) : ℝ :=
  classicalStrictMarginRateFullBudgetEnvelope
    (actualStrictMarginContourCoeff grid)
    (actualStrictMarginFiniteZeroCoeff C)
    actualStrictMarginRateIndependentResidual theta b k m

/-- Closed `1 / q` majorant after finite-grid rate optimization. -/
noncomputable def actualStrictMarginGridFullPNTErrorMajorant
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (C theta b q : ℝ) (m : ℕ) : ℝ :=
  classicalStrictMarginGridFullBudgetEnvelope
    (actualStrictMarginContourCoeff grid)
    (actualStrictMarginFiniteZeroCoeff C)
    actualStrictMarginRateIndependentResidual theta b q m

theorem actualStrictMarginContourCoeff_nonneg
    (grid : ActualPintzCarlsonGoodHeightRateGrid) (m : ℕ) :
    0 ≤ actualStrictMarginContourCoeff grid m := by
  unfold actualStrictMarginContourCoeff
  exact mul_nonneg
    (mul_nonneg (by norm_num) grid.selection.constant_nonneg)
    (by positivity)

theorem actualStrictMarginFiniteZeroCoeff_nonneg
    {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    0 ≤ actualStrictMarginFiniteZeroCoeff C m := by
  unfold actualStrictMarginFiniteZeroCoeff
  positivity

/-- The exact selected contour upper bound reduces to its closed-form
exponential plus rate-independent tail. -/
theorem eventually_actualPintzCarlsonRateNaturalRemainderUpperBound_le_closedForm
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {k : ℝ} (hk : k ∈ grid.rates) (hkOne : k ≤ 1) :
    ∀ᶠ m : ℕ in atTop,
      actualPintzCarlsonRateNaturalRemainderUpperBound grid k m ≤
        cofinalPNTZeroDepthRelativeRemainderMajorant
            grid.selection.constant k m +
          classicalClosedLogRelativeMajorant m := by
  have hkPos : 0 < k := grid.rates_pos k hk
  filter_upwards
      [eventually_actualPintzCarlsonRateCandidateHeight_mem grid hk,
        eventually_ge_atTop (3 : ℕ),
        tendsto_pntSqrtLog_atTop.eventually
          (eventually_ge_atTop (max 1 (Real.log 6 / k)))]
      with m hmHeight hm hmScale
  have hcontour :=
    cofinalPNTFormulaRemainderBound_zero_relative_le_majorant
      grid.selection.constant_nonneg hkPos hkOne hm hmScale hmHeight
  unfold actualPintzCarlsonRateNaturalRemainderUpperBound
  exact add_le_add hcontour le_rfl

/-- At every fixed certified grid rate, the real relative PNT error is
eventually bounded by the concrete same-height strict-margin envelope. -/
theorem eventually_abs_relativeChebyshevPsi0Error_le_actualStrictMarginRateMajorant
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {b C theta k : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C)
    (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hk : k ∈ grid.rates) (hkOne : k ≤ 1)
    (hzeros : ∀ x T : ℝ, 1 < x → 4 ≤ T →
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        C * x ^ (1 - b / Real.log (T + 6)) *
          (1 + Real.log (T + 6)) ^ 2) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        actualStrictMarginRateFullPNTErrorMajorant grid C theta b k m := by
  let H : ℝ → ℝ := actualPintzCarlsonRateCandidateHeight grid k
  have hfinite :=
    eventually_actualPintzCarlsonRate_finiteZeroRelative_le_strictMarginMajorant
      grid hb hC htheta hthetaOne hk hkOne hzeros
  have hremainder :=
    eventually_abs_actualPintzCarlsonRate_actualRemainder_le grid hk
  have hremainderClosed :=
    eventually_actualPintzCarlsonRateNaturalRemainderUpperBound_le_closedForm
      grid hk hkOne
  filter_upwards [hfinite, hremainder, hremainderClosed,
      eventually_ge_atTop (3 : ℕ)] with m hfiniteM hremainderM
      hremainderClosedM hm
  have hmPos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hm)
  have hfiniteRe :
      |(dynamicFinitePNTZeroSum H (m : ℝ)).re| ≤
        classicalStrictMarginFiniteZeroRelativeMajorant C theta b k m := by
    calc
      |(dynamicFinitePNTZeroSum H (m : ℝ)).re| ≤
          ‖dynamicFinitePNTZeroSum H (m : ℝ)‖ := Complex.abs_re_le_norm _
      _ = ‖finiteNontrivialZeroSumWithMultiplicity (m : ℝ) (H (m : ℝ))‖ /
          (m : ℝ) := by
        unfold dynamicFinitePNTZeroSum
        exact
          norm_sum_pntRelativeZeroContribution_eq_norm_finiteNontrivialZeroSumWithMultiplicity_div
            hmPos (H (m : ℝ))
      _ ≤ classicalStrictMarginFiniteZeroRelativeMajorant C theta b k m :=
        hfiniteM
  rw [relativeChebyshevPsi0Error_eq_dynamicFinite_add_closed_add_remainder
    H (m : ℝ)]
  calc
    |(dynamicFinitePNTZeroSum H (m : ℝ)).re +
        (actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ))| ≤
      |(dynamicFinitePNTZeroSum H (m : ℝ)).re| +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          |actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)|) := by
        exact (abs_add_le _ _).trans
          (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ classicalStrictMarginFiniteZeroRelativeMajorant C theta b k m +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          actualPintzCarlsonRateNaturalRemainderUpperBound grid k m) :=
      add_le_add hfiniteRe (add_le_add le_rfl hremainderM)
    _ ≤ classicalStrictMarginFiniteZeroRelativeMajorant C theta b k m +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          (cofinalPNTZeroDepthRelativeRemainderMajorant
              grid.selection.constant k m +
            classicalClosedLogRelativeMajorant m)) :=
      add_le_add le_rfl (add_le_add le_rfl hremainderClosedM)
    _ = actualStrictMarginRateFullPNTErrorMajorant grid C theta b k m := by
      unfold actualStrictMarginRateFullPNTErrorMajorant
        classicalStrictMarginRateFullBudgetEnvelope
        classicalStrictMarginFiniteZeroRelativeMajorant
        actualStrictMarginContourCoeff actualStrictMarginFiniteZeroCoeff
        actualStrictMarginRateIndependentResidual
        cofinalPNTZeroDepthRelativeRemainderMajorant
      ring

/-- The actual real relative PNT error inherits the explicit finite-grid
`1 / q` strict-margin exponent. -/
theorem eventually_abs_relativeChebyshevPsi0Error_le_actualStrictMarginGridMajorant
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {b C theta q witness : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C)
    (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hratesOne : ∀ k ∈ grid.rates, k ≤ 1)
    (hwitness : witness ∈ grid.rates)
    (hlower : classicalAdmissibleBalancedRate (theta * b) / q ≤ witness)
    (hupper : witness ≤ classicalAdmissibleBalancedRate (theta * b))
    (hzeros : ∀ x T : ℝ, 1 < x → 4 ≤ T →
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        C * x ^ (1 - b / Real.log (T + 6)) *
          (1 + Real.log (T + 6)) ^ 2) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        actualStrictMarginGridFullPNTErrorMajorant grid C theta b q m := by
  let k := classicalBalancedEnvelopeGridOptimalRate (theta * b) grid
  have hk : k ∈ grid.rates :=
    classicalBalancedEnvelopeGridOptimalRate_mem (theta * b) grid
  have hactual :=
    eventually_abs_relativeChebyshevPsi0Error_le_actualStrictMarginRateMajorant
      grid hb hC htheta hthetaOne hk (hratesOne k hk) hzeros
  filter_upwards [hactual] with m hm
  exact hm.trans (by
    simpa [actualStrictMarginRateFullPNTErrorMajorant,
      actualStrictMarginGridFullPNTErrorMajorant, k] using
      classicalStrictMarginRateFullBudgetEnvelope_le_grid
        grid (actualStrictMarginContourCoeff grid)
          (actualStrictMarginFiniteZeroCoeff C)
          actualStrictMarginRateIndependentResidual m htheta hb hwitness
          hlower hupper (actualStrictMarginContourCoeff_nonneg grid m)
          (actualStrictMarginFiniteZeroCoeff_nonneg hC m))

end PrimeNumberTheorem
