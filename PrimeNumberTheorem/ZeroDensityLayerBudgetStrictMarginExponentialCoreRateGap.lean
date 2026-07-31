import PrimeNumberTheorem.ZeroDensityLayerBudgetNormalizedCofinalLowerWitnessObstruction

/-!
# Strict rate-gap decay for the actual exponential core

The contour and finite-zero terms in the actual strict-margin full-PNT
majorant decay relative to every slower square-root-log exponential scale.
The rate-independent residual is kept explicit rather than silently promoted
from ordinary convergence to normalized convergence.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Square-root-log exponential comparison amplitude. -/
noncomputable def pntSqrtLogExponentialAmplitude
    (rate : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-rate * pntSqrtLog m)

theorem pntSqrtLogExponentialAmplitude_pos (rate : ℝ) (m : ℕ) :
    0 < pntSqrtLogExponentialAmplitude rate m := by
  unfold pntSqrtLogExponentialAmplitude
  exact Real.exp_pos _

/-- The two rate-sensitive terms in the actual strict-margin grid envelope. -/
noncomputable def actualStrictMarginGridExponentialCore
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (C theta b q : ℝ) (m : ℕ) : ℝ :=
  2 *
    (actualStrictMarginContourCoeff grid m +
      actualStrictMarginFiniteZeroCoeff C m) *
    Real.exp
      (-(classicalAdmissibleBalancedRate (theta * b) / q) *
        pntSqrtLog m)

/-- Exact separation of the full majorant into its exponential core and
rate-independent residual. -/
theorem actualStrictMarginGridFullPNTErrorMajorant_eq_core_add_residual
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (C theta b q : ℝ) (m : ℕ) :
    actualStrictMarginGridFullPNTErrorMajorant grid C theta b q m =
      actualStrictMarginGridExponentialCore grid C theta b q m +
        actualStrictMarginRateIndependentResidual m := by
  unfold actualStrictMarginGridFullPNTErrorMajorant
    classicalStrictMarginGridFullBudgetEnvelope
    actualStrictMarginGridExponentialCore
  rfl

/-- A strict gap below the certified target rate absorbs both polynomial
coefficients in the actual contour-plus-finite-zero core. -/
theorem tendsto_actualStrictMarginGridExponentialCore_div_amplitude_zero
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (C : ℝ) {theta b q slowerRate : ℝ}
    (htheta : 0 < theta) (hb : 0 < b) (hq : 0 < q)
    (hslower :
      slowerRate < classicalAdmissibleBalancedRate (theta * b) / q) :
    Tendsto
      (fun m : ℕ =>
        actualStrictMarginGridExponentialCore grid C theta b q m /
          pntSqrtLogExponentialAmplitude slowerRate m)
      atTop (nhds 0) := by
  let targetRate := classicalAdmissibleBalancedRate (theta * b) / q
  have hbalanced : 0 < classicalAdmissibleBalancedRate (theta * b) :=
    classicalAdmissibleBalancedRate_pos (mul_pos htheta hb)
  have htarget : 0 < targetRate := div_pos hbalanced hq
  have hgap : 0 < targetRate - slowerRate := sub_pos.mpr hslower
  have hcontour :=
    (tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      (targetRate - slowerRate) hgap 4).const_mul
        (52 * grid.selection.constant)
  have hfinite :=
    (tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      (targetRate - slowerRate) hgap 2).const_mul
        (18 * C)
  convert hcontour.add hfinite using 1
  · funext m
    have hexp :
        Real.exp (-targetRate * pntSqrtLog m) /
            Real.exp (-slowerRate * pntSqrtLog m) =
          Real.exp (-(targetRate - slowerRate) * pntSqrtLog m) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    unfold actualStrictMarginGridExponentialCore
      pntSqrtLogExponentialAmplitude
      actualStrictMarginContourCoeff actualStrictMarginFiniteZeroCoeff
    change
      (2 *
          (26 * grid.selection.constant * pntSqrtLog m ^ 4 +
            9 * C * pntSqrtLog m ^ 2) *
        Real.exp (-targetRate * pntSqrtLog m)) /
          Real.exp (-slowerRate * pntSqrtLog m) = _
    rw [mul_div_assoc, hexp]
    ring
  · simp

/-- Full normalized decay follows exactly when the explicitly separated
rate-independent residual is negligible on the same slower scale. -/
theorem tendsto_actualStrictMarginGridFullPNTErrorMajorant_div_amplitude_zero
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (C : ℝ) {theta b q slowerRate : ℝ}
    (htheta : 0 < theta) (hb : 0 < b) (hq : 0 < q)
    (hslower :
      slowerRate < classicalAdmissibleBalancedRate (theta * b) / q)
    (hresidual :
      Tendsto
        (fun m : ℕ =>
          actualStrictMarginRateIndependentResidual m /
            pntSqrtLogExponentialAmplitude slowerRate m)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ =>
        actualStrictMarginGridFullPNTErrorMajorant grid C theta b q m /
          pntSqrtLogExponentialAmplitude slowerRate m)
      atTop (nhds 0) := by
  have hcore :=
    tendsto_actualStrictMarginGridExponentialCore_div_amplitude_zero
      grid C htheta hb hq hslower
  convert hcore.add hresidual using 1
  · funext m
    rw [actualStrictMarginGridFullPNTErrorMajorant_eq_core_add_residual]
    ring
  · simp

end PrimeNumberTheorem
