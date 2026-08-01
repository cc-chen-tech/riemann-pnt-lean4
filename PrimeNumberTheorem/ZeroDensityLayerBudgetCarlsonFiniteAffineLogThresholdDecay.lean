import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffineAdapter
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffinePowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteAffineLogPowerTransfer

/-!
# Carlson finite-strip logarithmic decay at the optimized height

This module specializes the finite affine fourth-logarithmic-power transfer
to Carlson's classical density exponent.  It keeps the weighted-balanced
height exponent already used by the actual PNT chain, exposes the existing
optimal physical margin in the pointwise common envelope, and derives decay
directly from the standard strip-endpoint threshold conditions.

Thus Carlson's `(log x)^4` loss does not require a different truncation
height: every positive optimized affine margin absorbs it automatically.
-/

noncomputable section

namespace PrimeNumberTheorem

open Filter

/-- Carlson's finite power-log majorant at the automatically balanced
truncation exponent. -/
def carlsonFiniteAffineBalancedLogPowerMajorant
    {n : ℕ} (contourCoeff : ℝ)
    (stripCoeff : Fin (n + 1) → ℝ)
    (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ)
    (x : ℝ) : ℝ :=
  finiteAffineDensityLogPowerMajorant
    contourCoeff stripCoeff
    (carlsonAffineDensityFloor beta)
    (finiteAffineBalancedExponent
      (carlsonAffineDensityFloor beta)
      (carlsonAffineDensityCeiling beta tau)
      (carlsonAffineDensitySlope sigma))
    (carlsonAffineDensityCeiling beta tau)
    (carlsonAffineDensitySlope sigma)
    x

/-- The Carlson log-majorant uses exactly the weighted-balanced exponent
already present in the selected-height PNT chain. -/
theorem carlsonFiniteAffineBalancedLogPowerMajorant_eq_weighted
    {n : ℕ} (contourCoeff : ℝ)
    (stripCoeff : Fin (n + 1) → ℝ)
    (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ) :
    carlsonFiniteAffineBalancedLogPowerMajorant
        contourCoeff stripCoeff beta sigma tau =
      finiteAffineDensityLogPowerMajorant
        contourCoeff stripCoeff
        (carlsonAffineDensityFloor beta)
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau)
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma) := by
  funext x
  unfold carlsonFiniteAffineBalancedLogPowerMajorant
  rw [carlsonAffineBalancedExponent_eq]

/-- The optimized Carlson power-log majorant is pointwise controlled by the
common envelope using the existing optimal physical margin. -/
theorem
    carlsonFiniteAffineBalancedLogPowerMajorant_le_optimalPhysical
    {n : ℕ} {contourCoeff beta x : ℝ}
    {stripCoeff sigma tau : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hx : 1 ≤ x) :
    carlsonFiniteAffineBalancedLogPowerMajorant
        contourCoeff stripCoeff beta sigma tau x ≤
      finiteAffineDensityCommonLogPower
        contourCoeff stripCoeff
        (actualSelectedHeightFiniteStripOptimalPhysicalMargin
          beta sigma tau)
        x := by
  have hsigmaPos : ∀ i, 0 < sigma i := by
    intro i
    linarith [hsigma i]
  unfold carlsonFiniteAffineBalancedLogPowerMajorant
  have hbound :=
    finiteAffineDensityLogPowerMajorant_le_common
      hcontourCoeff hstripCoeff hx
      (finiteAffineBalancedExponent_marginCertificate
        (carlsonAffineDensityFloor beta)
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma)
        (carlsonAffineDensitySlope_pos hsigmaPos hsigmaOne))
  rw [carlsonAffineOptimalMargin_eq] at hbound
  exact hbound

/-- Standard Carlson strip-endpoint thresholds make the optimized finite
power-log majorant tend to zero. -/
theorem
    tendsto_carlsonFiniteAffineBalancedLogPowerMajorant_zero_of_threshold
    {n : ℕ} {contourCoeff beta : ℝ}
    {stripCoeff sigma tau : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) :
    Tendsto
      (carlsonFiniteAffineBalancedLogPowerMajorant
        contourCoeff stripCoeff beta sigma tau)
      atTop (nhds 0) := by
  have hsigmaPos : ∀ i, 0 < sigma i := by
    intro i
    linarith [hsigma i]
  unfold carlsonFiniteAffineBalancedLogPowerMajorant
  exact tendsto_finiteAffineDensityLogPowerMajorant_zero
    hcontourCoeff hstripCoeff
    (carlsonAffineOptimalMargin_pos
      sigma tau hsigma hsigmaOne hthreshold)
    (finiteAffineBalancedExponent_marginCertificate
      (carlsonAffineDensityFloor beta)
      (carlsonAffineDensityCeiling beta tau)
      (carlsonAffineDensitySlope sigma)
      (carlsonAffineDensitySlope_pos hsigmaPos hsigmaOne))

end PrimeNumberTheorem
