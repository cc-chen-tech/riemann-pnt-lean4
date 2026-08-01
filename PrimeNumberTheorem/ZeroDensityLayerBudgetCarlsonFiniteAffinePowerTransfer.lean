import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffineAdapter
import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteAffinePowerTransfer

/-!
# Carlson finite-strip power decay through the affine optimizer

This module specializes the density-agnostic finite affine power transfer to
Carlson's classical exponent.  For a target exponent `beta`, strip endpoint
`tau i`, and density parameter `sigma i`, the affine data are

* contour floor `1 - beta`;
* strip ceiling `beta - tau i`;
* strip slope `4 * sigma i * (1 - sigma i)`.

The generic balanced exponent is already proved equal, in the affine Carlson
adapter, to the weighted-balanced height exponent used by the actual PNT
transfer chain.  Thus the same automatically optimized height now carries an
explicit finite-sum power majorant and decay theorem.
-/

noncomputable section

namespace PrimeNumberTheorem

open Filter

/-- Carlson's finite affine power majorant evaluated at the automatically
balanced truncation exponent. -/
def carlsonFiniteAffineBalancedPowerMajorant
    {n : ℕ} (contourCoeff : ℝ)
    (stripCoeff : Fin (n + 1) → ℝ)
    (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ)
    (x : ℝ) : ℝ :=
  finiteAffineDensityPowerMajorant
    contourCoeff stripCoeff
    (carlsonAffineDensityFloor beta)
    (finiteAffineBalancedExponent
      (carlsonAffineDensityFloor beta)
      (carlsonAffineDensityCeiling beta tau)
      (carlsonAffineDensitySlope sigma))
    (carlsonAffineDensityCeiling beta tau)
    (carlsonAffineDensitySlope sigma)
    x

/-- Carlson slopes are positive throughout the classical density range. -/
theorem carlsonAffineDensitySlope_pos
    {n : ℕ} {sigma : Fin (n + 1) → ℝ}
    (hsigma : ∀ i, 0 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    ∀ i, 0 < carlsonAffineDensitySlope sigma i := by
  intro i
  unfold carlsonAffineDensitySlope
  unfold actualSelectedHeightStripCarlsonSlope
  nlinarith [hsigma i, hsigmaOne i]

/-- The Carlson-balanced majorant is exactly the generic affine majorant at
the weighted-balanced exponent already used by the PNT chain. -/
theorem carlsonFiniteAffineBalancedPowerMajorant_eq_weighted
    {n : ℕ} (contourCoeff : ℝ)
    (stripCoeff : Fin (n + 1) → ℝ)
    (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ) :
    carlsonFiniteAffineBalancedPowerMajorant
        contourCoeff stripCoeff beta sigma tau =
      finiteAffineDensityPowerMajorant
        contourCoeff stripCoeff
        (carlsonAffineDensityFloor beta)
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau)
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma) := by
  funext x
  unfold carlsonFiniteAffineBalancedPowerMajorant
  rw [carlsonAffineBalancedExponent_eq]

/-- The optimized Carlson finite-strip majorant is pointwise bounded by its
total coefficient times the optimal common decay power. -/
theorem carlsonFiniteAffineBalancedPowerMajorant_le_optimalDecay
    {n : ℕ} {contourCoeff beta x : ℝ}
    {stripCoeff sigma tau : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hsigma : ∀ i, 0 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hx : 1 ≤ x) :
    carlsonFiniteAffineBalancedPowerMajorant
        contourCoeff stripCoeff beta sigma tau x ≤
      finiteAffineDensityTotalCoeff contourCoeff stripCoeff *
        x ^ (-finiteAffineOptimalMargin
          (carlsonAffineDensityFloor beta)
          (carlsonAffineDensityCeiling beta tau)
          (carlsonAffineDensitySlope sigma)) := by
  unfold carlsonFiniteAffineBalancedPowerMajorant
  exact finiteAffineBalancedPowerMajorant_le_optimalDecay
    hcontourCoeff hstripCoeff
    (carlsonAffineDensitySlope_pos hsigma hsigmaOne)
    hx

/-- Positive Carlson budget at the contour floor makes the automatically
balanced finite-strip majorant tend to zero. -/
theorem tendsto_carlsonFiniteAffineBalancedPowerMajorant_zero
    {n : ℕ} {contourCoeff beta : ℝ}
    {stripCoeff sigma tau : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hsigma : ∀ i, 0 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hbudget :
      ∀ i,
        carlsonAffineDensitySlope sigma i *
            carlsonAffineDensityFloor beta <
          carlsonAffineDensityCeiling beta tau i) :
    Tendsto
      (carlsonFiniteAffineBalancedPowerMajorant
        contourCoeff stripCoeff beta sigma tau)
      atTop (nhds 0) := by
  unfold carlsonFiniteAffineBalancedPowerMajorant
  exact tendsto_finiteAffineBalancedPowerMajorant_zero
    hcontourCoeff hstripCoeff
    (carlsonAffineDensitySlope_pos hsigma hsigmaOne)
    hbudget

end PrimeNumberTheorem
