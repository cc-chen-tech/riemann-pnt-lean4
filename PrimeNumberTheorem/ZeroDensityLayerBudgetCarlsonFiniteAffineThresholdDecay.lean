import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffinePowerTransfer

/-!
# Carlson threshold conditions imply optimized finite-strip power decay

The affine Carlson power transfer exposes a raw positivity condition on the
strip budgets.  The actual PNT chain is naturally stated instead with the
classical endpoint thresholds

`carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta`.

The Carlson affine adapter already proves that these threshold inequalities
make the optimal physical margin positive.  This module closes the interface
gap: the automatically weighted-balanced finite-strip majorant is bounded by
the existing optimal physical margin and tends to zero directly from the
threshold hypotheses used elsewhere in the PNT transfer chain.
-/

noncomputable section

namespace PrimeNumberTheorem

open Filter

/-- On the classical Carlson density range, the optimized pointwise power
bound is expressed by the existing finite-strip optimal physical margin. -/
theorem
    carlsonFiniteAffineBalancedPowerMajorant_le_optimalPhysicalDecay
    {n : ℕ} {contourCoeff beta x : ℝ}
    {stripCoeff sigma tau : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hx : 1 ≤ x) :
    carlsonFiniteAffineBalancedPowerMajorant
        contourCoeff stripCoeff beta sigma tau x ≤
      finiteAffineDensityTotalCoeff contourCoeff stripCoeff *
        x ^ (-actualSelectedHeightFiniteStripOptimalPhysicalMargin
          beta sigma tau) := by
  have hsigmaPos : ∀ i, 0 < sigma i := by
    intro i
    linarith [hsigma i]
  have hbound :=
    carlsonFiniteAffineBalancedPowerMajorant_le_optimalDecay
      (beta := beta) (tau := tau)
      hcontourCoeff hstripCoeff hsigmaPos hsigmaOne hx
  rw [carlsonAffineOptimalMargin_eq] at hbound
  exact hbound

/-- The standard Carlson strip-endpoint threshold condition automatically
makes the weighted-balanced finite affine power majorant tend to zero. -/
theorem
    tendsto_carlsonFiniteAffineBalancedPowerMajorant_zero_of_threshold
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
      (carlsonFiniteAffineBalancedPowerMajorant
        contourCoeff stripCoeff beta sigma tau)
      atTop (nhds 0) := by
  have hsigmaPos : ∀ i, 0 < sigma i := by
    intro i
    linarith [hsigma i]
  unfold carlsonFiniteAffineBalancedPowerMajorant
  exact tendsto_finiteAffineDensityPowerMajorant_zero
    hcontourCoeff hstripCoeff
    (carlsonAffineOptimalMargin_pos
      sigma tau hsigma hsigmaOne hthreshold)
    (finiteAffineBalancedExponent_marginCertificate
      (carlsonAffineDensityFloor beta)
      (carlsonAffineDensityCeiling beta tau)
      (carlsonAffineDensitySlope sigma)
      (carlsonAffineDensitySlope_pos hsigmaPos hsigmaOne))

end PrimeNumberTheorem
