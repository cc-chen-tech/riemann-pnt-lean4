import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualTwoHeightSplit

/-!
# Balanced actual two-height Carlson transfer

The optimized intermediate height is now substituted into the actual zeta
strip theorem.  A single upper-endpoint condition implies decay of the full
multiplicity-weighted strip.
-/

open Filter
open scoped Topology

namespace PrimeNumberTheorem

/-- Largest strip upper endpoint allowed by the balanced two-height power
calculation, before logarithmic loss. -/
noncomputable def carlsonTwoHeightBalancedTauCeiling
    (sigma alpha : ℝ) : ℝ :=
  1 -
    (carlsonTwoHeightDensityExponent sigma) ^ 2 * alpha /
      (carlsonTwoHeightDensityExponent sigma + 1)

/-- Strip upper endpoint supplied by counting the complete strip only at the
outer height. -/
def carlsonSingleHeightTauCeiling
    (sigma alpha : ℝ) : ℝ :=
  1 - carlsonTwoHeightDensityExponent sigma * alpha

theorem carlsonTwoHeightBalancedExponent_add_lt_zero_iff
    {sigma tau alpha epsilon : ℝ} :
    carlsonTwoHeightBalancedExponent sigma tau alpha + epsilon < 0 ↔
      tau + epsilon <
        carlsonTwoHeightBalancedTauCeiling sigma alpha := by
  let A : ℝ :=
    (carlsonTwoHeightDensityExponent sigma) ^ 2 * alpha /
      (carlsonTwoHeightDensityExponent sigma + 1)
  change tau - 1 + A + epsilon < 0 ↔ tau + epsilon < 1 - A
  constructor <;> intro h <;> linarith

/-- The optimized vertical split admits a strictly larger real-part endpoint
than the unsplit outer-height count. -/
theorem carlsonSingleHeightTauCeiling_lt_balanced
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    carlsonSingleHeightTauCeiling sigma alpha <
      carlsonTwoHeightBalancedTauCeiling sigma alpha := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  have hden : 0 < carlsonTwoHeightDensityExponent sigma + 1 := by
    linarith
  have hstrict :
      carlsonTwoHeightDensityExponent sigma ^ 2 * alpha /
          (carlsonTwoHeightDensityExponent sigma + 1) <
        carlsonTwoHeightDensityExponent sigma * alpha := by
    rw [div_lt_iff₀ hden]
    nlinarith
  unfold carlsonSingleHeightTauCeiling
    carlsonTwoHeightBalancedTauCeiling
  linarith

/-- A single balanced exponent margin implies decay of the actual
multiplicity-weighted zeta kernels in the complete strip. -/
theorem
    tendsto_sum_norm_actualPositiveCarlsonStrip_balancedTwoHeight
    {sigma tau alpha epsilon : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin :
      carlsonTwoHeightBalancedExponent sigma tau alpha + epsilon < 0) :
    Tendsto
      (fun x =>
        ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
            (carlsonPolynomialHeight alpha x),
          ‖pntRelativeZeroContribution x rho‖)
      atTop (nhds 0) := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  have hden :
      carlsonTwoHeightDensityExponent sigma + 1 ≠ 0 := by
    linarith
  have hgamma :
      0 < carlsonTwoHeightBalancedCut sigma alpha :=
    carlsonTwoHeightBalancedCut_pos hhalf hone halpha
  have hgammaAlpha :
      carlsonTwoHeightBalancedCut sigma alpha ≤ alpha :=
    (carlsonTwoHeightBalancedCut_lt_alpha
      hhalf hone halpha).le
  apply tendsto_sum_norm_actualPositiveCarlsonStrip_twoHeight
    hhalf hone halpha hgamma hgammaAlpha hepsilon
  · rwa [carlsonTwoHeightLowExponent_balanced hden]
  · rwa [carlsonTwoHeightHighExponent_balanced hden]

/-- User-facing endpoint form of the balanced actual transfer. -/
theorem
    tendsto_sum_norm_actualPositiveCarlsonStrip_of_lt_balancedTauCeiling
    {sigma tau alpha epsilon : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (htau :
      tau + epsilon <
        carlsonTwoHeightBalancedTauCeiling sigma alpha) :
    Tendsto
      (fun x =>
        ∑ rho ∈ actualPositiveCarlsonStrip sigma tau
            (carlsonPolynomialHeight alpha x),
          ‖pntRelativeZeroContribution x rho‖)
      atTop (nhds 0) := by
  exact
    tendsto_sum_norm_actualPositiveCarlsonStrip_balancedTwoHeight
      hhalf hone halpha hepsilon
      (carlsonTwoHeightBalancedExponent_add_lt_zero_iff.mpr htau)

end PrimeNumberTheorem
