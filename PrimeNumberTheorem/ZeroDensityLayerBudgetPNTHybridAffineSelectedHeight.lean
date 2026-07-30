import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualFiniteStrips
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffinePowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightOptimality
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicReverseZeroFree

/-!
# Mixed global/Carlson affine optimizer and selected good height

A hybrid finite profile has two kinds of density slope:

* a low-threshold layer counted globally has height slope `1`;
* a high-threshold layer counted by Carlson has slope
  `4 * sigma * (1 - sigma)`.

This file sends both kinds into the same finite affine minimax optimizer.  The
contour floor remains `1 - beta`, and every strip ceiling remains
`beta - tau i`.  The resulting exponent therefore optimizes the low global
layers, high Carlson layers, and contour remainder simultaneously.

The optimized exponent is then fed to the existing uniform good-height
selector.  Its selected height has asymptotic ratio one to the optimized
power scale and the certified logarithmic growth exponent.
-/

open Filter Topology

noncomputable section

namespace PrimeNumberTheorem

/-- Mixed height slope: global count on low indices, Carlson on high indices. -/
def pntHybridAffineDensitySlope
    {n : ℕ} (sigma : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i =>
    if sigma i ≤ 1 / 2 then
      1
    else
      carlsonAffineDensitySlope sigma i

/-- The hybrid optimizer has the same explicit-formula contour floor. -/
def pntHybridAffineDensityFloor (beta : ℝ) : ℝ :=
  1 - beta

/-- The hybrid optimizer has the same endpoint ceilings as the Carlson
optimizer. -/
def pntHybridAffineDensityCeiling
    {n : ℕ} (beta : ℝ) (tau : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => beta - tau i

/-- Optimal common physical margin of the mixed profile. -/
def pntHybridAffineOptimalMargin
    {n : ℕ} (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  finiteAffineOptimalMargin
    (pntHybridAffineDensityFloor beta)
    (pntHybridAffineDensityCeiling beta tau)
    (pntHybridAffineDensitySlope sigma)

/-- Power exponent of the jointly optimized mixed-profile truncation height. -/
def pntHybridAffineBalancedExponent
    {n : ℕ} (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  finiteAffineBalancedExponent
    (pntHybridAffineDensityFloor beta)
    (pntHybridAffineDensityCeiling beta tau)
    (pntHybridAffineDensitySlope sigma)

/-- Every mixed slope is positive when each high-threshold Carlson index has
upper threshold below one.  No positivity condition is imposed on low
thresholds. -/
theorem pntHybridAffineDensitySlope_pos
    {n : ℕ} {sigma : Fin (n + 1) → ℝ}
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1) :
    ∀ i, 0 < pntHybridAffineDensitySlope sigma i := by
  intro i
  unfold pntHybridAffineDensitySlope
  split
  · norm_num
  · rename_i hnotLow
    have hhalf : 1 / 2 < sigma i :=
      lt_of_not_ge hnotLow
    have hhigh :
        i ∈ pintzCarlsonHighDensityIndices sigma :=
      mem_pintzCarlsonHighDensityIndices.mpr hhalf
    have hone : sigma i < 1 :=
      hsigmaOneHigh i hhigh
    unfold carlsonAffineDensitySlope
      actualSelectedHeightStripCarlsonSlope
    nlinarith

/-- The mixed balanced exponent attains the finite-affine optimal margin. -/
theorem pntHybridAffineBalancedExponent_marginCertificate
    {n : ℕ} (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1) :
    FiniteAffineDensityMarginCertificate
      (pntHybridAffineDensityFloor beta)
      (pntHybridAffineDensityCeiling beta tau)
      (pntHybridAffineDensitySlope sigma)
      (pntHybridAffineBalancedExponent beta sigma tau)
      (pntHybridAffineOptimalMargin beta sigma tau) := by
  exact
    finiteAffineBalancedExponent_marginCertificate
      (pntHybridAffineDensityFloor beta)
      (pntHybridAffineDensityCeiling beta tau)
      (pntHybridAffineDensitySlope sigma)
      (pntHybridAffineDensitySlope_pos hsigmaOneHigh)

/-- Strict feasibility at the contour floor gives a positive optimal mixed
margin. -/
theorem pntHybridAffineOptimalMargin_pos
    {n : ℕ} {beta : ℝ}
    {sigma tau : Fin (n + 1) → ℝ}
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
            pntHybridAffineDensityFloor beta <
          pntHybridAffineDensityCeiling beta tau i) :
    0 < pntHybridAffineOptimalMargin beta sigma tau := by
  exact
    finiteAffineOptimalMargin_pos
      (pntHybridAffineDensityFloor beta)
      (pntHybridAffineDensityCeiling beta tau)
      (pntHybridAffineDensitySlope sigma)
      (pntHybridAffineDensitySlope_pos hsigmaOneHigh)
      hbudget

/-- Under `beta < 1`, strict mixed feasibility makes the optimized height
exponent positive. -/
theorem pntHybridAffineBalancedExponent_pos
    {n : ℕ} {beta : ℝ}
    {sigma tau : Fin (n + 1) → ℝ}
    (hbetaOne : beta < 1)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
            pntHybridAffineDensityFloor beta <
          pntHybridAffineDensityCeiling beta tau i) :
    0 < pntHybridAffineBalancedExponent beta sigma tau := by
  have hmargin :
      0 < pntHybridAffineOptimalMargin beta sigma tau :=
    pntHybridAffineOptimalMargin_pos hsigmaOneHigh hbudget
  unfold pntHybridAffineOptimalMargin
    pntHybridAffineDensityFloor at hmargin
  unfold pntHybridAffineBalancedExponent
    finiteAffineBalancedExponent pntHybridAffineDensityFloor
  linarith

/-- Uniformly selected good height at the jointly optimized hybrid exponent. -/
def pntHybridAffineSelectedGoodHeight
    {n : ℕ} (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  selectedUniformGoodHeight
    (pntHybridAffineBalancedExponent beta sigma tau)
    selection x

/-- The selected hybrid good height is asymptotic to its optimized power
scale. -/
theorem pntHybridAffineSelectedGoodHeight_div_optimalScale_tendsto_one
    {n : ℕ} {beta : ℝ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
            pntHybridAffineDensityFloor beta <
          pntHybridAffineDensityCeiling beta tau i)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun x =>
        pntHybridAffineSelectedGoodHeight beta sigma tau selection x /
          x ^ pntHybridAffineBalancedExponent beta sigma tau)
      atTop (nhds 1) := by
  exact
    selectedUniformGoodHeight_div_rpow_tendsto_one
      (pntHybridAffineBalancedExponent_pos
        hbetaOne hsigmaOneHigh hbudget)
      selection

/-- The logarithmic growth exponent of the selected hybrid height is the
certified mixed affine optimum. -/
theorem pntHybridAffineSelectedGoodHeight_logGrowth_tendsto_optimalExponent
    {n : ℕ} {beta : ℝ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
            pntHybridAffineDensityFloor beta <
          pntHybridAffineDensityCeiling beta tau i)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun x =>
        Real.log
              (pntHybridAffineSelectedGoodHeight
                beta sigma tau selection x) /
          Real.log x)
      atTop
      (nhds (pntHybridAffineBalancedExponent beta sigma tau)) := by
  exact
    selectedUniformGoodHeight_log_div_log_tendsto
      (pntHybridAffineBalancedExponent_pos
        hbetaOne hsigmaOneHigh hbudget)
      selection

/-- The selected hybrid height is cofinal. -/
theorem pntHybridAffineSelectedGoodHeight_tendsto_atTop
    {n : ℕ} {beta : ℝ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
            pntHybridAffineDensityFloor beta <
          pntHybridAffineDensityCeiling beta tau i)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (pntHybridAffineSelectedGoodHeight beta sigma tau selection)
      atTop atTop := by
  exact
    selectedUniformGoodHeight_tendsto_atTop
      (pntHybridAffineBalancedExponent_pos
        hbetaOne hsigmaOneHigh hbudget)
      selection

end PrimeNumberTheorem
