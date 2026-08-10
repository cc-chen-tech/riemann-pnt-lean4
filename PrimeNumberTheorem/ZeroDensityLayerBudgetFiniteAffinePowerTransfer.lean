import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteAffineDensityOptimizer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Power decay from a finite affine density certificate

This module turns the arithmetic certificate produced by the finite affine
density optimizer into an explicit power majorant.  The contour contribution
has exponent `floor - alpha`, while strip `i` has exponent
`slope i * alpha - ceiling i`.  A common margin certificate bounds every one
of these exponents by `-delta`.

Consequently, for `x >= 1`, every nonnegative weighted contribution is
bounded by the same power `x ^ (-delta)`.  The finite sum is therefore
controlled by the total coefficient times that power.  A positive margin
then gives decay at infinity, and the balanced optimizer supplies the
largest certified margin automatically.
-/

noncomputable section

namespace PrimeNumberTheorem

open Filter

/-- The finite affine power majorant consisting of one contour term and a
finite family of density-strip terms. -/
def finiteAffineDensityPowerMajorant
    {n : ℕ} (contourCoeff : ℝ)
    (stripCoeff : Fin (n + 1) → ℝ)
    (floor alpha : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ)
    (x : ℝ) : ℝ :=
  contourCoeff * x ^ (floor - alpha) +
    ∑ i, stripCoeff i * x ^ (slope i * alpha - ceiling i)

/-- The coefficient left after every affine contribution is compressed to
one common decay power. -/
def finiteAffineDensityTotalCoeff
    {n : ℕ} (contourCoeff : ℝ)
    (stripCoeff : Fin (n + 1) → ℝ) : ℝ :=
  contourCoeff + ∑ i, stripCoeff i

/-- Nonnegative coefficients make the affine power majorant nonnegative. -/
theorem finiteAffineDensityPowerMajorant_nonneg
    {n : ℕ} {contourCoeff floor alpha x : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hx : 0 ≤ x) :
    0 ≤
      finiteAffineDensityPowerMajorant
        contourCoeff stripCoeff floor alpha ceiling slope x := by
  unfold finiteAffineDensityPowerMajorant
  exact add_nonneg
    (mul_nonneg hcontourCoeff (Real.rpow_nonneg hx _))
    (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hstripCoeff i) (Real.rpow_nonneg hx _))

/-- A feasible common margin compresses the contour term and every density
strip to the single power `x ^ (-delta)`. -/
theorem finiteAffineDensityPowerMajorant_le_commonDecay
    {n : ℕ} {contourCoeff floor alpha delta x : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hx : 1 ≤ x)
    (certificate :
      FiniteAffineDensityMarginCertificate
        floor ceiling slope alpha delta) :
    finiteAffineDensityPowerMajorant
        contourCoeff stripCoeff floor alpha ceiling slope x ≤
      finiteAffineDensityTotalCoeff contourCoeff stripCoeff *
        x ^ (-delta) := by
  have hcontourExponent : floor - alpha ≤ -delta := by
    linarith [certificate.contour]
  have hstripExponent :
      ∀ i, slope i * alpha - ceiling i ≤ -delta := by
    intro i
    linarith [certificate.strip i]
  unfold finiteAffineDensityPowerMajorant
  calc
    contourCoeff * x ^ (floor - alpha) +
          ∑ i, stripCoeff i * x ^ (slope i * alpha - ceiling i) ≤
        contourCoeff * x ^ (-delta) +
          ∑ i, stripCoeff i * x ^ (-delta) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx hcontourExponent)
          hcontourCoeff
      · apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx (hstripExponent i))
          (hstripCoeff i)
    _ =
        finiteAffineDensityTotalCoeff contourCoeff stripCoeff *
          x ^ (-delta) := by
      rw [finiteAffineDensityTotalCoeff, add_mul, Finset.sum_mul]

/-- Any positive feasible margin makes the complete finite affine power
majorant tend to zero. -/
theorem tendsto_finiteAffineDensityPowerMajorant_zero
    {n : ℕ} {contourCoeff floor alpha delta : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hdelta : 0 < delta)
    (certificate :
      FiniteAffineDensityMarginCertificate
        floor ceiling slope alpha delta) :
    Tendsto
      (finiteAffineDensityPowerMajorant
        contourCoeff stripCoeff floor alpha ceiling slope)
      atTop (nhds 0) := by
  have hconstant :
      Tendsto
        (fun _ : ℝ =>
          finiteAffineDensityTotalCoeff contourCoeff stripCoeff)
        atTop
        (nhds (finiteAffineDensityTotalCoeff contourCoeff stripCoeff)) :=
    tendsto_const_nhds
  have hcommon :
      Tendsto
        (fun x : ℝ =>
          finiteAffineDensityTotalCoeff contourCoeff stripCoeff *
            x ^ (-delta))
        atTop (nhds 0) :=
    by
      simpa using hconstant.mul (tendsto_rpow_neg_atTop hdelta)
  refine squeeze_zero' ?_ ?_ hcommon
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact finiteAffineDensityPowerMajorant_nonneg
      hcontourCoeff hstripCoeff hx
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact finiteAffineDensityPowerMajorant_le_commonDecay
      hcontourCoeff hstripCoeff hx certificate

/-- The balanced affine exponent gives the pointwise majorant with the
optimal certified common power. -/
theorem finiteAffineBalancedPowerMajorant_le_optimalDecay
    {n : ℕ} {contourCoeff floor x : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hslope : ∀ i, 0 < slope i)
    (hx : 1 ≤ x) :
    finiteAffineDensityPowerMajorant
        contourCoeff stripCoeff floor
        (finiteAffineBalancedExponent floor ceiling slope)
        ceiling slope x ≤
      finiteAffineDensityTotalCoeff contourCoeff stripCoeff *
        x ^ (-finiteAffineOptimalMargin floor ceiling slope) := by
  exact finiteAffineDensityPowerMajorant_le_commonDecay
    hcontourCoeff hstripCoeff hx
    (finiteAffineBalancedExponent_marginCertificate
      floor ceiling slope hslope)

/-- Positive strip budget at the contour floor makes the optimally balanced
finite affine power majorant decay automatically. -/
theorem tendsto_finiteAffineBalancedPowerMajorant_zero
    {n : ℕ} {contourCoeff floor : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hslope : ∀ i, 0 < slope i)
    (hbudget : ∀ i, slope i * floor < ceiling i) :
    Tendsto
      (finiteAffineDensityPowerMajorant
        contourCoeff stripCoeff floor
        (finiteAffineBalancedExponent floor ceiling slope)
        ceiling slope)
      atTop (nhds 0) := by
  exact tendsto_finiteAffineDensityPowerMajorant_zero
    hcontourCoeff hstripCoeff
    (finiteAffineOptimalMargin_pos
      floor ceiling slope hslope hbudget)
    (finiteAffineBalancedExponent_marginCertificate
      floor ceiling slope hslope)

end PrimeNumberTheorem
