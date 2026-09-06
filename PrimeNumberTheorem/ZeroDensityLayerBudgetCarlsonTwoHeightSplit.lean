import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonRectangleTransfer

/-!
# A two-height Carlson split

A growing ordinate floor cannot cover every positive zero below a cofinal
truncation height.  The correct use of the rectangular kernel is to split at
an intermediate height `x ^ gamma`:

* the low part is counted only up to `x ^ gamma`;
* the high part is counted up to `x ^ alpha`, but gains the denominator
  `x ^ gamma`.

Writing `q = 4 * sigma * (1 - sigma)`, the two polynomial exponents are

`q * gamma + tau - 1`

and

`q * alpha + tau - 1 - gamma`.

This module records the exact balancing calculation and transfers it to the
already-audited Carlson logarithmic majorants.  It does not yet construct the
two actual filtered zeta-zero finsets.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/-- The polynomial exponent in the Carlson count at real threshold `sigma`. -/
def carlsonTwoHeightDensityExponent (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

/-- Exponent of the low-ordinate part, counted only to `x ^ gamma`. -/
def carlsonTwoHeightLowExponent
    (sigma tau gamma : ℝ) : ℝ :=
  carlsonRectangleExponent sigma tau gamma 0

/-- Exponent of the high-ordinate part, counted to `x ^ alpha` and divided by
the splitting height `x ^ gamma`. -/
def carlsonTwoHeightHighExponent
    (sigma tau alpha gamma : ℝ) : ℝ :=
  carlsonRectangleExponent sigma tau alpha gamma

/-- The intermediate-height exponent which equalizes the low and high
Carlson powers. -/
noncomputable def carlsonTwoHeightBalancedCut
    (sigma alpha : ℝ) : ℝ :=
  carlsonTwoHeightDensityExponent sigma * alpha /
    (carlsonTwoHeightDensityExponent sigma + 1)

/-- The common exponent at the balanced intermediate height. -/
noncomputable def carlsonTwoHeightBalancedExponent
    (sigma tau alpha : ℝ) : ℝ :=
  tau - 1 +
    (carlsonTwoHeightDensityExponent sigma) ^ 2 * alpha /
      (carlsonTwoHeightDensityExponent sigma + 1)

theorem carlsonTwoHeightDensityExponent_pos
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    0 < carlsonTwoHeightDensityExponent sigma := by
  unfold carlsonTwoHeightDensityExponent
  exact mul_pos
    (mul_pos (by norm_num) (lt_trans (by norm_num) hhalf))
    (sub_pos.mpr hone)

theorem carlsonTwoHeightBalancedCut_pos
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    0 < carlsonTwoHeightBalancedCut sigma alpha := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  exact div_pos (mul_pos hq halpha) (by linarith)

theorem carlsonTwoHeightBalancedCut_lt_alpha
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    carlsonTwoHeightBalancedCut sigma alpha < alpha := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  rw [carlsonTwoHeightBalancedCut]
  exact (div_lt_iff₀ (by linarith)).2 (by nlinarith)

theorem carlsonTwoHeightLowExponent_eq
    (sigma tau gamma : ℝ) :
    carlsonTwoHeightLowExponent sigma tau gamma =
      carlsonTwoHeightDensityExponent sigma * gamma + tau - 1 := by
  simp [carlsonTwoHeightLowExponent, carlsonRectangleExponent,
    carlsonClassicalPolynomialDensityExponent,
    carlsonPolynomialHeightDensityExponent,
    carlsonTwoHeightDensityExponent]
  ring

theorem carlsonTwoHeightHighExponent_eq
    (sigma tau alpha gamma : ℝ) :
    carlsonTwoHeightHighExponent sigma tau alpha gamma =
      carlsonTwoHeightDensityExponent sigma * alpha + tau - 1 - gamma := by
  simp [carlsonTwoHeightHighExponent, carlsonRectangleExponent,
    carlsonClassicalPolynomialDensityExponent,
    carlsonPolynomialHeightDensityExponent,
    carlsonTwoHeightDensityExponent]
  ring

theorem carlsonTwoHeightLowExponent_balanced
    {sigma tau alpha : ℝ}
    (hden :
      carlsonTwoHeightDensityExponent sigma + 1 ≠ 0) :
    carlsonTwoHeightLowExponent sigma tau
        (carlsonTwoHeightBalancedCut sigma alpha) =
      carlsonTwoHeightBalancedExponent sigma tau alpha := by
  rw [carlsonTwoHeightLowExponent_eq]
  unfold carlsonTwoHeightBalancedCut carlsonTwoHeightBalancedExponent
  field_simp [hden]
  ring

theorem carlsonTwoHeightHighExponent_balanced
    {sigma tau alpha : ℝ}
    (hden :
      carlsonTwoHeightDensityExponent sigma + 1 ≠ 0) :
    carlsonTwoHeightHighExponent sigma tau alpha
        (carlsonTwoHeightBalancedCut sigma alpha) =
      carlsonTwoHeightBalancedExponent sigma tau alpha := by
  rw [carlsonTwoHeightHighExponent_eq]
  unfold carlsonTwoHeightBalancedCut carlsonTwoHeightBalancedExponent
  field_simp [hden]
  ring

/-- The balanced two-height exponent is strictly smaller than the exponent
obtained by counting the whole strip at the outer height. -/
theorem carlsonTwoHeightBalancedExponent_lt_singleHeight
    {sigma tau alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    carlsonTwoHeightBalancedExponent sigma tau alpha <
      carlsonTwoHeightDensityExponent sigma * alpha + tau - 1 := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  have hden : 0 < carlsonTwoHeightDensityExponent sigma + 1 := by
    linarith
  unfold carlsonTwoHeightBalancedExponent
  have hstrict :
      carlsonTwoHeightDensityExponent sigma ^ 2 * alpha /
          (carlsonTwoHeightDensityExponent sigma + 1) <
        carlsonTwoHeightDensityExponent sigma * alpha := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

/-- Sum of the low-height Carlson majorant and the high-ordinate rectangular
majorant. -/
noncomputable def carlsonTwoHeightLogMajorant
    (sigma tau alpha gamma x : ℝ) : ℝ :=
  carlsonRectangleLogMajorant sigma tau gamma 0 x +
    carlsonRectangleLogMajorant sigma tau alpha gamma x

theorem tendsto_carlsonTwoHeightLogMajorant
    {sigma tau alpha gamma epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hlow :
      carlsonTwoHeightLowExponent sigma tau gamma + epsilon < 0)
    (hhigh :
      carlsonTwoHeightHighExponent sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (carlsonTwoHeightLogMajorant sigma tau alpha gamma)
      atTop (nhds 0) := by
  have hlow' :
      Tendsto
        (carlsonRectangleLogMajorant sigma tau gamma 0)
        atTop (nhds 0) :=
    tendsto_carlsonRectangleLogMajorant hepsilon (by
      simpa [carlsonTwoHeightLowExponent] using hlow)
  have hhigh' :
      Tendsto
        (carlsonRectangleLogMajorant sigma tau alpha gamma)
        atTop (nhds 0) :=
    tendsto_carlsonRectangleLogMajorant hepsilon (by
      simpa [carlsonTwoHeightHighExponent] using hhigh)
  change
    Tendsto
      (fun x =>
        carlsonRectangleLogMajorant sigma tau gamma 0 x +
          carlsonRectangleLogMajorant sigma tau alpha gamma x)
      atTop (nhds 0)
  simpa only [zero_add] using hlow'.add hhigh'

/-- At the balanced cut, one strict exponent margin discharges both halves of
the two-height split. -/
theorem tendsto_balancedCarlsonTwoHeightLogMajorant
    {sigma tau alpha epsilon : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hepsilon : 0 < epsilon)
    (hmargin :
      carlsonTwoHeightBalancedExponent sigma tau alpha + epsilon < 0) :
    Tendsto
      (carlsonTwoHeightLogMajorant sigma tau alpha
        (carlsonTwoHeightBalancedCut sigma alpha))
      atTop (nhds 0) := by
  have hq := carlsonTwoHeightDensityExponent_pos hhalf hone
  have hden :
      carlsonTwoHeightDensityExponent sigma + 1 ≠ 0 := by
    linarith
  apply tendsto_carlsonTwoHeightLogMajorant hepsilon
  · rwa [carlsonTwoHeightLowExponent_balanced hden]
  · rwa [carlsonTwoHeightHighExponent_balanced hden]

end PrimeNumberTheorem
