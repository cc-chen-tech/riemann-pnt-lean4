import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTRectangularStrips
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualStripTransfer

/-!
# Carlson transfer with a growing ordinate floor

At polynomial truncation height `T = x ^ alpha`, a strip counted at `sigma`,
bounded above in real part by `tau`, and bounded below in ordinate by
`x ^ gamma` has total power exponent

`4 * alpha * sigma * (1 - sigma) + tau - 1 - gamma`.

The final `-gamma` is the denominator gain that is absent from a purely
real-part strip.  This module proves logarithmic absorption for that exponent,
transfers Carlson's actual multiplicity-weighted count, and applies the result
to one genuine rectangular layer of zeta zeros.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Total power exponent of a polynomial-height Carlson rectangle. -/
def carlsonRectangleExponent
    (sigma tau alpha gamma : ℝ) : ℝ :=
  carlsonClassicalPolynomialDensityExponent alpha sigma +
    tau - 1 - gamma

/-- Endpoint kernel when the ordinate floor grows like `x ^ gamma`. -/
noncomputable def polynomialOrdinateRectangleKernel
    (tau gamma x : ℝ) : ℝ :=
  x ^ (tau - 1) / x ^ gamma

/-- Power-times-logarithm majorant for one dynamic rectangle. -/
noncomputable def carlsonRectangleLogMajorant
    (sigma tau alpha gamma x : ℝ) : ℝ :=
  x ^ carlsonRectangleExponent sigma tau alpha gamma *
    (Real.log x) ^ (4 : ℕ)

/-- The ordinate floor lowers the endpoint-aware exponent by exactly
`gamma`. -/
theorem carlsonRectangleExponent_eq_stripEndpoint_sub
    (sigma tau alpha gamma : ℝ) :
    carlsonRectangleExponent sigma tau alpha gamma =
      targetAmplitudeStripEndpointExponent 1 tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) -
        gamma := by
  simp [carlsonRectangleExponent,
    targetAmplitudeStripEndpointExponent]

theorem carlsonRectangleExponent_zero_ordinateGain
    (sigma tau alpha : ℝ) :
    carlsonRectangleExponent sigma tau alpha 0 =
      targetAmplitudeStripEndpointExponent 1 tau
        (carlsonClassicalPolynomialDensityExponent alpha sigma) := by
  rw [carlsonRectangleExponent_eq_stripEndpoint_sub]
  ring

/-- A strict negative rectangle exponent absorbs Carlson's logarithmic fourth
power. -/
theorem tendsto_carlsonRectangleLogMajorant
    {sigma tau alpha gamma epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hmargin :
      carlsonRectangleExponent sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (carlsonRectangleLogMajorant sigma tau alpha gamma)
      atTop (nhds 0) :=
  tendsto_rpow_mul_log_four_atTop_nhds_zero hepsilon hmargin

/-- After composition with `T = x ^ alpha`, Carlson's count budget times the
growing-floor kernel is eventually a fixed coefficient times the rectangle
majorant. -/
theorem eventually_carlsonCountBudget_mul_polynomialOrdinateRectangleKernel
    (sigma tau alpha gamma : ℝ) :
    (fun x : ℝ =>
      carlsonPolynomialCountBudget sigma alpha x *
        polynomialOrdinateRectangleKernel tau gamma x)
      =ᶠ[atTop]
    (fun x : ℝ =>
      alpha ^ (4 : ℕ) *
        carlsonRectangleLogMajorant sigma tau alpha gamma x) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hpower :
      x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
          (x ^ (tau - 1) / x ^ gamma) =
        x ^ carlsonRectangleExponent sigma tau alpha gamma := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    simp [carlsonRectangleExponent]
    ring
  simp only [carlsonPolynomialCountBudget,
    polynomialOrdinateRectangleKernel, carlsonRectangleLogMajorant]
  rw [show
    alpha ^ (4 : ℕ) *
          (x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
            (Real.log x) ^ (4 : ℕ)) *
        (x ^ (tau - 1) / x ^ gamma) =
      alpha ^ (4 : ℕ) *
        ((x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
          (x ^ (tau - 1) / x ^ gamma)) *
            (Real.log x) ^ (4 : ℕ)) by ring]
  rw [hpower]

/-- The complete direct Carlson count budget times the growing-floor kernel
tends to zero under the rectangle exponent criterion. -/
theorem tendsto_carlsonCountBudget_mul_polynomialOrdinateRectangleKernel
    {sigma tau alpha gamma epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hmargin :
      carlsonRectangleExponent sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (fun x : ℝ =>
        carlsonPolynomialCountBudget sigma alpha x *
          polynomialOrdinateRectangleKernel tau gamma x)
      atTop (nhds 0) := by
  have hscaled :
      Tendsto
        (fun x : ℝ =>
          alpha ^ (4 : ℕ) *
            carlsonRectangleLogMajorant sigma tau alpha gamma x)
        atTop (nhds 0) := by
    simpa using
      tendsto_const_nhds.mul
        (tendsto_carlsonRectangleLogMajorant hepsilon hmargin)
  exact hscaled.congr'
    (eventually_carlsonCountBudget_mul_polynomialOrdinateRectangleKernel
      sigma tau alpha gamma).symm

/-- Carlson's actual multiplicity-weighted count, not merely its direct
majorant, inherits the rectangle decay. -/
theorem tendsto_dynamicCarlsonCount_mul_polynomialOrdinateRectangleKernel
    {sigma tau alpha gamma epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin :
      carlsonRectangleExponent sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (fun x : ℝ =>
        (ZeroDensity.zeroDensityCount sigma
            (carlsonPolynomialHeight alpha x) : ℝ) *
          polynomialOrdinateRectangleKernel tau gamma x)
      atTop (nhds 0) := by
  have hraw :=
    tendsto_count_mul_kernel_div_amplitude_of_isBigO
      (amplitude := fun _ : ℝ => 1)
      (carlson_zeroDensity_polynomialHeight_countBudget_isBigO
        hsigma hsigmaOne halpha)
      (by
        simpa using
          tendsto_carlsonCountBudget_mul_polynomialOrdinateRectangleKernel
            hepsilon hmargin)
  simpa using hraw

/-- Multiplicity mass of one actual zeta rectangle tends to zero when its
lower ordinate is eventually `x ^ gamma` and the rectangle exponent has a
strict negative margin. -/
theorem tendsto_actualPositiveRectangleLayerMass
    {n : ℕ} {sigma tau alpha gamma epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroRectangleInput (carlsonPolynomialHeight alpha x) n)
    (i : Fin n)
    (hfixedSigma : ∀ x, (input x).toBucket.sigma i = sigma)
    (hfixedTau : ∀ x, (input x).tau i = tau)
    (hfloor :
      ∀ᶠ x : ℝ in atTop,
        (input x).ordinateFloor i = x ^ gamma)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin :
      carlsonRectangleExponent sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (fun x : ℝ =>
        ∑ rho ∈ (input x).toBucket.layer i,
          ‖pntRelativeZeroContribution x rho‖)
      atTop (nhds 0) := by
  have hbudget :=
    tendsto_dynamicCarlsonCount_mul_polynomialOrdinateRectangleKernel
      hsigma hsigmaOne halpha hepsilon hmargin
  refine squeeze_zero'
    (g := fun x : ℝ =>
      (ZeroDensity.zeroDensityCount sigma
          (carlsonPolynomialHeight alpha x) : ℝ) *
        polynomialOrdinateRectangleKernel tau gamma x)
    ?_ ?_ hbudget
  · exact Filter.Eventually.of_forall fun x =>
      Finset.sum_nonneg fun _ _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ), hfloor] with x hx hfloorx
    have hlayer := (input x).sum_norm_layer_le i hx
    simpa [pntRelativeRectangleLayerBudget,
      hfixedSigma x, hfixedTau x, hfloorx,
      polynomialOrdinateRectangleKernel, mul_comm] using hlayer

end PrimeNumberTheorem
