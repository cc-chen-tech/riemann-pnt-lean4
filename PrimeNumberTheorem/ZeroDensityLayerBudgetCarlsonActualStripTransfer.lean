import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZetaStripEndpointKernel

/-!
# Carlson transfer for an actual dynamic zeta strip

This file combines four independently audited ingredients:

* Carlson's actual multiplicity-weighted density `BigO`;
* polynomial dynamic height;
* the distinct strip upper-endpoint kernel bound;
* absorption of Carlson's logarithmic fourth power.

The result is an actual `PintzCarlsonTargetLayerBudget` for one positive-height
zeta bucket.  The hypotheses retain the strip upper endpoint and the explicit
denominator guard.
-/

namespace PrimeNumberTheorem

open Filter

/-- Power amplitude corresponding to a target zero with real part `beta`,
up to its fixed multiplicity and denominator constants. -/
noncomputable def targetZeroPowerAmplitude
    (beta x : ℝ) : ℝ :=
  x ^ (beta - 1)

/-- Endpoint-aware Carlson power-times-logarithm majorant after normalization
by the target power amplitude. -/
noncomputable def carlsonStripEndpointNormalizedLogMajorant
    (beta sigma tau alpha x : ℝ) : ℝ :=
  x ^ targetAmplitudeStripEndpointExponent beta tau
      (carlsonClassicalPolynomialDensityExponent alpha sigma) *
    (Real.log x) ^ (4 : ℕ)

/-- A strict endpoint-aware exponent margin absorbs Carlson's logarithmic
fourth power. -/
theorem tendsto_carlsonStripEndpointNormalizedLogMajorant
    {beta sigma tau alpha epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    Filter.Tendsto
      (carlsonStripEndpointNormalizedLogMajorant
        beta sigma tau alpha)
      Filter.atTop (nhds 0) := by
  exact tendsto_rpow_mul_log_four_atTop_nhds_zero
    hepsilon hmargin

/-- The direct Carlson count budget times the strip endpoint kernel, divided
by the target power amplitude, is eventually a fixed constant times the
endpoint-aware logarithmic majorant. -/
theorem eventually_carlsonCountBudget_mul_stripEndpoint_div_targetAmplitude
    (beta sigma tau alpha kappa : ℝ) :
    (fun x =>
      carlsonPolynomialCountBudget sigma alpha x *
          stripEndpointRelativeKernelBudget kappa tau x /
        targetZeroPowerAmplitude beta x)
      =ᶠ[Filter.atTop]
    (fun x =>
      (alpha ^ (4 : ℕ) * kappa⁻¹) *
        carlsonStripEndpointNormalizedLogMajorant
          beta sigma tau alpha x) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hpower :
      x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
            x ^ (tau - 1) /
          x ^ (beta - 1) =
        x ^ targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    simp [targetAmplitudeStripEndpointExponent]
    ring
  simp only [carlsonPolynomialCountBudget,
    stripEndpointRelativeKernelBudget, targetZeroPowerAmplitude,
    carlsonStripEndpointNormalizedLogMajorant]
  rw [show
    alpha ^ (4 : ℕ) *
          (x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
            (Real.log x) ^ (4 : ℕ)) *
          (kappa⁻¹ * x ^ (tau - 1)) /
        x ^ (beta - 1) =
      (alpha ^ (4 : ℕ) * kappa⁻¹) *
        ((x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
            x ^ (tau - 1) / x ^ (beta - 1)) *
          (Real.log x) ^ (4 : ℕ)) by ring]
  rw [hpower]

/-- A strict endpoint-aware margin makes the complete direct count budget
times endpoint kernel, normalized by the target amplitude, tend to zero. -/
theorem tendsto_carlsonCountBudget_mul_stripEndpoint_div_targetAmplitude
    {beta sigma tau alpha kappa epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    Filter.Tendsto
      (fun x =>
        carlsonPolynomialCountBudget sigma alpha x *
            stripEndpointRelativeKernelBudget kappa tau x /
          targetZeroPowerAmplitude beta x)
      Filter.atTop (nhds 0) := by
  have hscaled :
      Filter.Tendsto
        (fun x =>
          (alpha ^ (4 : ℕ) * kappa⁻¹) *
            carlsonStripEndpointNormalizedLogMajorant
              beta sigma tau alpha x)
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_carlsonStripEndpointNormalizedLogMajorant
          hepsilon hmargin))
  exact hscaled.congr'
    (eventually_carlsonCountBudget_mul_stripEndpoint_div_targetAmplitude
      beta sigma tau alpha kappa).symm

/-- A `BigO` count bound transfers any normalized product decay from the count
budget to the actual count. -/
theorem tendsto_count_mul_kernel_div_amplitude_of_isBigO
    {count countBudget kernel amplitude : ℝ → ℝ}
    (hcount :
      count =O[Filter.atTop] countBudget)
    (hbudget :
      Filter.Tendsto
        (fun x => countBudget x * kernel x / amplitude x)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun x => count x * kernel x / amplitude x)
      Filter.atTop (nhds 0) := by
  have hratio :
      (fun x => count x * (kernel x / amplitude x))
        =O[Filter.atTop]
      (fun x => countBudget x * (kernel x / amplitude x)) :=
    hcount.mul
      (Asymptotics.isBigO_refl
        (fun x => kernel x / amplitude x) Filter.atTop)
  have hproduct :
      (fun x => count x * kernel x / amplitude x)
        =O[Filter.atTop]
      (fun x => countBudget x * kernel x / amplitude x) := by
    refine hratio.congr' ?_ ?_
    · exact Filter.Eventually.of_forall fun x => by ring
    · exact Filter.Eventually.of_forall fun x => by ring
  exact hproduct.trans_tendsto hbudget

/-- Carlson's actual count at polynomial height, multiplied by the endpoint
kernel and normalized by the target power amplitude, tends to zero under the
strict endpoint-aware exponent margin. -/
theorem tendsto_dynamicCarlsonCount_mul_stripEndpoint_div_targetAmplitude
    {beta sigma tau alpha kappa epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    Filter.Tendsto
      (fun x =>
        dynamicCarlsonLayerCount sigma
              (carlsonPolynomialHeight alpha) x *
            stripEndpointRelativeKernelBudget kappa tau x /
          targetZeroPowerAmplitude beta x)
      Filter.atTop (nhds 0) := by
  apply tendsto_count_mul_kernel_div_amplitude_of_isBigO
    (carlson_zeroDensity_polynomialHeight_countBudget_isBigO
      hsigma hsigmaOne halpha)
  exact
    tendsto_carlsonCountBudget_mul_stripEndpoint_div_targetAmplitude
      hepsilon hmargin

/-- Actual target-amplitude budget for one zeta strip at polynomial dynamic
height.  No abstract pointwise kernel hypothesis or normalized-limit
hypothesis remains. -/
theorem actualZetaStrip_carlsonTargetLayerBudget
    {n : ℕ} {beta sigma tau alpha kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput (carlsonPolynomialHeight alpha x) n)
    (i : Fin n)
    (hfixedSigma : ∀ x, (input x).sigma i = sigma)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    PintzCarlsonTargetLayerBudget
      (targetZeroPowerAmplitude beta)
      (dynamicPositivePNTLayerNorm
        (carlsonPolynomialHeight alpha) input i)
      (dynamicCarlsonLayerCount sigma
        (carlsonPolynomialHeight alpha))
      (stripEndpointRelativeKernelBudget kappa tau) := by
  apply
    dynamicPositivePNTLayerNorm_stripEndpointTargetLayerBudget
      input i sigma tau kappa hfixedSigma hkappa hnorm hre
  exact
    tendsto_dynamicCarlsonCount_mul_stripEndpoint_div_targetAmplitude
      hsigma hsigmaOne halpha hepsilon hmargin

end PrimeNumberTheorem
