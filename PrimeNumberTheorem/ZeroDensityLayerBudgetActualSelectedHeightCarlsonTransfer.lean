import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZetaStripExcludingClusterTransfer

/-!
# Carlson transfer at a selected explicit-formula height

The explicit formula generally supplies a good height selected from a unit
interval, rather than the exact polynomial height used by the Carlson
asymptotic.  We place that interval immediately below the polynomial height.
Monotonicity of the actual multiplicity-weighted zero count then transfers
the proved Carlson estimate to the selected height.

This module treats one actual zeta strip outside a finite main cluster.  It
does not construct the good height or estimate the explicit-formula contour
remainder.
-/

namespace PrimeNumberTheorem

open Filter

/-- Base of the unit interval ending at the Carlson polynomial height. -/
noncomputable def actualCarlsonPolynomialGoodHeightBase
    (alpha x : ℝ) : ℝ :=
  carlsonPolynomialHeight alpha x - 1

/-- Every height in the selected unit interval lies below the exact
polynomial Carlson ceiling. -/
theorem goodHeightInterval_le_carlsonPolynomialHeight
    {alpha x T : ℝ}
    (hT :
      T ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
        (actualCarlsonPolynomialGoodHeightBase alpha x + 1)) :
    T ≤ carlsonPolynomialHeight alpha x := by
  simpa only [actualCarlsonPolynomialGoodHeightBase, sub_add_cancel] using hT.2

/-- An eventually selected good height is eventually below the polynomial
Carlson ceiling. -/
theorem eventually_selectedHeight_le_carlsonPolynomialHeight
    {alpha : ℝ} {H : ℝ → ℝ}
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
          (actualCarlsonPolynomialGoodHeightBase alpha x + 1)) :
    ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x :=
  hH.mono fun _ hx =>
    goodHeightInterval_le_carlsonPolynomialHeight hx

/-- The actual Carlson layer count is monotone in a pointwise height
comparison. -/
theorem dynamicCarlsonLayerCount_mono_height
    {sigma x : ℝ} {T U : ℝ → ℝ}
    (hTU : T x ≤ U x) :
    dynamicCarlsonLayerCount sigma T x ≤
      dynamicCarlsonLayerCount sigma U x := by
  simp only [dynamicCarlsonLayerCount]
  exact_mod_cast ZeroDensity.zeroDensityCount_mono_height hTU

/--
The normalized Carlson endpoint product at an arbitrary selected height
tends to zero whenever that height is eventually below the polynomial
height for which the Carlson estimate has already been proved.
-/
theorem
    tendsto_selectedDynamicCarlsonCount_mul_stripEndpoint_div_targetAmplitude
    {H : ℝ → ℝ}
    {beta sigma tau alpha kappa epsilon : ℝ}
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hkappa : 0 ≤ kappa)
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    Tendsto
      (fun x =>
        dynamicCarlsonLayerCount sigma H x *
            stripEndpointRelativeKernelBudget kappa tau x /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg
      (mul_nonneg
        (dynamicCarlsonLayerCount_nonneg sigma H x)
        (stripEndpointRelativeKernelBudget_nonneg hx.le hkappa))
      (by
        simp only [targetZeroPowerAmplitude]
        exact Real.rpow_nonneg hx.le _)
  · filter_upwards [hH, eventually_gt_atTop (0 : ℝ)] with x hxH hx
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right
        (dynamicCarlsonLayerCount_mono_height hxH)
        (stripEndpointRelativeKernelBudget_nonneg hx.le hkappa)
    · simp only [targetZeroPowerAmplitude]
      exact Real.rpow_nonneg hx.le _
  · exact
      tendsto_dynamicCarlsonCount_mul_stripEndpoint_div_targetAmplitude
        hsigma hsigmaOne halpha hepsilon hmargin

/--
One actual outside-cluster strip at an arbitrary selected height inherits the
polynomial-height Carlson target-amplitude budget.
-/
theorem actualZetaOutsideClusterStrip_selectedHeight_carlsonTargetLayerBudget
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta sigma tau alpha kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hfixedSigma : ∀ x, (input x).sigma i = sigma)
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
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
      (dynamicPositiveOutsideClusterPNTLayerNorm H S input i)
      (dynamicCarlsonLayerCount sigma H)
      (stripEndpointRelativeKernelBudget kappa tau) where
  count_eventually_nonneg :=
    Eventually.of_forall (dynamicCarlsonLayerCount_nonneg sigma H)
  kernel_eventually_nonneg := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact stripEndpointRelativeKernelBudget_nonneg hx hkappa.le
  layer_abs_le_count_mul_kernel := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact
      dynamicPositiveOutsideClusterPNTLayerNorm_le_carlson_mul_stripEndpoint
        input i sigma tau kappa hfixedSigma hkappa hnorm hre hx
  normalized_product_tendsto_zero :=
    tendsto_selectedDynamicCarlsonCount_mul_stripEndpoint_div_targetAmplitude
      hH hsigma hsigmaOne halpha hkappa.le hepsilon hmargin

/--
Good-height interval version of the selected-height outside-cluster strip
budget.  The height comparison is discharged automatically from interval
membership.
-/
theorem
    actualZetaOutsideClusterStrip_goodHeight_carlsonTargetLayerBudget
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta sigma tau alpha kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hfixedSigma : ∀ x, (input x).sigma i = sigma)
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
          (actualCarlsonPolynomialGoodHeightBase alpha x + 1))
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
      (dynamicPositiveOutsideClusterPNTLayerNorm H S input i)
      (dynamicCarlsonLayerCount sigma H)
      (stripEndpointRelativeKernelBudget kappa tau) :=
  actualZetaOutsideClusterStrip_selectedHeight_carlsonTargetLayerBudget
    input i hfixedSigma
    (eventually_selectedHeight_le_carlsonPolynomialHeight hH)
    hsigma hsigmaOne halpha hkappa hnorm hre hepsilon hmargin

end PrimeNumberTheorem
