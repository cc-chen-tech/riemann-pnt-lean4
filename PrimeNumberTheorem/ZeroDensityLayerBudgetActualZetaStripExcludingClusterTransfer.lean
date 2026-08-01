import PrimeNumberTheorem.ZeroDensityLayerBudgetPositiveZeroBucketExcludingClusterMultiplicity
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualStripTransfer

/-!
# Actual Carlson strip transfer outside a finite main cluster

This is the cluster-excluded analogue of the actual zeta strip transfer.  It
uses the existing endpoint kernel and Carlson polynomial-height limit, while
the dynamic layer sums precisely over positive-height zeros not in `S`.
-/

namespace PrimeNumberTheorem

open Filter

/-- Norm of one dynamic positive-height PNT zero layer after deletion of the
distinguished finite cluster. -/
noncomputable def dynamicPositiveOutsideClusterPNTLayerNorm
    {n : ℕ} (T : ℝ → ℝ) (S : Finset ℂ)
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (x : ℝ) : ℝ :=
  ‖∑ ρ ∈ (input x).layer i, pntRelativeZeroContribution x ρ‖

/-- One outside-cluster dynamic zeta bucket is bounded by the fixed-threshold
Carlson count times the strip upper-endpoint kernel. -/
theorem
    dynamicPositiveOutsideClusterPNTLayerNorm_le_carlson_mul_stripEndpoint
    {n : ℕ} {T : ℝ → ℝ} {S : Finset ℂ}
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (sigma tau kappa : ℝ)
    (hfixedSigma : ∀ x, (input x).sigma i = sigma)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    {x : ℝ} (hx : 1 ≤ x) :
    |dynamicPositiveOutsideClusterPNTLayerNorm T S input i x| ≤
      dynamicCarlsonLayerCount sigma T x *
        stripEndpointRelativeKernelBudget kappa tau x := by
  have hkernel :
      ∀ rho ∈ (input x).layer i,
        ‖pntRelativeSimpleZeroKernel x rho‖ ≤
          stripEndpointRelativeKernelBudget kappa tau x := by
    intro rho hrho
    exact
      norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
        hx hkappa (hnorm x rho hrho) (hre x rho hrho)
  have hkernelNonneg :
      0 ≤ stripEndpointRelativeKernelBudget kappa tau x :=
    stripEndpointRelativeKernelBudget_nonneg
      (zero_le_one.trans hx) hkappa.le
  calc
    |dynamicPositiveOutsideClusterPNTLayerNorm T S input i x| =
        dynamicPositiveOutsideClusterPNTLayerNorm T S input i x := by
      exact abs_of_nonneg (norm_nonneg _)
    _ ≤ ∑ rho ∈ (input x).layer i,
        ‖pntRelativeZeroContribution x rho‖ := by
      exact norm_sum_le _ _
    _ ≤ stripEndpointRelativeKernelBudget kappa tau x *
        (ZeroDensity.zeroDensityCount ((input x).sigma i) (T x) : ℝ) :=
      (input x).sum_norm_pntRelativeZeroContribution_layer_le_count
        i hkernelNonneg hkernel
    _ = dynamicCarlsonLayerCount sigma T x *
        stripEndpointRelativeKernelBudget kappa tau x := by
      rw [hfixedSigma x]
      simp [dynamicCarlsonLayerCount, mul_comm]

/--
Actual target-amplitude budget for one outside-cluster zeta strip at
polynomial dynamic height.  The normalized-limit input is discharged by the
existing Carlson endpoint criterion.
-/
theorem actualZetaOutsideClusterStrip_carlsonTargetLayerBudget
    {n : ℕ} {S : Finset ℂ}
    {beta sigma tau alpha kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
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
      (dynamicPositiveOutsideClusterPNTLayerNorm
        (carlsonPolynomialHeight alpha) S input i)
      (dynamicCarlsonLayerCount sigma
        (carlsonPolynomialHeight alpha))
      (stripEndpointRelativeKernelBudget kappa tau) where
  count_eventually_nonneg :=
    Eventually.of_forall
      (dynamicCarlsonLayerCount_nonneg sigma
        (carlsonPolynomialHeight alpha))
  kernel_eventually_nonneg := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact stripEndpointRelativeKernelBudget_nonneg hx hkappa.le
  layer_abs_le_count_mul_kernel := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact
      dynamicPositiveOutsideClusterPNTLayerNorm_le_carlson_mul_stripEndpoint
        input i sigma tau kappa hfixedSigma hkappa hnorm hre hx
  normalized_product_tendsto_zero :=
    tendsto_dynamicCarlsonCount_mul_stripEndpoint_div_targetAmplitude
      hsigma hsigmaOne halpha hepsilon hmargin

end PrimeNumberTheorem
