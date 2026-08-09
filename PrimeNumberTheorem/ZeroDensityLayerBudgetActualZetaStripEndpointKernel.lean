import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicActualZetaLayer
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonStripEndpointCriterion

/-!
# Actual zeta kernel bounds at a strip upper endpoint

Carlson counts zeros from a lower real-part threshold `sigma`.  To bound the
actual explicit-formula kernel in a strip, this file uses a separate upper
endpoint `tau` and an explicit denominator guard `kappa ≤ ‖rho‖`.

The denominator guard is not suppressed: zeros below the guarded height must
be isolated into a finite low-height contribution.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

open Filter

/-- Power-kernel budget at a strip upper endpoint, retaining the explicit
lower bound for the zero denominator. -/
noncomputable def stripEndpointRelativeKernelBudget
    (kappa tau x : ℝ) : ℝ :=
  kappa⁻¹ * x ^ (tau - 1)

/-- The exact relative PNT kernel is bounded by the strip upper-endpoint power
once the zero denominator has the explicit lower bound `kappa`. -/
theorem norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
    {x kappa tau : ℝ} {rho : ℂ}
    (hx : 1 ≤ x) (hkappa : 0 < kappa)
    (hnorm : kappa ≤ ‖rho‖) (hre : rho.re ≤ tau) :
    ‖pntRelativeSimpleZeroKernel x rho‖ ≤
      stripEndpointRelativeKernelBudget kappa tau x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpowNonneg : 0 ≤ x ^ (rho.re - 1) :=
    Real.rpow_nonneg (zero_le_one.trans hx) _
  have hpow :
      x ^ (rho.re - 1) ≤ x ^ (tau - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc
    ‖pntRelativeSimpleZeroKernel x rho‖ =
        x ^ (rho.re - 1) / ‖rho‖ :=
      norm_pntRelativeSimpleZeroKernel_eq hxpos rho
    _ ≤ x ^ (rho.re - 1) / kappa :=
      div_le_div_of_nonneg_left hpowNonneg hkappa hnorm
    _ ≤ x ^ (tau - 1) / kappa :=
      (div_le_div_iff_of_pos_right hkappa).2 hpow
    _ = stripEndpointRelativeKernelBudget kappa tau x := by
      simp [stripEndpointRelativeKernelBudget, div_eq_mul_inv, mul_comm]

/-- The strip-endpoint kernel budget is nonnegative at every positive base. -/
theorem stripEndpointRelativeKernelBudget_nonneg
    {x kappa tau : ℝ} (hx : 0 ≤ x) (hkappa : 0 ≤ kappa) :
    0 ≤ stripEndpointRelativeKernelBudget kappa tau x := by
  unfold stripEndpointRelativeKernelBudget
  positivity

/-- One dynamic actual-zeta bucket is bounded by the fixed-threshold Carlson
count times the distinct upper-endpoint kernel budget. -/
theorem dynamicPositivePNTLayerNorm_le_carlson_mul_stripEndpoint
    {n : ℕ} {T : ℝ → ℝ}
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) n)
    (i : Fin n) (sigma tau kappa : ℝ)
    (hsigma : ∀ x, (input x).sigma i = sigma)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    {x : ℝ} (hx : 1 ≤ x) :
    |dynamicPositivePNTLayerNorm T input i x| ≤
      dynamicCarlsonLayerCount sigma T x *
        stripEndpointRelativeKernelBudget kappa tau x := by
  have hkernel :
      ∀ rho ∈ (input x).layer i,
        ‖pntRelativeSimpleZeroKernel x rho‖ ≤
          stripEndpointRelativeKernelBudget kappa tau x := by
    intro rho hrho
    exact norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
      hx hkappa (hnorm x rho hrho) (hre x rho hrho)
  have hkernelNonneg :
      0 ≤ stripEndpointRelativeKernelBudget kappa tau x :=
    stripEndpointRelativeKernelBudget_nonneg
      (zero_le_one.trans hx) hkappa.le
  calc
    |dynamicPositivePNTLayerNorm T input i x| =
        dynamicPositivePNTLayerNorm T input i x := by
      exact abs_of_nonneg (norm_nonneg _)
    _ ≤ ∑ rho ∈ (input x).layer i,
          ‖pntRelativeZeroContribution x rho‖ := by
      exact norm_sum_le _ _
    _ ≤ stripEndpointRelativeKernelBudget kappa tau x *
          analyticMultiplicityMass ((input x).layer i) :=
      sum_norm_pntRelativeZeroContribution_le_kernel_mul_multiplicityMass
        ((input x).layer i) x
        (stripEndpointRelativeKernelBudget kappa tau x)
        hkernelNonneg hkernel
    _ ≤ stripEndpointRelativeKernelBudget kappa tau x *
          (ZeroDensity.zeroDensityCount ((input x).sigma i) (T x) : ℝ) :=
      mul_le_mul_of_nonneg_left
        ((input x).layer_multiplicityMass_le_zeroDensityCount i)
        hkernelNonneg
    _ = dynamicCarlsonLayerCount sigma T x *
          stripEndpointRelativeKernelBudget kappa tau x := by
      rw [hsigma x]
      simp [dynamicCarlsonLayerCount, mul_comm]

/-- The endpoint-aware pointwise theorem supplies the domination field of a
target-layer budget; only the normalized product remains as an analytic
hypothesis. -/
theorem dynamicPositivePNTLayerNorm_stripEndpointTargetLayerBudget
    {n : ℕ} {T amplitude : ℝ → ℝ}
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) n)
    (i : Fin n) (sigma tau kappa : ℝ)
    (hsigma : ∀ x, (input x).sigma i = sigma)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    (hnormalized :
      Filter.Tendsto
        (fun x =>
          dynamicCarlsonLayerCount sigma T x *
              stripEndpointRelativeKernelBudget kappa tau x /
            amplitude x)
        Filter.atTop (nhds 0)) :
    PintzCarlsonTargetLayerBudget amplitude
      (dynamicPositivePNTLayerNorm T input i)
      (dynamicCarlsonLayerCount sigma T)
      (stripEndpointRelativeKernelBudget kappa tau) where
  count_eventually_nonneg :=
    Filter.Eventually.of_forall
      (dynamicCarlsonLayerCount_nonneg sigma T)
  kernel_eventually_nonneg := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact stripEndpointRelativeKernelBudget_nonneg hx hkappa.le
  layer_abs_le_count_mul_kernel := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact dynamicPositivePNTLayerNorm_le_carlson_mul_stripEndpoint
      input i sigma tau kappa hsigma hkappa hnorm hre hx
  normalized_product_tendsto_zero := hnormalized

end PrimeNumberTheorem
