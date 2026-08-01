import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffineActualSelectedHeightCoefficient
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStrips

/-!
# Actual Carlson affine coefficients outside a visible zero cluster

The explicit-formula residual uses buckets of positive zeros outside a finite
visible cluster.  Such a bucket input is intentionally weaker than a bucket
input for all positive zeros, so it cannot be coerced to the earlier actual
coefficient bridge.

This module supplies the missing direct bridge.  Carlson's count of all zeros
still bounds each outside-cluster layer, while the actual endpoint zeta kernel
controls its multiplicity-weighted PNT norm.  The same finite coefficient
family and weighted affine optimizer therefore control the genuine positive
outside-cluster tail.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

/-- Target-normalized sum of actual multiplicity-weighted positive
outside-cluster layer norms. -/
noncomputable def
    actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
    {n : ℕ}
    (T : ℝ → ℝ) (S : Finset ℂ)
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S (n + 1))
    (beta x : ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    dynamicPositiveOutsideClusterPNTLayerNorm T S input i x /
      targetZeroPowerAmplitude beta x

/-- Actual outside-cluster layers are eventually bounded by the same exposed
Carlson coefficient log-majorant as the all-positive-zero bridge. -/
theorem
    eventually_actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum_le_majorant
    {n : ℕ} {T : ℝ → ℝ} {S : Finset ℂ}
    {sigma : Fin (n + 1) → ℝ} {alpha beta : ℝ}
    (certificate :
      CarlsonFiniteStripCountCoefficientCertificate T sigma alpha)
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S (n + 1))
    (tau kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    ∀ᶠ x : ℝ in atTop,
      actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
          T S input beta x ≤
        actualCarlsonFiniteStripEndpointCoefficientLogMajorant
          certificate beta tau kappa x := by
  unfold actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
    actualCarlsonFiniteStripEndpointCoefficientLogMajorant
  refine
    Filter.Eventually.mono
      ((Finset.eventually_all
        (p := fun i x =>
          dynamicPositiveOutsideClusterPNTLayerNorm T S input i x /
                targetZeroPowerAmplitude beta x ≤
              actualCarlsonFiniteAffineStripCoeff certificate kappa i *
                carlsonStripEndpointNormalizedLogMajorant
                  beta (sigma i) (tau i) alpha x)
        (Finset.univ : Finset (Fin (n + 1)))).2 ?_) ?_
  · intro i hi
    filter_upwards
        [certificate.count_eventually_le i,
          eventually_carlsonCountBudget_mul_stripEndpoint_div_targetAmplitude
            beta (sigma i) (tau i) alpha (kappa i),
          eventually_ge_atTop (1 : ℝ)] with
        x hxCount hxFormula hx
    have hxPos : 0 < x := zero_lt_one.trans_le hx
    have hAmplitude :
        0 < targetZeroPowerAmplitude beta x := by
      unfold targetZeroPowerAmplitude
      exact Real.rpow_pos_of_pos hxPos _
    have hKernel :
        0 ≤ stripEndpointRelativeKernelBudget (kappa i) (tau i) x :=
      stripEndpointRelativeKernelBudget_nonneg
        (zero_le_one.trans hx) (hkappa i).le
    have hLayer :=
      dynamicPositiveOutsideClusterPNTLayerNorm_le_carlson_mul_stripEndpoint
        input i (sigma i) (tau i) (kappa i)
        (hfixedSigma i) (hkappa i) (hnorm i) (hre i) hx
    have hLayerNonneg :
        0 ≤ dynamicPositiveOutsideClusterPNTLayerNorm T S input i x := by
      unfold dynamicPositiveOutsideClusterPNTLayerNorm
      exact norm_nonneg _
    rw [abs_of_nonneg hLayerNonneg] at hLayer
    calc
      dynamicPositiveOutsideClusterPNTLayerNorm T S input i x /
            targetZeroPowerAmplitude beta x ≤
          (dynamicCarlsonLayerCount (sigma i) T x *
              stripEndpointRelativeKernelBudget (kappa i) (tau i) x) /
            targetZeroPowerAmplitude beta x :=
        div_le_div_of_nonneg_right hLayer hAmplitude.le
      _ ≤
          ((certificate.coeff i *
                carlsonPolynomialCountBudget (sigma i) alpha x) *
              stripEndpointRelativeKernelBudget (kappa i) (tau i) x) /
            targetZeroPowerAmplitude beta x := by
        apply div_le_div_of_nonneg_right _ hAmplitude.le
        exact mul_le_mul_of_nonneg_right hxCount hKernel
      _ =
          certificate.coeff i *
            (carlsonPolynomialCountBudget (sigma i) alpha x *
                stripEndpointRelativeKernelBudget (kappa i) (tau i) x /
              targetZeroPowerAmplitude beta x) := by
        ring
      _ =
          certificate.coeff i *
            (alpha ^ 4 * (kappa i)⁻¹ *
              carlsonStripEndpointNormalizedLogMajorant
                beta (sigma i) (tau i) alpha x) := by
        rw [hxFormula]
      _ =
          actualCarlsonFiniteAffineStripCoeff certificate kappa i *
            carlsonStripEndpointNormalizedLogMajorant
              beta (sigma i) (tau i) alpha x := by
        unfold actualCarlsonFiniteAffineStripCoeff
        ring
  · intro x hx
    exact Finset.sum_le_sum fun i hi => hx i hi

/-- Finite-affine form of the actual outside-cluster coefficient majorant. -/
theorem
    eventually_actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum_le_finiteAffine
    {n : ℕ} {T : ℝ → ℝ} {S : Finset ℂ}
    {sigma : Fin (n + 1) → ℝ} {alpha beta : ℝ}
    (certificate :
      CarlsonFiniteStripCountCoefficientCertificate T sigma alpha)
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S (n + 1))
    (tau kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    ∀ᶠ x : ℝ in atTop,
      actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
          T S input beta x ≤
        finiteAffineDensityLogPowerMajorant
          0
          (actualCarlsonFiniteAffineStripCoeff certificate kappa)
          (carlsonAffineDensityFloor beta)
          alpha
          (carlsonAffineDensityCeiling beta tau)
          (carlsonAffineDensitySlope sigma)
          x := by
  simpa only
      [actualCarlsonFiniteStripEndpointCoefficientLogMajorant_eq_finiteAffine]
    using
      eventually_actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum_le_majorant
        certificate input tau kappa hfixedSigma hkappa hnorm hre

/-- At the weighted selected good height, the actual positive outside-cluster
layer norm sum is negligible relative to the target zero amplitude. -/
theorem
    tendsto_actualSelectedHeightWeightedBalancedOutsideClusterLayerNormSum_zero
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    Tendsto
      (actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)
        S input beta)
      atTop (nhds 0) := by
  let certificate :=
    actualSelectedHeightWeightedBalancedCountCoefficientCertificate
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
  have hmajorant :
      Tendsto
        (carlsonFiniteAffineBalancedLogPowerMajorant
          0
          (actualCarlsonFiniteAffineStripCoeff certificate kappa)
          beta sigma tau)
        atTop (nhds 0) :=
    tendsto_carlsonFiniteAffineBalancedLogPowerMajorant_zero_of_threshold
      (by norm_num)
      (actualCarlsonFiniteAffineStripCoeff_nonneg
        certificate hkappa)
      hsigma hsigmaOne hthreshold
  have hlower :
      ∀ᶠ x : ℝ in atTop,
        0 ≤
          actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S input beta x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    unfold actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hx _)
  have hupper :=
    eventually_actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum_le_finiteAffine
      (beta := beta) certificate input tau kappa
      hfixedSigma hkappa hnorm hre
  have hupperBalanced :
      ∀ᶠ x : ℝ in atTop,
        actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S input beta x ≤
          carlsonFiniteAffineBalancedLogPowerMajorant
            0
            (actualCarlsonFiniteAffineStripCoeff certificate kappa)
            beta sigma tau x := by
    simpa only
        [carlsonFiniteAffineBalancedLogPowerMajorant_eq_weighted] using
      hupper
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmajorant hlower hupperBalanced

/-- The genuine positive outside-cluster PNT tail, not only its layer-norm
majorant, is negligible at the optimized selected height. -/
theorem
    tendsto_actualSelectedHeightWeightedBalancedPositiveOutsideClusterTail_zero
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    Tendsto
      (fun x : ℝ =>
        dynamicPositiveOutsideClusterPNTTailNorm
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S x /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  have hsum :=
    tendsto_actualSelectedHeightWeightedBalancedOutsideClusterLayerNormSum_zero
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      input kappa hfixedSigma hkappa hnorm hre
  have hlower :
      ∀ᶠ x : ℝ in atTop,
        0 ≤
          dynamicPositiveOutsideClusterPNTTailNorm
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              S x /
            targetZeroPowerAmplitude beta x := by
    filter_upwards [targetZeroPowerAmplitude_eventually_pos beta] with x hx
    exact div_nonneg (norm_nonneg _) hx.le
  have hupper :
      ∀ᶠ x : ℝ in atTop,
        dynamicPositiveOutsideClusterPNTTailNorm
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              S x /
            targetZeroPowerAmplitude beta x ≤
          actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S input beta x := by
    filter_upwards [targetZeroPowerAmplitude_eventually_pos beta] with x hx
    have htail :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms input x
    calc
      dynamicPositiveOutsideClusterPNTTailNorm
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S x /
          targetZeroPowerAmplitude beta x ≤
        (∑ i : Fin (n + 1),
            dynamicPositiveOutsideClusterPNTLayerNorm
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              S input i x) /
          targetZeroPowerAmplitude beta x :=
        div_le_div_of_nonneg_right htail hx.le
      _ =
          actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S input beta x := by
        simp [actualCarlsonFiniteOutsideClusterNormalizedLayerNormSum,
          Finset.sum_div]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum hlower hupper

end PrimeNumberTheorem
