import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZetaStripExcludingClusterTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualFiniteStrips

/-!
# Finite aggregation of actual Carlson strips outside a main cluster

Finitely many endpoint-aware Carlson certificates are aggregated over the
exact positive-height zero tail with a distinguished finite cluster removed.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

open Filter

/-- Norm of the complete positive-ordinate relative PNT zero sum outside `S`
at a dynamic height. -/
noncomputable def dynamicPositiveOutsideClusterPNTTailNorm
    (T : ℝ → ℝ) (S : Finset ℂ) (x : ℝ) : ℝ :=
  ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset (T x) S,
      pntRelativeZeroContribution x rho‖

/-- The outside-cluster positive tail is pointwise dominated by the sum of the
norms of an exhaustive outside-cluster bucket decomposition. -/
theorem dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms
    {n : ℕ} {T : ℝ → ℝ} {S : Finset ℂ}
    (input :
      (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (x : ℝ) :
    dynamicPositiveOutsideClusterPNTTailNorm T S x ≤
      ∑ i : Fin n,
        dynamicPositiveOutsideClusterPNTLayerNorm T S input i x := by
  have hdecomp :
      (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset (T x) S,
          pntRelativeZeroContribution x rho) =
        ∑ i : Fin n, ∑ rho ∈ (input x).layer i,
          pntRelativeZeroContribution x rho :=
    (input x).certificate.sum_decomposition
      (pntRelativeZeroContribution x)
  rw [dynamicPositiveOutsideClusterPNTTailNorm, hdecomp]
  exact norm_sum_le _ _

/-- Finitely many actual outside-cluster Carlson strip certificates aggregate
to target-amplitude negligibility of their layer-norm sum. -/
theorem
    actualZetaFiniteStripsOutsideCluster_layerNormSum_targetAmplitudeNegligible
    {n : ℕ} {S : Finset ℂ} {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma :
      ∀ i x, (input x).sigma i = sigma i)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (halpha : 0 < alpha)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hepsilon : ∀ i, 0 < epsilon i)
    (hmargin :
      ∀ i,
        targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent
              alpha (sigma i)) +
          epsilon i < 0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        ∑ i : Fin n,
          dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) S input i x) := by
  simpa using
    (targetAmplitudeNegligible_finset_sum_of_pintzCarlsonBudgets
      (targetZeroPowerAmplitude_eventually_pos beta)
      (Finset.univ : Finset (Fin n))
      (fun i =>
        dynamicPositiveOutsideClusterPNTLayerNorm
          (carlsonPolynomialHeight alpha) S input i)
      (fun i =>
        dynamicCarlsonLayerCount (sigma i)
          (carlsonPolynomialHeight alpha))
      (fun i =>
        stripEndpointRelativeKernelBudget (kappa i) (tau i))
      (by
        intro i hi
        exact
          actualZetaOutsideClusterStrip_carlsonTargetLayerBudget
            input i (hfixedSigma i)
            (hsigma i) (hsigmaOne i) halpha
            (hkappa i) (hnorm i) (hre i)
            (hepsilon i) (hmargin i)))

/-- A finite family of endpoint-aware Carlson strips controls the complete
positive-ordinate cluster-excluded zeta tail relative to the target power
amplitude. -/
theorem
    actualZetaFiniteStripsOutsideCluster_positiveTail_targetAmplitudeNegligible
    {n : ℕ} {S : Finset ℂ} {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma :
      ∀ i x, (input x).sigma i = sigma i)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (halpha : 0 < alpha)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hepsilon : ∀ i, 0 < epsilon i)
    (hmargin :
      ∀ i,
        targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent
              alpha (sigma i)) +
          epsilon i < 0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  have hsum :=
    actualZetaFiniteStripsOutsideCluster_layerNormSum_targetAmplitudeNegligible
      input sigma tau kappa epsilon hfixedSigma
      hsigma hsigmaOne halpha hkappa hnorm hre hepsilon hmargin
  unfold TargetAmplitudeNegligible at hsum ⊢
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta] with x hx
    exact div_nonneg (abs_nonneg _) hx.le
  · filter_upwards
      [targetZeroPowerAmplitude_eventually_pos beta] with x hx
    have htail :=
      dynamicPositiveOutsideClusterPNTTailNorm_le_sum_layerNorms input x
    have htailNonneg :
        0 ≤ dynamicPositiveOutsideClusterPNTTailNorm
          (carlsonPolynomialHeight alpha) S x :=
      norm_nonneg _
    have hsumNonneg :
        0 ≤ ∑ i : Fin n,
          dynamicPositiveOutsideClusterPNTLayerNorm
            (carlsonPolynomialHeight alpha) S input i x :=
      Finset.sum_nonneg fun i hi => norm_nonneg _
    rw [abs_of_nonneg htailNonneg, abs_of_nonneg hsumNonneg]
    exact div_le_div_of_nonneg_right htail hx.le

end PrimeNumberTheorem
