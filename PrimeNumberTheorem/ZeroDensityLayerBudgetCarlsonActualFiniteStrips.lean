import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualStripTransfer

/-!
# Finite aggregation of actual Carlson zeta strips

A finite real-part decomposition may use distinct lower count thresholds,
upper kernel endpoints, denominator guards, and exponent margins.  This file
aggregates the actual single-strip certificates and transfers their normalized
decay to the complete positive-ordinate finite zero sum.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

open Filter

/-- Norm of the complete positive-ordinate relative PNT zero sum at a dynamic
height. -/
noncomputable def dynamicPositivePNTTailNorm
    (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  ‖∑ rho ∈ positiveNontrivialZerosFinset (T x),
      pntRelativeZeroContribution x rho‖

/-- The complete positive tail is pointwise dominated by the sum of the norms
of any exhaustive bucket decomposition. -/
theorem dynamicPositivePNTTailNorm_le_sum_layerNorms
    {n : ℕ} {T : ℝ → ℝ}
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) n)
    (x : ℝ) :
    dynamicPositivePNTTailNorm T x ≤
      ∑ i : Fin n, dynamicPositivePNTLayerNorm T input i x := by
  have hdecomp :
      (∑ rho ∈ positiveNontrivialZerosFinset (T x),
          pntRelativeZeroContribution x rho) =
        ∑ i : Fin n, ∑ rho ∈ (input x).layer i,
          pntRelativeZeroContribution x rho :=
    (input x).certificate.sum_decomposition
      (pntRelativeZeroContribution x)
  rw [dynamicPositivePNTTailNorm, hdecomp]
  exact norm_sum_le _ _

/-- A target power amplitude is eventually strictly positive. -/
theorem targetZeroPowerAmplitude_eventually_pos
    (beta : ℝ) :
    ∀ᶠ x in Filter.atTop, 0 < targetZeroPowerAmplitude beta x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact Real.rpow_pos_of_pos hx _

/-- Finitely many actual Carlson zeta-strip certificates aggregate to
target-amplitude negligibility of the sum of their layer norms. -/
theorem actualZetaFiniteStrips_layerNormSum_targetAmplitudeNegligible
    {n : ℕ} {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput (carlsonPolynomialHeight alpha x) n)
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
          dynamicPositivePNTLayerNorm
            (carlsonPolynomialHeight alpha) input i x) := by
  simpa using
    (targetAmplitudeNegligible_finset_sum_of_pintzCarlsonBudgets
      (targetZeroPowerAmplitude_eventually_pos beta)
      (Finset.univ : Finset (Fin n))
      (fun i =>
        dynamicPositivePNTLayerNorm
          (carlsonPolynomialHeight alpha) input i)
      (fun i =>
        dynamicCarlsonLayerCount (sigma i)
          (carlsonPolynomialHeight alpha))
      (fun i => stripEndpointRelativeKernelBudget (kappa i) (tau i))
      (by
        intro i hi
        exact actualZetaStrip_carlsonTargetLayerBudget
          input i (hfixedSigma i)
          (hsigma i) (hsigmaOne i) halpha
          (hkappa i) (hnorm i) (hre i)
          (hepsilon i) (hmargin i)))

/-- A finite family of endpoint-aware Carlson strips controls the complete
positive-ordinate finite zeta tail relative to the target power amplitude. -/
theorem actualZetaFiniteStrips_positiveTail_targetAmplitudeNegligible
    {n : ℕ} {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput (carlsonPolynomialHeight alpha x) n)
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
      (dynamicPositivePNTTailNorm
        (carlsonPolynomialHeight alpha)) := by
  have hsum :=
    actualZetaFiniteStrips_layerNormSum_targetAmplitudeNegligible
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
      dynamicPositivePNTTailNorm_le_sum_layerNorms input x
    have htailNonneg :
        0 ≤ dynamicPositivePNTTailNorm
          (carlsonPolynomialHeight alpha) x := by
      exact norm_nonneg _
    have hsumNonneg :
        0 ≤ ∑ i : Fin n,
          dynamicPositivePNTLayerNorm
            (carlsonPolynomialHeight alpha) input i x := by
      exact Finset.sum_nonneg fun i hi => norm_nonneg _
    rw [abs_of_nonneg htailNonneg, abs_of_nonneg hsumNonneg]
    exact div_le_div_of_nonneg_right htail hx.le

end PrimeNumberTheorem
