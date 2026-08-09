import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightCarlsonTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailExcludingClusterConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualRealOrdinateExcludingCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterSignedComplement
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualOscillationBoundary

/-!
# Finite actual Carlson strips at a selected good height

This module aggregates the selected-height one-strip transfer over a finite
outside-cluster bucket decomposition.  A good height chosen in
`[x^alpha - 1, x^alpha]` is eventually nonnegative and lies below the exact
Carlson polynomial ceiling.  Consequently the same selected height controls
the positive, real-ordinate, and conjugate negative pieces of the actual
finite zeta tail.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

open Filter

/-- A height selected from the unit interval below `x^alpha` is eventually
nonnegative when `alpha` is positive. -/
theorem eventually_selectedHeight_nonneg
    {alpha : ℝ} {H : ℝ → ℝ}
    (halpha : 0 < alpha)
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
          (actualCarlsonPolynomialGoodHeightBase alpha x + 1)) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ H x := by
  filter_upwards [hH, eventually_ge_atTop (1 : ℝ)] with x hxH hx
  calc
    0 ≤ actualCarlsonPolynomialGoodHeightBase alpha x := by
      dsimp [actualCarlsonPolynomialGoodHeightBase,
        carlsonPolynomialHeight]
      exact sub_nonneg.mpr (Real.one_le_rpow hx halpha.le)
    _ ≤ H x := hxH.1

/-- Finitely many selected-height Carlson strip certificates aggregate to
target-amplitude negligibility of the layer-norm sum. -/
theorem
    actualZetaFiniteStripsOutsideCluster_selectedHeight_layerNormSum_negligible
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
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
          dynamicPositiveOutsideClusterPNTLayerNorm H S input i x) := by
  simpa using
    (targetAmplitudeNegligible_finset_sum_of_pintzCarlsonBudgets
      (targetZeroPowerAmplitude_eventually_pos beta)
      (Finset.univ : Finset (Fin n))
      (fun i =>
        dynamicPositiveOutsideClusterPNTLayerNorm H S input i)
      (fun i => dynamicCarlsonLayerCount (sigma i) H)
      (fun i =>
        stripEndpointRelativeKernelBudget (kappa i) (tau i))
      (by
        intro i hi
        exact
          actualZetaOutsideClusterStrip_selectedHeight_carlsonTargetLayerBudget
            input i (hfixedSigma i) hH
            (hsigma i) (hsigmaOne i) halpha
            (hkappa i) (hnorm i) (hre i)
            (hepsilon i) (hmargin i)))

/-- The selected-height finite strip family controls the complete positive
outside-cluster zeta tail. -/
theorem
    actualZetaFiniteStripsOutsideCluster_selectedHeight_positiveTail_negligible
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta alpha : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
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
      (dynamicPositiveOutsideClusterPNTTailNorm H S) := by
  have hsum :=
    actualZetaFiniteStripsOutsideCluster_selectedHeight_layerNormSum_negligible
      input sigma tau kappa epsilon hfixedSigma hH
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
        0 ≤ dynamicPositiveOutsideClusterPNTTailNorm H S x :=
      norm_nonneg _
    have hsumNonneg :
        0 ≤ ∑ i : Fin n,
          dynamicPositiveOutsideClusterPNTLayerNorm H S input i x :=
      Finset.sum_nonneg fun i hi => norm_nonneg _
    rw [abs_of_nonneg htailNonneg, abs_of_nonneg hsumNonneg]
    exact div_le_div_of_nonneg_right htail hx.le

/-- Selected-height finite strips, conjugation, and the real-axis gap control
the complete actual outside-cluster zeta tail. -/
theorem
    actualZetaFiniteStripsOutsideCluster_selectedHeight_fullTail_negligible
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta alpha : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
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
          epsilon i < 0)
    (hreal :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm H S) := by
  apply
    dynamicFullOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      hS (targetZeroPowerAmplitude_eventually_pos beta)
  · exact
      actualZetaFiniteStripsOutsideCluster_selectedHeight_positiveTail_negligible
        input sigma tau kappa epsilon hfixedSigma hH
        hsigma hsigmaOne halpha hkappa hnorm hre hepsilon hmargin
  · exact
      dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
        H S beta hHnonneg hreal

/-- Good-height interval specialization of the complete selected-height tail
estimate. -/
theorem
    actualZetaFiniteStripsOutsideCluster_goodHeight_fullTail_negligible
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta alpha : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (sigma tau kappa epsilon : Fin n → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
          (actualCarlsonPolynomialGoodHeightBase alpha x + 1))
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
          epsilon i < 0)
    (hreal :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm H S) :=
  actualZetaFiniteStripsOutsideCluster_selectedHeight_fullTail_negligible
    hS input sigma tau kappa epsilon hfixedSigma
    (eventually_selectedHeight_le_carlsonPolynomialHeight hH)
    (eventually_selectedHeight_nonneg halpha hH)
    hsigma hsigmaOne halpha hkappa hnorm hre hepsilon hmargin hreal

/-- Auditable finite-strip certificate at one selected good-height function. -/
structure ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
    (beta alpha : ℝ) (S : Finset ℂ) (n : ℕ) (H : ℝ → ℝ)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n) : Type where
  sigma : Fin n → ℝ
  tau : Fin n → ℝ
  kappa : Fin n → ℝ
  epsilon : Fin n → ℝ
  conjugation_invariant : IsConjugationInvariantCluster S
  height_interval :
    ∀ᶠ x : ℝ in atTop,
      H x ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
        (actualCarlsonPolynomialGoodHeightBase alpha x + 1)
  fixed_sigma : ∀ i x, (input x).sigma i = sigma i
  sigma_half : ∀ i, 1 / 2 < sigma i
  sigma_one : ∀ i, sigma i < 1
  alpha_pos : 0 < alpha
  kappa_pos : ∀ i, 0 < kappa i
  norm_lower :
    ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖
  re_upper :
    ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i
  epsilon_pos : ∀ i, 0 < epsilon i
  exponent_margin :
    ∀ i,
      targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent
            alpha (sigma i)) +
        epsilon i < 0
  real_re_lt_beta :
    ∀ rho ∈
      realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta

/-- The selected-good-height certificate controls the complete actual zeta
tail outside the main cluster. -/
theorem
    ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate.fullTail_negligible
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ} {H : ℝ → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha S n H input) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm H S) :=
  actualZetaFiniteStripsOutsideCluster_goodHeight_fullTail_negligible
    certificate.conjugation_invariant input
    certificate.sigma certificate.tau
    certificate.kappa certificate.epsilon
    certificate.fixed_sigma certificate.height_interval
    certificate.sigma_half certificate.sigma_one
    certificate.alpha_pos certificate.kappa_pos
    certificate.norm_lower certificate.re_upper
    certificate.epsilon_pos certificate.exponent_margin
    certificate.real_re_lt_beta

/-- Domination by the complete selected-height tail supplies the signed
complement certificate used by the unified oscillation transfer. -/
theorem
    ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate.signedComplementCertificate
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ} {H : ℝ → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha S n H input)
    (complement : ℝ → ℝ)
    (hdominated :
      ∀ᶠ x in atTop,
        |complement x| ≤
          dynamicFullOutsideClusterPNTZeroTailNorm H S x) :
    ClusterExcludedTargetComplementCertificate
      (targetZeroPowerAmplitude beta) complement
      (dynamicFullOutsideClusterPNTZeroTailNorm H S) where
  amplitude_eventually_pos :=
    targetZeroPowerAmplitude_eventually_pos beta
  complement_dominated := hdominated
  excluded_tail_negligible := certificate.fullTail_negligible

/-- The actual signed outside-cluster zero complement is automatically
dominated by the complete selected-height tail. -/
theorem
    ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate.actualSignedComplementCertificate
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ} {H : ℝ → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha S n H input) :
    ClusterExcludedTargetComplementCertificate
      (targetZeroPowerAmplitude beta)
      (dynamicOutsideClusterPNTComplement H S)
      (dynamicFullOutsideClusterPNTZeroTailNorm H S) := by
  apply certificate.signedComplementCertificate
  exact Eventually.of_forall fun x =>
    abs_dynamicOutsideClusterPNTComplement_le_tailNorm H S x

end PrimeNumberTheorem
