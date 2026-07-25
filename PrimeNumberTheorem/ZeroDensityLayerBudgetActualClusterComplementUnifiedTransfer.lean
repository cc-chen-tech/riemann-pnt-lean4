import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailExcludingClusterConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualRealOrdinateExcludingCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualExplicitFormulaClusterDecomposition
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualOscillationBoundary

/-!
# Actual cluster-excluded Carlson complement in the unified PNT transfer

This module packages the concrete finite-strip hypotheses for the actual zeta
tail outside a conjugation-invariant main cluster.  The package constructs the
normalized full-tail estimate, transfers it to a signed complementary term by
an explicit domination hypothesis, and feeds that result into the common PNT
upper/lower transfer theorem.
-/

namespace PrimeNumberTheorem

open Filter

/-- Auditable finite-strip data controlling the actual zeta tail outside a
fixed conjugation-invariant main cluster. -/
structure ActualCarlsonOutsideClusterFiniteStripCertificate
    (beta alpha : ℝ) (S : Finset ℂ) (n : ℕ)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n) : Type where
  sigma : Fin n → ℝ
  tau : Fin n → ℝ
  kappa : Fin n → ℝ
  epsilon : Fin n → ℝ
  conjugation_invariant : IsConjugationInvariantCluster S
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

/-- The concrete outside-cluster Carlson certificate controls the complete
finite zeta tail outside the main cluster. -/
theorem
    ActualCarlsonOutsideClusterFiniteStripCertificate.fullTail_negligible
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate
        beta alpha S n input) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  exact
    actualZetaFiniteStripsOutsideCluster_fullTail_targetAmplitudeNegligible
      certificate.conjugation_invariant input
      certificate.sigma certificate.tau
      certificate.kappa certificate.epsilon
      certificate.fixed_sigma certificate.sigma_half
      certificate.sigma_one certificate.alpha_pos
      certificate.kappa_pos certificate.norm_lower
      certificate.re_upper certificate.epsilon_pos
      certificate.exponent_margin
      (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_carlsonPolynomial_negligible
        certificate.real_re_lt_beta)

/-- Domination by the actual full outside-cluster tail converts a signed
complement into the safe certificate required by oscillation transfer. -/
theorem
    ActualCarlsonOutsideClusterFiniteStripCertificate.signedComplementCertificate
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate
        beta alpha S n input)
    (complement : ℝ → ℝ)
    (hdominated :
      ∀ᶠ x in atTop,
        |complement x| ≤
          dynamicFullOutsideClusterPNTZeroTailNorm
            (carlsonPolynomialHeight alpha) S x) :
    ClusterExcludedTargetComplementCertificate
      (targetZeroPowerAmplitude beta) complement
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (carlsonPolynomialHeight alpha) S) where
  amplitude_eventually_pos :=
    targetZeroPowerAmplitude_eventually_pos beta
  complement_dominated := hdominated
  excluded_tail_negligible := certificate.fullTail_negligible

/-- The concrete real part of the actual outside-cluster zeta sum supplies the
signed complement certificate without any external domination hypothesis. -/
theorem
    ActualCarlsonOutsideClusterFiniteStripCertificate.actualSignedComplementCertificate
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate
        beta alpha S n input) :
    ClusterExcludedTargetComplementCertificate
      (targetZeroPowerAmplitude beta)
      (dynamicOutsideClusterPNTComplement
        (carlsonPolynomialHeight alpha) S)
      (dynamicFullOutsideClusterPNTZeroTailNorm
        (carlsonPolynomialHeight alpha) S) := by
  apply certificate.signedComplementCertificate
  exact Filter.Eventually.of_forall fun x =>
    abs_dynamicOutsideClusterPNTComplement_le_tailNorm
      (carlsonPolynomialHeight alpha) S x

/--
Concrete unified transfer using actual zeta zeros outside the main cluster.

All Carlson, Pintz-kernel, multiplicity, finite-strip, and conjugation work is
discharged by `certificate`.  The remaining hypotheses are precisely:

* the signed explicit-formula complement is dominated by that actual tail;
* real-axis and contour terms are target-negligible;
* the finite main cluster has a far target-amplitude witness;
* all pieces decompose the actual relative Chebyshev error.
-/
theorem
    unified_parametricPNTUpper_actualCarlsonOutsideClusterLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate
        beta alpha S n input)
    {main realAxis contour complement : ℝ → ℝ}
    (hcomplementDominated :
      ∀ᶠ x in atTop,
        |complement x| ≤
          dynamicFullOutsideClusterPNTZeroTailNorm
            (carlsonPolynomialHeight alpha) S x)
    (hrealAxis :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta) realAxis)
    (hcontour :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta) contour)
    (hmain :
      HasFarTargetAmplitudeWitness main
        (targetZeroPowerAmplitude beta))
    (hdecomp :
      ∀ x : ℝ,
        relativeChebyshevPsi0Error x =
          main x + (realAxis x + contour x + complement x)) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  exact
    unified_parametricPNTUpper_clusterExcludedComplementLower
      threshold hhalf hlt
      (certificate.signedComplementCertificate
        complement hcomplementDominated)
      hrealAxis hcontour hmain hdecomp

/--
Concrete specialization in which the complementary-zero term is the real part
of the actual zeta zero sum outside `S`; its norm domination is automatic.
-/
theorem
    unified_parametricPNTUpper_actualCarlsonSignedComplementLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate
        beta alpha S n input)
    {realAxis contour : ℝ → ℝ}
    (hrealAxis :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta) realAxis)
    (hcontour :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta) contour)
    (hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain
          (carlsonPolynomialHeight alpha) S)
        (targetZeroPowerAmplitude beta))
    (hdecomp :
      ∀ x : ℝ,
        relativeChebyshevPsi0Error x =
          dynamicVisibleClusterPNTMain
              (carlsonPolynomialHeight alpha) S x +
            (realAxis x + contour x +
              dynamicOutsideClusterPNTComplement
                (carlsonPolynomialHeight alpha) S x)) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  exact
    unified_parametricPNTUpper_clusterExcludedComplementLower
      threshold hhalf hlt
      certificate.actualSignedComplementCertificate
      hrealAxis hcontour hmain hdecomp

/-- The fully concrete lower-transfer facade: the signed complement and exact
decomposition are derived from the actual finite-height explicit formula.
The remaining hypotheses are the two target-normalized residual estimates and
a far witness for the visible main cluster. -/
theorem
    unified_parametricPNTUpper_actualExplicitFormulaSignedComplementLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta alpha : ℝ} {S : Finset ℂ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n}
    (certificate :
      ActualCarlsonOutsideClusterFiniteStripCertificate
        beta alpha S n input)
    (hclosed :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        actualPNTClosedRealAxisRelativeTerm)
    (hremainder :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (actualPNTExplicitFormulaRelativeRemainder
          (carlsonPolynomialHeight alpha)))
    (hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain
          (carlsonPolynomialHeight alpha) S)
        (targetZeroPowerAmplitude beta)) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  apply unified_parametricPNTUpper_actualCarlsonSignedComplementLower
    threshold hhalf hlt certificate hclosed hremainder hmain
  intro x
  exact
    relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
      (carlsonPolynomialHeight alpha) S x

end PrimeNumberTheorem
