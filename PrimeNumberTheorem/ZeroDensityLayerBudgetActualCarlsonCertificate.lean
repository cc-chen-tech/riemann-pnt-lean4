import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTwoHeightTail

/-!
# Certificates for actual finite-strip Carlson transfer

This file packages the concrete data required to turn a finite dynamic
real-part decomposition of actual zeta zeros into target-amplitude control.
Unlike the earlier abstract layer interface, the certificate does not contain
a pointwise kernel hypothesis or a normalized-limit hypothesis: those are
derived from the strip endpoints, denominator guards, Carlson's theorem, and
strict exponent margins.

The real-ordinate residual remains a separate certificate field because the
positive-height Carlson count does not cover it.
-/

namespace PrimeNumberTheorem

/-- Auditable finite-strip data at one polynomial dynamic height. -/
structure ActualCarlsonFiniteStripCertificate
    (beta alpha : ℝ) (n : ℕ)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput (carlsonPolynomialHeight alpha x) n) :
    Type where
  /-- Fixed lower thresholds used in Carlson's zero count. -/
  sigma : Fin n → ℝ
  /-- Upper real-part endpoints used in the explicit-formula kernel bounds. -/
  tau : Fin n → ℝ
  /-- Explicit lower bounds for the zero denominators in each strip. -/
  kappa : Fin n → ℝ
  /-- Positive margins absorbing Carlson's logarithmic fourth power. -/
  epsilon : Fin n → ℝ
  /-- Dynamic buckets use the fixed Carlson threshold assigned to their
  index. -/
  fixed_sigma :
    ∀ i x, (input x).sigma i = sigma i
  /-- Carlson's classical density range, lower endpoint. -/
  sigma_half :
    ∀ i, 1 / 2 < sigma i
  /-- Carlson's classical density range, upper endpoint. -/
  sigma_one :
    ∀ i, sigma i < 1
  /-- The polynomial height tends to infinity. -/
  alpha_pos :
    0 < alpha
  /-- Every denominator guard is positive. -/
  kappa_pos :
    ∀ i, 0 < kappa i
  /-- Actual zeros assigned to a strip satisfy its denominator guard. -/
  norm_lower :
    ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖
  /-- Actual zeros assigned to a strip lie below its upper real-part
  endpoint. -/
  re_upper :
    ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i
  /-- Every logarithmic absorption margin is positive. -/
  epsilon_pos :
    ∀ i, 0 < epsilon i
  /-- Endpoint-aware Carlson exponent has a strict negative margin in every
  strip. -/
  exponent_margin :
    ∀ i,
      targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) +
        epsilon i < 0
  /-- Real-ordinate zeros, not counted by Carlson, are controlled separately. -/
  real_residual_negligible :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicRealOrdinatePNTZeroTailNorm
        (carlsonPolynomialHeight alpha))

/-- A concrete finite-strip certificate controls the complete positive-height
finite zero tail. -/
theorem ActualCarlsonFiniteStripCertificate.positiveTail_negligible
    {beta alpha : ℝ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroBucketInput (carlsonPolynomialHeight alpha x) n}
    (certificate :
      ActualCarlsonFiniteStripCertificate beta alpha n input) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositivePNTTailNorm
        (carlsonPolynomialHeight alpha)) := by
  exact actualZetaFiniteStrips_positiveTail_targetAmplitudeNegligible
    input certificate.sigma certificate.tau certificate.kappa
    certificate.epsilon certificate.fixed_sigma
    certificate.sigma_half certificate.sigma_one
    certificate.alpha_pos certificate.kappa_pos
    certificate.norm_lower certificate.re_upper
    certificate.epsilon_pos certificate.exponent_margin

/-- A concrete finite-strip certificate, including its explicit real residual,
controls the complete finite zeta zero tail. -/
theorem ActualCarlsonFiniteStripCertificate.fullTail_negligible
    {beta alpha : ℝ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroBucketInput (carlsonPolynomialHeight alpha x) n}
    (certificate :
      ActualCarlsonFiniteStripCertificate beta alpha n input) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullPNTZeroTailNorm
        (carlsonPolynomialHeight alpha)) := by
  exact dynamicFullPNTZeroTailNorm_targetAmplitudeNegligible
    (targetZeroPowerAmplitude_eventually_pos beta)
    certificate.positiveTail_negligible
    certificate.real_residual_negligible

/-- Two independently certified polynomial heights automatically provide the
actual two-height complementary zero-tail control used by the unified
transfer layer. -/
theorem actualCarlsonTwoHeightPNTZeroTailControl
    {beta innerAlpha outerAlpha : ℝ}
    {innerCount outerCount : ℕ}
    {innerInput :
      (x : ℝ) →
        PositiveZeroBucketInput
          (carlsonPolynomialHeight innerAlpha x) innerCount}
    {outerInput :
      (x : ℝ) →
        PositiveZeroBucketInput
          (carlsonPolynomialHeight outerAlpha x) outerCount}
    (innerCertificate :
      ActualCarlsonFiniteStripCertificate
        beta innerAlpha innerCount innerInput)
    (outerCertificate :
      ActualCarlsonFiniteStripCertificate
        beta outerAlpha outerCount outerInput) :
    TwoHeightTargetComplementControl
      (targetZeroPowerAmplitude beta)
      (dynamicFullPNTZeroTailNorm
        (carlsonPolynomialHeight innerAlpha))
      (dynamicPNTZeroHeightAnnulusNorm
        (carlsonPolynomialHeight innerAlpha)
        (carlsonPolynomialHeight outerAlpha)) := by
  exact actualTwoHeightPNTZeroTailControl
    (targetZeroPowerAmplitude_eventually_pos beta)
    innerCertificate.fullTail_negligible
    outerCertificate.fullTail_negligible

/-- The complete actual two-height zero-tail norm budget associated with two
Carlson certificates is negligible relative to the target power amplitude. -/
theorem actualCarlsonTwoHeightPNTZeroTail_combined_negligible
    {beta innerAlpha outerAlpha : ℝ}
    {innerCount outerCount : ℕ}
    {innerInput :
      (x : ℝ) →
        PositiveZeroBucketInput
          (carlsonPolynomialHeight innerAlpha x) innerCount}
    {outerInput :
      (x : ℝ) →
        PositiveZeroBucketInput
          (carlsonPolynomialHeight outerAlpha x) outerCount}
    (innerCertificate :
      ActualCarlsonFiniteStripCertificate
        beta innerAlpha innerCount innerInput)
    (outerCertificate :
      ActualCarlsonFiniteStripCertificate
        beta outerAlpha outerCount outerInput) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (twoHeightComplement
        (dynamicFullPNTZeroTailNorm
          (carlsonPolynomialHeight innerAlpha))
        (dynamicPNTZeroHeightAnnulusNorm
          (carlsonPolynomialHeight innerAlpha)
          (carlsonPolynomialHeight outerAlpha))) :=
  (actualCarlsonTwoHeightPNTZeroTailControl
    innerCertificate outerCertificate).combined_negligible

end PrimeNumberTheorem
