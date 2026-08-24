import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffineActualSelectedHeightCoefficient
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay

/-!
# Full normalized Carlson budget at the selected good height

At the slope-weighted selected good height, two independently constructed
actual quantities are negligible on the same natural samples:

* the multiplicity-weighted finite-strip zeta norm sum, by Carlson density
  with the optimized affine coefficient majorant;
* the actual explicit-formula contour and closed-log remainder.

Their sum is therefore negligible relative to the target zero amplitude.
This is a quantitative residual budget, not an assertion that the supplied
finite bucket family covers every zeta zero.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

/-- The actual finite-strip norm budget and the actual explicit-formula
remainder are jointly negligible relative to the target zero amplitude at
natural points, using one weighted selected good-height schedule. -/
theorem
    tendsto_actualSelectedHeightWeightedBalancedFullNormalizedBudget_zero
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    let H :=
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
        beta sigma tau selection
    Tendsto
      (fun m : ℕ =>
        actualCarlsonFiniteStripNormalizedLayerNormSum
            H input beta (m : ℝ) +
          |actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ))
      atTop (nhds 0) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  let H :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
      beta sigma tau selection
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have halpha : 0 < alpha := hspec.2.1
  have halphaOne : alpha ≤ 1 := hspec.2.2.1.le
  have hmargin : 1 - beta < alpha := hspec.2.2.2.1
  have hstripReal :
      Tendsto
        (actualCarlsonFiniteStripNormalizedLayerNormSum H input beta)
        atTop (nhds 0) := by
    simpa [H] using
      tendsto_actualSelectedHeightWeightedBalancedNormalizedLayerNormSum_zero
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
        input kappa hfixedSigma hkappa hnorm hre
  have hstripNat :
      Tendsto
        (fun m : ℕ =>
          actualCarlsonFiniteStripNormalizedLayerNormSum
            H input beta (m : ℝ))
        atTop (nhds 0) :=
    hstripReal.comp tendsto_natCast_atTop_atTop
  have hremainder :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)) := by
    change
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder
            (selectedUniformGoodHeight alpha selection) (m : ℝ))
    exact (selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hmargin selection).negligible
  simpa only [add_zero] using hstripNat.add hremainder

end PrimeNumberTheorem
