import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightBalancedExponent
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightGoodHeightChoice
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStrips

/-!
# Actual finite-strip certificates at the explicit balanced exponent

This module realizes the explicit balanced exponent as an actual selected
good-height schedule.  The strict Carlson margin again supplies an automatic
positive slack equal to half of the available negative exponent.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace PrimeNumberTheorem

/-- Uniform good-height schedule at the explicit balanced finite-strip
exponent. -/
noncomputable def actualSelectedHeightFiniteStripBalancedHeight
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  selectedUniformGoodHeight
    (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau)
    selection x

/-- Automatic positive slack at the explicit balanced exponent. -/
noncomputable def actualSelectedHeightFiniteStripBalancedEpsilon
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  -targetAmplitudeStripEndpointExponent beta (tau i)
      (carlsonClassicalPolynomialDensityExponent
        (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau)
        (sigma i)) / 2

/-- Endpoint thresholds and genuine zero-layer geometry construct the actual
Carlson certificate at the explicit balanced truncation exponent. -/
noncomputable def
    actualCarlsonOutsideClusterBalancedGoodHeightFiniteStripCertificate
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripBalancedHeight
            beta sigma tau selection x)
          S (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
      beta
      (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau)
      S (n + 1)
      (actualSelectedHeightFiniteStripBalancedHeight
        beta sigma tau selection)
      input := by
  have hspec :=
    actualSelectedHeightFiniteStripBalancedExponent_spec
      sigma tau hbeta hbetaOne hsigma hsigmaOne hthreshold
  let alpha :=
    actualSelectedHeightFiniteStripBalancedExponent beta sigma tau
  let epsilon :=
    actualSelectedHeightFiniteStripBalancedEpsilon beta sigma tau
  refine
    { sigma := sigma
      tau := tau
      kappa := kappa
      epsilon := epsilon
      conjugation_invariant := hS
      height_interval := ?_
      fixed_sigma := hfixedSigma
      sigma_half := hsigma
      sigma_one := hsigmaOne
      alpha_pos := hspec.1
      kappa_pos := hkappa
      norm_lower := hnorm
      re_upper := hre
      epsilon_pos := ?_
      exponent_margin := ?_
      real_re_lt_beta := hreal }
  · simpa [actualSelectedHeightFiniteStripBalancedHeight,
      actualCarlsonPolynomialGoodHeightBase,
      carlsonPolynomialHeight] using
      eventually_selectedUniformGoodHeight_mem hspec.1 selection
  · intro i
    have hdecay := hspec.2.2.2.2.1 i
    dsimp [epsilon,
      actualSelectedHeightFiniteStripBalancedEpsilon, alpha]
    linarith
  · intro i
    have hdecay := hspec.2.2.2.2.1 i
    dsimp [epsilon,
      actualSelectedHeightFiniteStripBalancedEpsilon, alpha]
    linarith

end PrimeNumberTheorem
