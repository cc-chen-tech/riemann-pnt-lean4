import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStripExponentFeasibility
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightGoodHeightChoice
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStrips

/-!
# Automatic choices in the actual selected-height finite-strip certificate

The actual Carlson finite-strip certificate previously required callers to
choose both a common polynomial exponent and a positive slack for every strip.
Those choices are forced by the endpoint thresholds:

* use the canonical common exponent supplied by finite-strip feasibility;
* if the resulting strip exponent is `E_i < 0`, use `epsilon_i = -E_i / 2`.

The constructor below leaves visible only the genuine analytic and geometric
inputs: the good-height selector, the zero-layer partition, norm lower bounds,
real-part upper endpoints, conjugation symmetry, and the real-axis gap.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace PrimeNumberTheorem

/-- The common exponent selected from all endpoint thresholds. -/
noncomputable def actualSelectedHeightFiniteStripChosenExponent
    (beta : ℝ) {n : ℕ} (sigma tau : Fin n → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) : ℝ :=
  actualSelectedHeightFiniteStripExponent beta sigma tau
    hbeta hbetaOne hsigma hsigmaOne hthreshold

/-- The uniform good-height schedule at the canonically selected common
finite-strip exponent. -/
noncomputable def actualSelectedHeightFiniteStripChosenHeight
    (beta : ℝ) {n : ℕ} (sigma tau : Fin n → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  selectedUniformGoodHeight
    (actualSelectedHeightFiniteStripChosenExponent beta sigma tau
      hbeta hbetaOne hsigma hsigmaOne hthreshold)
    selection x

/-- Half of the available negative exponent gap, used as the automatic
positive strip slack. -/
noncomputable def actualSelectedHeightFiniteStripChosenEpsilon
    (beta : ℝ) {n : ℕ} (sigma tau : Fin n → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (i : Fin n) : ℝ :=
  -targetAmplitudeStripEndpointExponent beta (tau i)
      (carlsonClassicalPolynomialDensityExponent
        (actualSelectedHeightFiniteStripChosenExponent beta sigma tau
          hbeta hbetaOne hsigma hsigmaOne hthreshold)
        (sigma i)) / 2

/-- Endpoint thresholds automatically determine the exponent, selected height,
positive strip slacks, and exponent margins in the actual Carlson finite-strip
certificate. -/
noncomputable def
    actualCarlsonOutsideClusterGoodHeightFiniteStripCertificate_of_thresholds
    {beta : ℝ} {n : ℕ} (sigma tau : Fin n → ℝ)
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
          (actualSelectedHeightFiniteStripChosenHeight beta sigma tau
            hbeta hbetaOne hsigma hsigmaOne hthreshold selection x)
          S n)
    (kappa : Fin n → ℝ)
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
      (actualSelectedHeightFiniteStripChosenExponent beta sigma tau
        hbeta hbetaOne hsigma hsigmaOne hthreshold)
      S n
      (actualSelectedHeightFiniteStripChosenHeight beta sigma tau
        hbeta hbetaOne hsigma hsigmaOne hthreshold selection)
      input := by
  have hspec :=
    actualSelectedHeightFiniteStripExponent_spec beta sigma tau
      hbeta hbetaOne hsigma hsigmaOne hthreshold
  have hdecay :
      ∀ i,
        targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent
            (actualSelectedHeightFiniteStripChosenExponent beta sigma tau
              hbeta hbetaOne hsigma hsigmaOne hthreshold)
            (sigma i)) < 0 := by
    intro i
    simpa [actualSelectedHeightFiniteStripChosenExponent] using
      hspec.2.2.2 i
  let alpha :=
    actualSelectedHeightFiniteStripChosenExponent beta sigma tau
      hbeta hbetaOne hsigma hsigmaOne hthreshold
  let epsilon :=
    actualSelectedHeightFiniteStripChosenEpsilon beta sigma tau
      hbeta hbetaOne hsigma hsigmaOne hthreshold
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
  · simpa [actualSelectedHeightFiniteStripChosenHeight,
      actualSelectedHeightFiniteStripChosenExponent,
      actualCarlsonPolynomialGoodHeightBase,
      carlsonPolynomialHeight] using
      eventually_selectedUniformGoodHeight_mem hspec.1 selection
  · intro i
    have hdecay' := hdecay i
    dsimp [epsilon,
      actualSelectedHeightFiniteStripChosenEpsilon, alpha]
    linarith
  · intro i
    have hdecay' := hdecay i
    dsimp [epsilon,
      actualSelectedHeightFiniteStripChosenEpsilon, alpha]
    linarith

end PrimeNumberTheorem
