import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedExponent
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStrips
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroForcingUnifiedTransfer

/-!
# Weighted balanced good-height transfer at natural points

The slope-weighted Carlson optimizer produces an exponent `alphaStar` with

* `0 < alphaStar < 1`;
* `1 - beta < alphaStar`;
* every finite-strip Carlson endpoint exponent strictly negative.

A uniform good height selected in
`[x ^ alphaStar - 1, x ^ alphaStar]` therefore serves both sides of the
explicit formula.  The selected-height Carlson machinery controls the actual
outside-cluster zeta tail, while the natural-point contour theorem controls
the actual explicit-formula remainder.  No separate remainder certificate is
needed.

The visible-cluster far witness remains an explicit input owned by the
independent sharp-oscillation development.
-/

namespace PrimeNumberTheorem

open Filter

/-- Uniform good-height schedule at the slope-weighted balanced exponent. -/
noncomputable def actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  selectedUniformGoodHeight
    (actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau)
    selection x

/-- The weighted optimizer and the uniform short-interval selector construct
the complete actual Carlson certificate at one common good-height schedule. -/
noncomputable def
    actualCarlsonOutsideClusterWeightedBalancedGoodHeightFiniteStripCertificate
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
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
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
      beta
      (actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau)
      S (n + 1)
      (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
        beta sigma tau selection)
      input := by
  let delta :=
    actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  let epsilon : Fin (n + 1) → ℝ := fun _ => delta / 2
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have hdelta : 0 < delta := hspec.1
  have halpha : 0 < alpha := hspec.2.1
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
      alpha_pos := halpha
      kappa_pos := hkappa
      norm_lower := hnorm
      re_upper := hre
      epsilon_pos := ?_
      exponent_margin := ?_
      real_re_lt_beta := hreal }
  · simpa [actualSelectedHeightFiniteStripWeightedBalancedGoodHeight,
      actualCarlsonPolynomialGoodHeightBase, carlsonPolynomialHeight,
      alpha] using
      eventually_selectedUniformGoodHeight_mem halpha selection
  · intro i
    dsimp [epsilon]
    linarith
  · intro i
    have hi :=
      actualSelectedHeightFiniteStripWeightedBalancedExponent_endpointExponent_le
        (beta := beta) sigma tau hsigma hsigmaOne i
    dsimp [epsilon, alpha, delta] at hi ⊢
    linarith

/--
Natural-point Pintz--Carlson--explicit-formula transfer at the physical
slope-weighted optimal height.

The upper PNT decay and lower target-amplitude transfer act on the same
`relativeChebyshevPsi0Error`.  Carlson strip margins, good-height selection,
the actual signed complementary zeta tail, the closed real-axis term, and the
actual contour remainder are all discharged automatically.  Only the
finite-cluster far witness and the explicit strip-cover data remain.
-/
theorem
    unified_parametricPNTUpper_actualWeightedBalancedGoodHeightNaturalLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
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
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have halpha : 0 < alpha := hspec.2.1
  have halphaOne : alpha ≤ 1 := hspec.2.2.1.le
  have hmargin : 1 - beta < alpha := hspec.2.2.2.1
  let carlsonCertificate :=
    actualCarlsonOutsideClusterWeightedBalancedGoodHeightFiniteStripCertificate
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  have remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate beta
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection) := by
    simpa [actualSelectedHeightFiniteStripWeightedBalancedGoodHeight, alpha] using
      selectedUniformGoodHeight_actualNaturalRemainderCertificate
        hbeta halpha halphaOne hmargin selection
  exact
    ⟨exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
        threshold hhalf hlt,
      actualSelectedHeight_naturalPointRemainder_lowerTransfer
        hbeta carlsonCertificate remainderCertificate hmain⟩

end PrimeNumberTheorem
