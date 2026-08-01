import PrimeNumberTheorem.ZeroDensityLayerBudgetArbitraryEpsilonTransfer

/-!
# Arbitrarily sharp same-formula PNT bounds

The arbitrary-epsilon cluster approximation sharpens both sides of the
same-formula transfer:

* the PNT upper coefficient is `C_S + epsilon` for every positive `epsilon`;
* every strict main-cluster threshold `q < c` remains strict for the genuine
  PNT error, by choosing half of the available coefficient gap.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
For every positive `epsilon`, the actual relative PNT error is eventually
bounded by `(C_S + epsilon)` times the target zero-power amplitude.

Here `C_S` is the explicit finite visible-cluster coefficient.  Thus the
previous fixed `C_S + 1/2` bound is sharpened to an arbitrarily small additive
loss without changing the selected height or the zero decomposition.
-/
theorem
    eventually_abs_relativeChebyshevPsi0Error_le_visibleClusterCoefficient_add_epsilon
    {beta epsilon : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hepsilon : 0 < epsilon)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (hclusterRe : ∀ rho ∈ S, rho.re ≤ beta)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        (finiteVisibleClusterPNTAmplitudeCoefficient S + epsilon) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  let H :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
      beta sigma tau selection
  have happroxDirect :=
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_epsilon_mul_targetAmplitude
      hbeta hbetaOne hepsilon sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal
  have happrox :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H S (m : ℝ)| <
          epsilon * targetZeroPowerAmplitude beta (m : ℝ) := by
    simpa [H] using happroxDirect
  filter_upwards [happrox, eventually_ge_atTop (1 : ℕ)] with
      m hsmall hm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hmainBound :
      |dynamicVisibleClusterPNTMain H S (m : ℝ)| ≤
        finiteVisibleClusterPNTAmplitudeCoefficient S *
          targetZeroPowerAmplitude beta (m : ℝ) :=
    abs_dynamicVisibleClusterPNTMain_le_coefficient_mul_target
      H S hmReal hclusterRe
  have htriangle :
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        |dynamicVisibleClusterPNTMain H S (m : ℝ)| +
          |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H S (m : ℝ)| := by
    calc
      |relativeChebyshevPsi0Error (m : ℝ)| =
          |dynamicVisibleClusterPNTMain H S (m : ℝ) +
            (relativeChebyshevPsi0Error (m : ℝ) -
              dynamicVisibleClusterPNTMain H S (m : ℝ))| := by
            congr 1
            ring
      _ ≤
          |dynamicVisibleClusterPNTMain H S (m : ℝ)| +
            |relativeChebyshevPsi0Error (m : ℝ) -
              dynamicVisibleClusterPNTMain H S (m : ℝ)| :=
        abs_add_le _ _
  calc
    |relativeChebyshevPsi0Error (m : ℝ)| ≤
        |dynamicVisibleClusterPNTMain H S (m : ℝ)| +
          |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H S (m : ℝ)| :=
      htriangle
    _ ≤
        finiteVisibleClusterPNTAmplitudeCoefficient S *
            targetZeroPowerAmplitude beta (m : ℝ) +
          epsilon * targetZeroPowerAmplitude beta (m : ℝ) :=
      add_le_add hmainBound hsmall.le
    _ =
        (finiteVisibleClusterPNTAmplitudeCoefficient S + epsilon) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
      ring

/--
Every nonnegative strict threshold below a visible-cluster coefficient remains
a strict threshold for the genuine PNT error.

Given `q < c`, choose the remainder loss `(c - q) / 2`.  The transferred
coefficient is `(c + q) / 2`, which is still strictly larger than `q`.
-/
theorem
    actualWeightedBalancedGoodHeightPNTPreservesStrictOscillationThreshold
    {beta c q : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hq : 0 ≤ q)
    (hqC : q < c)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S
            (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    q < (c + q) / 2 ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => ((c + q) / 2) * targetZeroPowerAmplitude beta x) := by
  have hepsilon : 0 < (c - q) / 2 := by
    nlinarith
  have hepsilonC : (c - q) / 2 < c := by
    nlinarith
  have htransfer :=
    actualWeightedBalancedGoodHeightPNTArbitraryEpsilonSharpConstantTransfer
      hbeta hbetaOne hepsilon hepsilonC sigma tau hsigma hsigmaOne htau
      hthreshold selection input kappa hS hfixedSigma hkappa hnorm hre hreal
      hmain
  have hcoefficient :
      c - (c - q) / 2 = (c + q) / 2 := by
    ring
  exact
    ⟨by nlinarith,
      by simpa only [hcoefficient] using htransfer.2⟩

end PrimeNumberTheorem
