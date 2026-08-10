import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualSelectedHeightClusterResidual
import PrimeNumberTheorem.ZeroDensityLayerBudgetArbitraryEpsilonTransfer

/-!
# Arbitrarily sharp transfer from an actual visible zero cluster

The coefficient-aware Carlson chain proves that the actual relative PNT
error differs from the visible-cluster main term by `o(x^(beta-1))` on
natural points.  This module exposes the two direct consumer interfaces:

* every positive epsilon eventually bounds the actual cluster residual;
* a main-term far witness with coefficient `c` transfers to every strictly
  smaller positive coefficient `q`.

The main-term witness remains an external input.  In particular, this module
does not prove a localized oscillation theorem or any specific sharp
constant.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

/-- The actual relative PNT error tracks the visible-cluster main term within
`epsilon * x^(beta-1)` for every positive `epsilon`. -/
theorem
    eventually_actualSelectedHeightWeightedBalancedClusterResidual_lt_mul
    {beta epsilon : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hepsilon : 0 < epsilon)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
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
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S (m : ℝ)| <
        epsilon * targetZeroPowerAmplitude beta (m : ℝ) := by
  have hnegligible :=
    actualSelectedHeightWeightedBalancedClusterResidual_targetNegligible
      hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  exact
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hnegligible hepsilon

/-- A visible-cluster far witness with coefficient `c` transfers to the
actual relative PNT error with every prescribed positive coefficient `q<c`.
Thus the coefficient loss can be made arbitrarily small. -/
theorem
    actualSelectedHeightWeightedBalancedClusterWitness_transfer_lt
    {beta c q : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hq : 0 < q) (hqc : q < c)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
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
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarTargetAmplitudeWitness
      relativeChebyshevPsi0Error
      (fun x : ℝ =>
        q * targetZeroPowerAmplitude beta x) := by
  have hloss : 0 < c - q := sub_pos.mpr hqc
  have happrox :=
    eventually_actualSelectedHeightWeightedBalancedClusterResidual_lt_mul
      hbeta hbetaOne hloss sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal
  have hnatural :=
    hmain.transfer_eventually_sub_lt happrox
  have hnaturalQ :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        (fun m : ℕ =>
          q * targetZeroPowerAmplitude beta (m : ℝ)) := by
    convert hnatural using 1 <;> ext m <;> ring
  exact hnaturalQ.toReal

end PrimeNumberTheorem
