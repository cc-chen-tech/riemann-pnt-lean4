import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTQuantitativeReverseClusterExclusion

/-!
# Sharp natural-point Omega transfer for the actual PNT error

Suppose a visible zero cluster has a natural-point witness with coefficient
`c` at the target zero-power scale.  The arbitrarily small dynamic
Carlson/Pintz explicit-formula remainder then transfers every strict
coefficient `q < c` to the actual relative Chebyshev error.

This file records both standard forms of the conclusion:

* arbitrary far natural points with error at least `q A_beta`;
* failure of every eventual upper bound with coefficient `q < c`.

The visible-cluster witness remains an explicit input.  In particular, these
theorems do not claim that a finite rightmost cluster has already been proved
to possess such a witness.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/--
Every strict coefficient below a visible-cluster natural-point witness survives
transfer to the actual relative Chebyshev error.
-/
theorem actualWeightedBalancedGoodHeightPNTHasFarNaturalPoint_belowClusterConstant
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
      ∀ x,
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm : ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre : ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
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
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m => relativeChebyshevPsi0Error (m : ℝ))
      (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  have hloss : 0 < c - q := sub_pos.mpr hqC
  have happrox :=
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_epsilon_mul_targetAmplitude
      hbeta hbetaOne hloss sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal
  have hcoeff : c - (c - q) = q := by
    ring
  simpa only [hcoeff] using
    hmain.transfer_eventually_sub_lt happrox

/--
For a nonempty visible cluster with coefficient `c`, the actual PNT error
cannot eventually stay below `q A_beta` for any `q < c`.
-/
theorem actualWeightedBalancedGoodHeightPNTNonemptyCluster_not_eventually_le_belowConstant
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
      ∀ x,
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hNonempty : S.Nonempty)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm : ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre : ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
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
    ¬ ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| ≤
          q * targetZeroPowerAmplitude beta (m : ℝ) := by
  intro hupper
  have hEmpty :=
    actualWeightedBalancedGoodHeightPNTEventualUpper_forces_emptyCluster
      hbeta hbetaOne hq hqC sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal hupper
      (fun _ => hmain)
  exact (Finset.nonempty_iff_ne_empty.mp hNonempty) hEmpty

end PrimeNumberTheorem
