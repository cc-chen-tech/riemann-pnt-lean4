import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualSelectedHeightClusterResidual
import PrimeNumberTheorem.ZeroDensityLayerBudgetArbitraryEpsilonTransfer

/-!
# Sharp transfer from a visible cluster through the actual hybrid PNT chain

The hybrid global/Carlson residual theorem gives an arbitrarily small
target-normalized error between the genuine relative Chebyshev error and the
visible-cluster main term.  Consequently every natural-point cluster witness
with coefficient `c` transfers to every strictly smaller positive coefficient
`q`.

The cluster witness is an explicit hypothesis.  This file does not prove the
localized oscillation theorem that supplies it.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

/-- For every positive epsilon, the genuine relative PNT error tracks the
visible-cluster main term within `epsilon * x^(beta-1)` eventually on natural
points. -/
theorem eventually_actualHybridSelectedHeightClusterResidual_lt_mul
    {beta epsilon : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hepsilon : 0 < epsilon)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (htau : ∀ i, 0 ≤ tau i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (pntHybridAffineSelectedGoodHeight
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
            (pntHybridAffineSelectedGoodHeight
              beta sigma tau selection)
            S (m : ℝ)| <
        epsilon * targetZeroPowerAmplitude beta (m : ℝ) := by
  have hnegligible :=
    actualHybridSelectedHeightClusterResidual_targetNegligible
      hbeta hbetaOne sigma tau htau hsigmaOneHigh hbudget selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  exact
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hnegligible hepsilon

/-- A visible-cluster far witness with coefficient `c` transfers to the
genuine relative PNT error with every prescribed positive coefficient
`q < c`. -/
theorem actualHybridSelectedHeightClusterWitness_transfer_lt
    {beta c q : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hq : 0 < q) (hqc : q < c)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (htau : ∀ i, 0 ≤ tau i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (pntHybridAffineSelectedGoodHeight
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
            (pntHybridAffineSelectedGoodHeight
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
    eventually_actualHybridSelectedHeightClusterResidual_lt_mul
      hbeta hbetaOne hloss sigma tau htau hsigmaOneHigh hbudget
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
