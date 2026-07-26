import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightClusterApproximation

/-!
# Sharp-constant transfer through an explicit-formula remainder

This file records the exact constant loss when a main zero-cluster term is
transferred to the genuine PNT error through a pointwise remainder estimate.
It is deliberately independent of how the main-term lower witness is proved.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
If `f` is eventually within `loss * amplitude` of `g`, then every far-point
lower witness for `g` with coefficient `c` transfers to `f` with coefficient
`c - loss`.

No positivity assumptions are needed for this algebraic transfer.  Concrete
applications should separately certify `0 < c - loss` to obtain a nontrivial
lower scale.
-/
theorem
    HasFarNaturalPointTargetAmplitudeWitness.transfer_eventually_sub_lt
    {f g amplitude : ℕ → ℝ}
    {c loss : ℝ}
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        g
        (fun m => c * amplitude m))
    (happrox :
      ∀ᶠ m : ℕ in atTop,
        |f m - g m| < loss * amplitude m) :
    HasFarNaturalPointTargetAmplitudeWitness
      f
      (fun m => (c - loss) * amplitude m) := by
  intro M
  rcases eventually_atTop.1 happrox with ⟨N, hN⟩
  rcases hmain (max M N) with ⟨m, hm, hmainAt⟩
  refine ⟨m, le_trans (le_max_left M N) hm, ?_⟩
  have hNle : N ≤ m := le_trans (le_max_right M N) hm
  have hsmall := hN m hNle
  have hreverse :
      |g m| - |f m| ≤ |g m - f m| :=
    abs_sub_abs_le_abs_sub (g m) (f m)
  have hsmall' :
      |g m - f m| < loss * amplitude m := by
    simpa only [abs_sub_comm] using hsmall
  nlinarith

/--
Sharp-constant transfer from the visible zero cluster to the actual relative
Chebyshev error at the selected weighted balanced good height.

A cluster witness with coefficient `c > 1/2` produces a genuine PNT-error
witness with the strictly positive coefficient `c - 1/2`.  Thus constants
proved by a separate local oscillation theorem are preserved quantitatively,
with exactly the half-amplitude cost of the explicit-formula complement.
-/
theorem
    actualWeightedBalancedGoodHeightPNTSharpConstantTransfer
    {beta c : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hc : 1 / 2 < c)
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
    0 < c - 1 / 2 ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => (c - 1 / 2) * targetZeroPowerAmplitude beta x) := by
  have happrox :=
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_half_targetAmplitude
      hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  have happrox' :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              S
              (m : ℝ)| <
          (1 / 2) * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [happrox] with m hm
    simpa [div_eq_mul_inv, mul_comm] using hm
  have hnatural :=
    hmain.transfer_eventually_sub_lt happrox'
  exact ⟨sub_pos.mpr hc, hnatural.toReal⟩

end PrimeNumberTheorem
