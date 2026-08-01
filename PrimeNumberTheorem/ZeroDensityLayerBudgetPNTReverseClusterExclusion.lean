import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPNTZeroClusterDichotomy

/-!
# Reverse PNT transfer: target-scale error excludes a visible zero cluster

The forward transfer machine sends a visible-cluster oscillation witness to the
actual relative Chebyshev error.  This file records the converse obstruction:
an actual PNT error that is negligible at the target zero-power scale cannot
support a positive-proportion far-point witness at that scale.

Combining this elementary incompatibility with the arbitrarily sharp
same-formula approximation gives a conditional reverse theorem.  If a nonempty
visible cluster would have a positive natural-point oscillation witness, then
target-scale negligibility of the actual PNT error forces that cluster to be
empty.

This does not construct the cluster witness and does not assert a new
zero-free region.  It isolates the exact reverse-transfer interface needed from
a sharp oscillation theorem.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/-- The target zero-power amplitude is eventually positive on natural points. -/
theorem eventually_targetZeroPowerAmplitude_natural_pos (beta : ℝ) :
    ∀ᶠ m : ℕ in atTop, 0 < targetZeroPowerAmplitude beta (m : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  rw [targetZeroPowerAmplitude]
  apply Real.rpow_pos_of_pos
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)

/--
A remainder negligible relative to an eventually positive amplitude cannot
have a positive-proportion far natural-point witness.
-/
theorem NaturalPointTargetAmplitudeNegligible.not_hasFarNaturalPoint_mul
    {amplitude remainder : ℕ → ℝ}
    (hnegligible : NaturalPointTargetAmplitudeNegligible amplitude remainder)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    {c : ℝ}
    (hc : 0 < c) :
    ¬ HasFarNaturalPointTargetAmplitudeWitness
        remainder
        (fun m => c * amplitude m) := by
  intro hfar
  have hsmall := hnegligible.eventually_abs_lt_mul hamplitude hc
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  obtain ⟨m, hmM, hmLower⟩ := hfar M
  exact (not_lt_of_ge hmLower) (hM m hmM)

/--
Reverse dynamic-height transfer for the actual PNT error.

Assume the actual relative Chebyshev error is `o(x^(beta-1))`.  If every
nonempty instance of the supplied visible cluster has a positive-proportion
natural-point witness, then the cluster must be empty.  The proof transfers
that witness with loss `c/2` through the same explicit-formula decomposition
and contradicts target-scale negligibility.
-/
theorem actualWeightedBalancedGoodHeightPNTErrorNegligible_forces_emptyCluster
    {beta c : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hc : 0 < c)
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
    (herror :
      NaturalPointTargetAmplitudeNegligible
        (fun m => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m => relativeChebyshevPsi0Error (m : ℝ)))
    (hmain :
      S.Nonempty →
        HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              S
              (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    S = ∅ := by
  by_contra hEmpty
  have hNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hhalfPos : 0 < c / 2 := half_pos hc
  have hhalfLt : c / 2 < c := half_lt_self hc
  have happrox :=
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_epsilon_mul_targetAmplitude
      hbeta hbetaOne hhalfPos sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal
  have hwitness :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => (c - c / 2) * targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmain hNonempty).transfer_eventually_sub_lt happrox
  exact
    (herror.not_hasFarNaturalPoint_mul
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      (sub_pos.mpr hhalfLt))
      hwitness

end PrimeNumberTheorem
