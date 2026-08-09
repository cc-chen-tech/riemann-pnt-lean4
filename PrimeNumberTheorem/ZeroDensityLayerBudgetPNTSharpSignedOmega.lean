import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSharpNaturalOmega

/-!
# Sharp signed Omega transfer for the actual PNT error

Absolute-value oscillation does not by itself provide `Omega_+` or `Omega_-`.
This file therefore introduces separate positive and negative natural-point
witnesses and transfers each one through the same explicit-formula remainder
bound.

If the visible cluster supplies both signed witnesses with coefficient `c`,
then every strict coefficient `q < c` survives for the actual relative
Chebyshev error in both signs.  Construction of the signed cluster witnesses
is deliberately external; no phase-selection or finite-cluster
anti-cancellation claim is made here.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/-- Arbitrarily far natural points where `f` is at least `amplitude`. -/
def HasFarNaturalPointPositiveTargetAmplitudeWitness
    (f amplitude : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, ∃ m, M ≤ m ∧ amplitude m ≤ f m

/-- Arbitrarily far natural points where `f` is at most `-amplitude`. -/
def HasFarNaturalPointNegativeTargetAmplitudeWitness
    (f amplitude : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, ∃ m, M ≤ m ∧ f m ≤ -amplitude m

/--
A positive natural-point witness transfers through an eventually small
absolute difference, with coefficient loss `loss`.
-/
theorem HasFarNaturalPointPositiveTargetAmplitudeWitness.transfer_eventually_sub_lt
    {f g amplitude : ℕ → ℝ}
    {c loss : ℝ}
    (hmain :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        g
        (fun m => c * amplitude m))
    (happrox :
      ∀ᶠ m : ℕ in atTop,
        |f m - g m| < loss * amplitude m) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness
      f
      (fun m => (c - loss) * amplitude m) := by
  intro M
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp happrox
  obtain ⟨m, hm, hmainm⟩ := hmain (max M M₀)
  refine ⟨m, le_trans (le_max_left M M₀) hm, ?_⟩
  have herror := hM₀ m (le_trans (le_max_right M M₀) hm)
  have hleft : g m - loss * amplitude m < f m := by
    have hside := (abs_sub_lt_iff.mp herror).2
    linarith
  calc
    (c - loss) * amplitude m =
        c * amplitude m - loss * amplitude m := by ring
    _ ≤ g m - loss * amplitude m := sub_le_sub_right hmainm _
    _ ≤ f m := le_of_lt hleft

/--
A negative natural-point witness transfers through an eventually small
absolute difference, with coefficient loss `loss`.
-/
theorem HasFarNaturalPointNegativeTargetAmplitudeWitness.transfer_eventually_sub_lt
    {f g amplitude : ℕ → ℝ}
    {c loss : ℝ}
    (hmain :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        g
        (fun m => c * amplitude m))
    (happrox :
      ∀ᶠ m : ℕ in atTop,
        |f m - g m| < loss * amplitude m) :
    HasFarNaturalPointNegativeTargetAmplitudeWitness
      f
      (fun m => (c - loss) * amplitude m) := by
  intro M
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp happrox
  obtain ⟨m, hm, hmainm⟩ := hmain (max M M₀)
  refine ⟨m, le_trans (le_max_left M M₀) hm, ?_⟩
  have herror := hM₀ m (le_trans (le_max_right M M₀) hm)
  have hright : f m < g m + loss * amplitude m := by
    have hside := (abs_sub_lt_iff.mp herror).1
    linarith
  calc
    f m ≤ g m + loss * amplitude m := le_of_lt hright
    _ ≤ -(c * amplitude m) + loss * amplitude m :=
      by simpa [add_comm] using add_le_add_right hmainm (loss * amplitude m)
    _ = -((c - loss) * amplitude m) := by ring

/--
Sharp signed natural-point transfer from a visible zero cluster to the actual
relative Chebyshev error.

For every `0 ≤ q < c`, independent positive and negative visible-cluster
witnesses with coefficient `c` yield actual PNT witnesses with coefficient
`q` in both signs.
-/
theorem actualWeightedBalancedGoodHeightPNTSharpSignedOmega
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
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S
            (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S
            (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) ∧
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m => q * targetZeroPowerAmplitude beta (m : ℝ)) := by
  have hloss : 0 < c - q := sub_pos.mpr hqC
  have happrox :=
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_epsilon_mul_targetAmplitude
      hbeta hbetaOne hloss sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal
  have hcoeff : c - (c - q) = q := by
    ring
  constructor
  · simpa only [hcoeff] using
      hmainPos.transfer_eventually_sub_lt happrox
  · simpa only [hcoeff] using
      hmainNeg.transfer_eventually_sub_lt happrox

end PrimeNumberTheorem
