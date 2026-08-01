import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTBidirectionalTransfer

/-!
# Quantitative reverse PNT cluster exclusion

The qualitative reverse transfer excludes a visible cluster when the actual
PNT error is `o(A_beta)`.  Here the constants are retained.

If the actual error is eventually at most `q A_beta`, a nonempty visible
cluster has a `c A_beta` natural-point witness, and `q < c`, choose the
explicit-formula approximation loss `(c - q) / 2`.  The transferred witness
then has coefficient

`c - (c - q) / 2 = (c + q) / 2 > q`,

contradicting the eventual upper bound at the same natural point.  This is the
constant-sensitive reverse counterpart of the strict forward oscillation
transfer.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/--
An eventual `q * amplitude` upper bound excludes any far natural-point witness
with coefficient `d > q`, provided the amplitude is eventually positive.
-/
theorem not_hasFarNaturalPoint_mul_of_eventually_abs_le_mul
    {amplitude remainder : ℕ → ℝ}
    {q d : ℝ}
    (hupper : ∀ᶠ m : ℕ in atTop, |remainder m| ≤ q * amplitude m)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (hqd : q < d) :
    ¬ HasFarNaturalPointTargetAmplitudeWitness
        remainder
        (fun m => d * amplitude m) := by
  intro hfar
  have hbound :
      ∀ᶠ m : ℕ in atTop,
        |remainder m| ≤ q * amplitude m ∧ 0 < amplitude m :=
    hupper.and hamplitude
  obtain ⟨M, hM⟩ := eventually_atTop.mp hbound
  obtain ⟨m, hmM, hmLower⟩ := hfar M
  have hm := hM m hmM
  have hqLt : q * amplitude m < d * amplitude m :=
    mul_lt_mul_of_pos_right hqd hm.2
  exact (not_lt_of_ge hmLower) (lt_of_le_of_lt hm.1 hqLt)

/--
Constant-sensitive reverse transfer for the actual relative Chebyshev error.

An eventual actual-error upper bound with coefficient `q` forces the supplied
visible cluster to be empty whenever a nonempty cluster would have coefficient
`c > q`.  The proof transfers the cluster witness through the same dynamic
Carlson/Pintz explicit-formula decomposition with the symmetric loss
`(c - q) / 2`.
-/
theorem actualWeightedBalancedGoodHeightPNTEventualUpper_forces_emptyCluster
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
    (hupper :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| ≤
          q * targetZeroPowerAmplitude beta (m : ℝ))
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
  have hlossPos : 0 < (c - q) / 2 := half_pos (sub_pos.mpr hqC)
  have happrox :=
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_epsilon_mul_targetAmplitude
      hbeta hbetaOne hlossPos sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal
  have hwitness :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (c - q) / 2) * targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmain hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (c - q) / 2 := by
    linarith
  exact
    (not_hasFarNaturalPoint_mul_of_eventually_abs_le_mul
      hupper
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

end PrimeNumberTheorem
