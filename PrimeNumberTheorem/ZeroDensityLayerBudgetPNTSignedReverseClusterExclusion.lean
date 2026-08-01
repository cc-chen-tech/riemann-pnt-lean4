import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSharpSignedOmega

/-!
# One-sided reverse PNT cluster exclusion

The absolute-value reverse theorem assumes a two-sided PNT error bound.  Signed
cluster witnesses permit strictly weaker hypotheses:

* an eventual upper bound excludes a larger positive cluster witness;
* an eventual lower bound excludes a larger negative cluster witness.

After transferring the cluster witness with loss `(c - q) / 2`, the surviving
coefficient is `(c + q) / 2 > q`, so the contradiction occurs on the same
natural-point side.  This is a one-sided, constant-sensitive reverse transfer
interface; the signed visible-cluster witness remains external.
-/

open scoped Topology
open Filter

noncomputable section

namespace PrimeNumberTheorem

/-- An eventual upper bound excludes a larger positive far-point witness. -/
theorem not_hasFarNaturalPointPositive_mul_of_eventually_le_mul
    {amplitude remainder : ℕ → ℝ}
    {q d : ℝ}
    (hupper : ∀ᶠ m : ℕ in atTop, remainder m ≤ q * amplitude m)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (hqd : q < d) :
    ¬ HasFarNaturalPointPositiveTargetAmplitudeWitness
        remainder
        (fun m => d * amplitude m) := by
  intro hfar
  have hbound :
      ∀ᶠ m : ℕ in atTop,
        remainder m ≤ q * amplitude m ∧ 0 < amplitude m :=
    hupper.and hamplitude
  obtain ⟨M, hM⟩ := eventually_atTop.mp hbound
  obtain ⟨m, hmM, hmLower⟩ := hfar M
  have hm := hM m hmM
  have hqLt : q * amplitude m < d * amplitude m :=
    mul_lt_mul_of_pos_right hqd hm.2
  exact (not_lt_of_ge (le_trans hmLower hm.1)) hqLt

/-- An eventual lower bound excludes a larger negative far-point witness. -/
theorem not_hasFarNaturalPointNegative_mul_of_eventually_neg_mul_le
    {amplitude remainder : ℕ → ℝ}
    {q d : ℝ}
    (hlower : ∀ᶠ m : ℕ in atTop, -(q * amplitude m) ≤ remainder m)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (hqd : q < d) :
    ¬ HasFarNaturalPointNegativeTargetAmplitudeWitness
        remainder
        (fun m => d * amplitude m) := by
  intro hfar
  have hbound :
      ∀ᶠ m : ℕ in atTop,
        -(q * amplitude m) ≤ remainder m ∧ 0 < amplitude m :=
    hlower.and hamplitude
  obtain ⟨M, hM⟩ := eventually_atTop.mp hbound
  obtain ⟨m, hmM, hmUpper⟩ := hfar M
  have hm := hM m hmM
  have hqLt : q * amplitude m < d * amplitude m :=
    mul_lt_mul_of_pos_right hqd hm.2
  have hnegLt : -(d * amplitude m) < -(q * amplitude m) :=
    neg_lt_neg hqLt
  exact (not_lt_of_ge (le_trans hm.1 hmUpper)) hnegLt

/--
An eventual one-sided upper bound for the actual PNT error forces a visible
cluster with a stronger positive witness to be empty.
-/
theorem actualWeightedBalancedGoodHeightPNTEventualUpper_forces_emptyCluster_of_positiveWitness
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
        relativeChebyshevPsi0Error (m : ℝ) ≤
          q * targetZeroPowerAmplitude beta (m : ℝ))
    (hmainPos :
      S.Nonempty →
        HasFarNaturalPointPositiveTargetAmplitudeWitness
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
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (c - q) / 2) *
            targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmainPos hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (c - q) / 2 := by
    linarith only [hqC]
  exact
    (not_hasFarNaturalPointPositive_mul_of_eventually_le_mul
      hupper
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

/--
An eventual one-sided lower bound for the actual PNT error forces a visible
cluster with a stronger negative witness to be empty.
-/
theorem actualWeightedBalancedGoodHeightPNTEventualLower_forces_emptyCluster_of_negativeWitness
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
    (hlower :
      ∀ᶠ m : ℕ in atTop,
        -(q * targetZeroPowerAmplitude beta (m : ℝ)) ≤
          relativeChebyshevPsi0Error (m : ℝ))
    (hmainNeg :
      S.Nonempty →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
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
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m => relativeChebyshevPsi0Error (m : ℝ))
        (fun m =>
          (c - (c - q) / 2) *
            targetZeroPowerAmplitude beta (m : ℝ)) :=
    (hmainNeg hNonempty).transfer_eventually_sub_lt happrox
  have hqTransferred : q < c - (c - q) / 2 := by
    linarith only [hqC]
  exact
    (not_hasFarNaturalPointNegative_mul_of_eventually_neg_mul_le
      hlower
      (eventually_targetZeroPowerAmplitude_natural_pos beta)
      hqTransferred)
      hwitness

end PrimeNumberTheorem
