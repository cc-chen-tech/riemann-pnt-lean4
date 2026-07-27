import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTSignedReverseClusterExclusion

/-!
# One-sided reverse PNT transfer to a finite-height zeta zero-free region

The signed reverse transfer currently concludes that an abstract finite visible
cluster `S` is empty.  This module gives that conclusion concrete zeta-zero
semantics.

For a target real part `beta` and height `H`, we define the finite cluster of
all nontrivial zeta zeros satisfying

`|rho.im| <= H` and `beta <= rho.re`.

The cluster is invariant under complex conjugation, and its emptiness is
equivalent to the finite-height zero-free statement that every nontrivial zero
up to height `H` has real part strictly below `beta`.  Specializing the positive
and negative one-sided reverse transfers to this cluster therefore turns an
eventual one-sided PNT bound into an actual finite-height zeta-zero exclusion.

The result remains conditional on the outside-cluster bucket input and on the
corresponding signed visible-cluster witness.  It is not an unconditional
zero-free region.
-/

open scoped ComplexConjugate

noncomputable section

namespace PrimeNumberTheorem

open Complex
open Filter

/-- Nontrivial zeta zeros up to height `H` lying at or to the right of
`Re(s) = beta`. -/
noncomputable def rightEdgeNontrivialZerosFinset
    (beta H : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset H).filter fun rho => beta ≤ rho.re

/-- Exact membership in the finite right-edge zero cluster. -/
lemma mem_rightEdgeNontrivialZerosFinset
    {beta H : ℝ} {rho : ℂ} :
    rho ∈ rightEdgeNontrivialZerosFinset beta H ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        |rho.im| ≤ H ∧ beta ≤ rho.re := by
  simp [rightEdgeNontrivialZerosFinset, mem_nontrivialZerosFinset,
    and_assoc]

/-- Every nontrivial zeta zero up to height `H` lies strictly to the left of
`Re(s) = beta`. -/
def FiniteHeightRightEdgeZeroFree (beta H : ℝ) : Prop :=
  ∀ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho →
      |rho.im| ≤ H →
        rho.re < beta

/-- The finite right-edge cluster is empty exactly when the corresponding
finite-height zeta zero-free statement holds. -/
theorem rightEdgeNontrivialZerosFinset_eq_empty_iff_zeroFree
    (beta H : ℝ) :
    rightEdgeNontrivialZerosFinset beta H = ∅ ↔
      FiniteHeightRightEdgeZeroFree beta H := by
  constructor
  · intro hempty rho hzero hheight
    have hnot : ¬ beta ≤ rho.re := by
      intro hre
      have hmem :
          rho ∈ rightEdgeNontrivialZerosFinset beta H :=
        mem_rightEdgeNontrivialZerosFinset.mpr
          ⟨hzero, hheight, hre⟩
      rw [hempty] at hmem
      simpa using hmem
    exact lt_of_not_ge hnot
  · intro hzeroFree
    ext rho
    constructor
    · intro hmem
      have hrho := mem_rightEdgeNontrivialZerosFinset.mp hmem
      exact
        (not_lt_of_ge hrho.2.2
          (hzeroFree rho hrho.1 hrho.2.1)).elim
    · simp

/-- The finite right-edge zero cluster is stable under complex conjugation. -/
theorem rightEdgeNontrivialZerosFinset_conjugationInvariant
    (beta H : ℝ) :
    IsConjugationInvariantCluster
      (rightEdgeNontrivialZerosFinset beta H) := by
  intro rho
  constructor
  · intro hconj
    have hrho :=
      mem_rightEdgeNontrivialZerosFinset.mp hconj
    apply mem_rightEdgeNontrivialZerosFinset.mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa using
        RiemannVonMangoldt.isNontrivialZero_conj hrho.1
    · simpa using hrho.2.1
    · simpa using hrho.2.2
  · intro hrho
    have h :=
      mem_rightEdgeNontrivialZerosFinset.mp hrho
    apply mem_rightEdgeNontrivialZerosFinset.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact RiemannVonMangoldt.isNontrivialZero_conj h.1
    · simpa using h.2.1
    · simpa using h.2.2

/--
An eventual upper bound for the actual relative PNT error excludes every
nontrivial zeta zero with `beta <= rho.re` and `|rho.im| <= H`, provided every
nonempty right-edge cluster supplies the stronger positive signed witness.
-/
theorem
    actualWeightedBalancedGoodHeightPNTEventualUpper_zeroFree_of_positiveWitness
    {beta c q H : ℝ}
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
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (rightEdgeNontrivialZerosFinset beta H)
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0
          (rightEdgeNontrivialZerosFinset beta H),
        rho.re < beta)
    (hupper :
      ∀ᶠ m : ℕ in atTop,
        relativeChebyshevPsi0Error (m : ℝ) ≤
          q * targetZeroPowerAmplitude beta (m : ℝ))
    (hmainPos :
      (rightEdgeNontrivialZerosFinset beta H).Nonempty →
        HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              (rightEdgeNontrivialZerosFinset beta H)
              (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    FiniteHeightRightEdgeZeroFree beta H := by
  apply
    (rightEdgeNontrivialZerosFinset_eq_empty_iff_zeroFree beta H).mp
  exact
    actualWeightedBalancedGoodHeightPNTEventualUpper_forces_emptyCluster_of_positiveWitness
      hbeta hbetaOne hq hqC sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa
      (rightEdgeNontrivialZerosFinset_conjugationInvariant beta H)
      hfixedSigma hkappa hnorm hre hreal hupper hmainPos

/--
An eventual lower bound for the actual relative PNT error excludes every
nontrivial zeta zero with `beta <= rho.re` and `|rho.im| <= H`, provided every
nonempty right-edge cluster supplies the stronger negative signed witness.
-/
theorem
    actualWeightedBalancedGoodHeightPNTEventualLower_zeroFree_of_negativeWitness
    {beta c q H : ℝ}
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
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (rightEdgeNontrivialZerosFinset beta H)
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0
          (rightEdgeNontrivialZerosFinset beta H),
        rho.re < beta)
    (hlower :
      ∀ᶠ m : ℕ in atTop,
        -(q * targetZeroPowerAmplitude beta (m : ℝ)) ≤
          relativeChebyshevPsi0Error (m : ℝ))
    (hmainNeg :
      (rightEdgeNontrivialZerosFinset beta H).Nonempty →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              (rightEdgeNontrivialZerosFinset beta H)
              (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    FiniteHeightRightEdgeZeroFree beta H := by
  apply
    (rightEdgeNontrivialZerosFinset_eq_empty_iff_zeroFree beta H).mp
  exact
    actualWeightedBalancedGoodHeightPNTEventualLower_forces_emptyCluster_of_negativeWitness
      hbeta hbetaOne hq hqC sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa
      (rightEdgeNontrivialZerosFinset_conjugationInvariant beta H)
      hfixedSigma hkappa hnorm hre hreal hlower hmainNeg

end PrimeNumberTheorem
