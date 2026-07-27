import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicReverseZeroFree

/-!
# Dynamic signed reverse transfer from the actual PNT error to zeta zero-freeness

The fixed-height signed reverse theorem requires a Carlson/explicit-formula
tail input for the right-edge zero cluster at a chosen cutoff `H`.  The global
cofinality theorem requires such finite-height zero-freeness only along a
height schedule tending to infinity.

This module combines the two statements at the actual weighted-balanced good
height shared by the Carlson density estimate and the explicit formula.  A
single certificate packages all outside-cluster tail data at one cluster
cutoff.  A family of these certificates only along

`H = actualSelectedHeightFiniteStripWeightedBalancedGoodHeight ... x`

is enough.  Consequently, either an eventual upper PNT bound together with
positive cluster witnesses, or an eventual lower PNT bound together with
negative cluster witnesses, forces the global right-edge zeta zero-free
statement.

The certificate family and the signed cluster witnesses remain analytic
hypotheses.  No unconditional zero-free region or RH statement is asserted.
-/

open scoped Topology

noncomputable section

namespace PrimeNumberTheorem

open Filter

/--
All actual Carlson/explicit-formula tail data needed to remove the finite
right-edge zero cluster at cutoff `H`.

The explicit-formula evaluation height remains the selected weighted-balanced
height as a function of its own argument.  The parameter `H` controls only the
distinguished finite right-edge cluster.
-/
structure ActualWeightedBalancedGoodHeightRightEdgeTailCertificate
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : Type where
  cluster_height : ℝ
  input :
    (y : ℝ) →
      PositiveZeroOutsideClusterBucketInput
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection y)
        (rightEdgeNontrivialZerosFinset beta cluster_height)
        (n + 1)
  kappa : Fin (n + 1) → ℝ
  fixed_sigma :
    ∀ i y, (input y).sigma i = sigma i
  kappa_pos :
    ∀ i, 0 < kappa i
  layer_norm_lower :
    ∀ i y rho, rho ∈ (input y).layer i → kappa i ≤ ‖rho‖
  layer_re_upper :
    ∀ i y rho, rho ∈ (input y).layer i → rho.re ≤ tau i
  real_ordinate_re_lt :
    ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0
        (rightEdgeNontrivialZerosFinset beta cluster_height),
      rho.re < beta

/--
Dynamic positive one-sided reverse transfer.

It is enough to provide the outside-cluster certificate and positive cluster
witness only at the cofinal sequence of actual weighted-balanced good heights.
An eventual upper bound with coefficient `q` strictly below the cluster
coefficient `c` then forces every nontrivial zeta zero to satisfy
`rho.re < beta`.
-/
theorem
    actualWeightedBalancedGoodHeightPNTEventualUpper_globalZeroFree_of_dynamicPositiveWitness
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
    (tail :
      (x : ℝ) →
        ActualWeightedBalancedGoodHeightRightEdgeTailCertificate
          (beta := beta)
          sigma tau selection)
    (tail_height :
      ∀ x : ℝ,
        (tail x).cluster_height =
          actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
    (hupper :
      ∀ᶠ m : ℕ in atTop,
        relativeChebyshevPsi0Error (m : ℝ) ≤
          q * targetZeroPowerAmplitude beta (m : ℝ))
    (hmainPos :
      ∀ x : ℝ,
        (rightEdgeNontrivialZerosFinset beta
          (tail x).cluster_height).Nonempty →
          HasFarNaturalPointPositiveTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                  beta sigma tau selection)
                (rightEdgeNontrivialZerosFinset beta
                  (tail x).cluster_height)
                (m : ℝ))
            (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    GlobalRightEdgeZeroFree beta := by
  apply globalRightEdgeZeroFree_of_eventually_finiteHeight_of_tendsto
  · have hactual :=
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_tendsto_atTop
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
    apply hactual.congr'
    exact Filter.Eventually.of_forall fun x => (tail_height x).symm
  · apply Filter.Eventually.of_forall
    intro x
    exact
      actualWeightedBalancedGoodHeightPNTEventualUpper_zeroFree_of_positiveWitness
        hbeta hbetaOne hq hqC sigma tau hsigma hsigmaOne htau hthreshold
        selection (tail x).input (tail x).kappa (tail x).fixed_sigma
        (tail x).kappa_pos (tail x).layer_norm_lower
        (tail x).layer_re_upper (tail x).real_ordinate_re_lt
        hupper (hmainPos x)

/--
Dynamic negative one-sided reverse transfer.

It is enough to provide the outside-cluster certificate and negative cluster
witness only at the cofinal sequence of actual weighted-balanced good heights.
An eventual lower bound with coefficient `q` strictly below the cluster
coefficient `c` then forces every nontrivial zeta zero to satisfy
`rho.re < beta`.
-/
theorem
    actualWeightedBalancedGoodHeightPNTEventualLower_globalZeroFree_of_dynamicNegativeWitness
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
    (tail :
      (x : ℝ) →
        ActualWeightedBalancedGoodHeightRightEdgeTailCertificate
          (beta := beta)
          sigma tau selection)
    (tail_height :
      ∀ x : ℝ,
        (tail x).cluster_height =
          actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
    (hlower :
      ∀ᶠ m : ℕ in atTop,
        -(q * targetZeroPowerAmplitude beta (m : ℝ)) ≤
          relativeChebyshevPsi0Error (m : ℝ))
    (hmainNeg :
      ∀ x : ℝ,
        (rightEdgeNontrivialZerosFinset beta
          (tail x).cluster_height).Nonempty →
          HasFarNaturalPointNegativeTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                  beta sigma tau selection)
                (rightEdgeNontrivialZerosFinset beta
                  (tail x).cluster_height)
                (m : ℝ))
            (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    GlobalRightEdgeZeroFree beta := by
  apply globalRightEdgeZeroFree_of_eventually_finiteHeight_of_tendsto
  · have hactual :=
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_tendsto_atTop
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
    apply hactual.congr'
    exact Filter.Eventually.of_forall fun x => (tail_height x).symm
  · apply Filter.Eventually.of_forall
    intro x
    exact
      actualWeightedBalancedGoodHeightPNTEventualLower_zeroFree_of_negativeWitness
        hbeta hbetaOne hq hqC sigma tau hsigma hsigmaOne htau hthreshold
        selection (tail x).input (tail x).kappa (tail x).fixed_sigma
        (tail x).kappa_pos (tail x).layer_norm_lower
        (tail x).layer_re_upper (tail x).real_ordinate_re_lt
        hlower (hmainNeg x)

end PrimeNumberTheorem
