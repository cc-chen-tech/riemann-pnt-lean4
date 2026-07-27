import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicSignedReverseTransfer

/-!
# Critical-half barrier for the current dynamic outside-cluster bucket input

The current Carlson bucket interface assigns every positive-height
outside-cluster zero to a strip whose lower endpoint is strictly greater than
`1 / 2`.  Consequently, every zero covered by such an input must itself have
real part strictly greater than `1 / 2`.

For the right-edge cluster at a target `beta > 1 / 2`, a zero with
`rho.re <= 1 / 2` can never belong to the cluster.  Since the actual selected
evaluation height tends to infinity, even one right-edge tail certificate
therefore excludes every positive-height nontrivial zero on or to the left of
the critical line.

This module makes that hidden strength explicit.  It does not construct the
missing critical-half tail split.  In particular, the dynamic signed reverse
transfer remains conditional until that separate analytic decomposition is
available.
-/

open scoped Topology

noncomputable section

namespace PrimeNumberTheorem

open Filter

/-- A positive outside-cluster zero assigned to a Carlson strip with lower
endpoint above `1 / 2` must itself lie strictly to the right of `1 / 2`. -/
theorem
    PositiveZeroOutsideClusterBucketInput.half_lt_re_of_sigma_half
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (hsigma : ∀ i, 1 / 2 < input.sigma i)
    {rho : ℂ}
    (hrho : rho ∈ positiveNontrivialZerosOutsideClusterFinset T S) :
    1 / 2 < rho.re :=
  (hsigma (input.bucket rho)).trans
    (input.sigma_lt_re rho hrho)

/-- A right-edge outside-cluster bucket with all strip endpoints above
`1 / 2` cannot coexist with a positive-height zero at or to the left of the
critical line within its truncation height. -/
theorem
    no_positiveNontrivialZero_re_le_half_of_rightEdgeBucket
    {beta H T : ℝ} {n : ℕ}
    (hbetaHalf : 1 / 2 < beta)
    (input :
      PositiveZeroOutsideClusterBucketInput T
        (rightEdgeNontrivialZerosFinset beta H) n)
    (hsigma : ∀ i, 1 / 2 < input.sigma i) :
    ¬ ∃ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho ∧
          0 < rho.im ∧ rho.im ≤ T ∧ rho.re ≤ 1 / 2 := by
  rintro ⟨rho, hzero, him, himT, hre⟩
  have hnotCluster :
      rho ∉ rightEdgeNontrivialZerosFinset beta H := by
    intro hrho
    have hright :=
      (mem_rightEdgeNontrivialZerosFinset.mp hrho).2.2
    linarith
  have houtside :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset T
        (rightEdgeNontrivialZerosFinset beta H) :=
    mem_positiveNontrivialZerosOutsideClusterFinset.mpr
      ⟨hzero, him, himT, hnotCluster⟩
  have hright :=
    input.half_lt_re_of_sigma_half hsigma houtside
  linarith

/-- Every positive-height nontrivial zeta zero lies strictly to the right of
the critical line.  This predicate records the hidden consequence of the
current right-edge tail-certificate interface; it is not asserted
unconditionally. -/
def PositiveNontrivialZerosStrictlyRightOfHalf : Prop :=
  ∀ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho →
      0 < rho.im →
        1 / 2 < rho.re

/-- A single right-edge tail certificate at `beta > 1 / 2`, together with the
strip assumptions used by the transfer, forces every positive-height
nontrivial zero strictly to the right of the critical line. -/
theorem
    ActualWeightedBalancedGoodHeightRightEdgeTailCertificate.positiveZeros_strictlyRightOfHalf
    {beta : ℝ} {n : ℕ}
    {sigma tau : Fin (n + 1) → ℝ}
    {selection : UniformNaturalPointGoodHeightSelection}
    (certificate :
      ActualWeightedBalancedGoodHeightRightEdgeTailCertificate
        (beta := beta) sigma tau selection)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) :
    PositiveNontrivialZerosStrictlyRightOfHalf := by
  intro rho hzero him
  by_contra hnotRight
  have hre : rho.re ≤ 1 / 2 := le_of_not_gt hnotRight
  have hheight :
      Tendsto
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)
        atTop
        atTop :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight_tendsto_atTop
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
  have heventuallyHeight :
      ∀ᶠ y : ℝ in atTop,
        rho.im ≤
          actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection y :=
    (tendsto_atTop.1 hheight) rho.im
  rcases heventuallyHeight.exists with ⟨y, himHeight⟩
  have hsigmaInput :
      ∀ i, 1 / 2 < (certificate.input y).sigma i := by
    intro i
    rw [certificate.fixed_sigma i y]
    exact hsigma i
  exact
    (no_positiveNontrivialZero_re_le_half_of_rightEdgeBucket
      hbetaHalf (certificate.input y) hsigmaInput)
      ⟨rho, hzero, him, himHeight, hre⟩

/-- If a positive-height nontrivial zero exists on or to the left of the
critical line, then the current right-edge tail-certificate type is empty
under the strip assumptions used by the dynamic transfer. -/
theorem
    not_nonempty_rightEdgeTailCertificate_of_positiveZero_re_le_half
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (rho : ℂ)
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im)
    (hre : rho.re ≤ 1 / 2) :
    ¬ Nonempty
      (ActualWeightedBalancedGoodHeightRightEdgeTailCertificate
        (beta := beta) sigma tau selection) := by
  rintro ⟨certificate⟩
  have hright :=
    certificate.positiveZeros_strictlyRightOfHalf
      hbetaHalf hbetaOne hsigma hsigmaOne htau hthreshold
      rho hzero him
  exact (not_lt_of_ge hre) hright

end PrimeNumberTheorem
