import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryCanonicalBetaTransfer

/-!
# Zero-free and capped right-edge dynamic-boundary transfer

The beta-only dynamic-boundary theorem previously exposed two pointwise
right-edge inputs: one for indexed positive zeros and one for the finite
real-ordinate residual.  Both are projections of one global statement about
all nontrivial zeta zeros.

There are two logically distinct global inputs:

* strict `GlobalRightEdgeZeroFree beta`, appropriate for an upper bound;
* a non-strict global cap `rho.re <= beta`, compatible with zeros on the
  boundary and hence with a lower oscillation witness.

This distinction matters.  Strict zero-freeness at `beta` makes every
equal-real-part package at `beta` empty, so it cannot simultaneously be used
as a nontrivial boundary-cluster lower hypothesis.
-/

namespace PrimeNumberTheorem

open Filter

/-- A non-strict global real-part cap supplies both right-edge inputs used by
the actual dynamic-boundary transfer. -/
theorem globalNontrivialZeroRealPartCap_dynamicBoundaryRightEdges
    {beta sigma : ℝ}
    (hcap :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.re ≤ beta) :
    (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta) := by
  constructor
  · intro index
    exact hcap (actualCarlsonPositiveZero index)
      (actualCarlsonPositiveZero_spec index).1
  · intro rho hrho
    have hreal :
        rho ∈ realOrdinateNontrivialZerosFinset 0 :=
      (Finset.mem_sdiff.mp hrho).1
    have hzero : RiemannHypothesis.IsNontrivialZero rho :=
      (mem_nontrivialZerosFinset.mp
        (mem_realOrdinateNontrivialZerosFinset.mp hreal).1).1
    exact hcap rho hzero

/-- Strict global right-edge zero-freeness supplies the non-strict transfer
right edges by weakening `< beta` to `<= beta`. -/
theorem globalRightEdgeZeroFree_dynamicBoundaryRightEdges
    {beta sigma : ℝ}
    (hzeroFree : GlobalRightEdgeZeroFree beta) :
    (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta) :=
  globalNontrivialZeroRealPartCap_dynamicBoundaryRightEdges
    (fun rho hzero => (hzeroFree rho hzero).le)

/-- A strict zero-free line contains no dynamic equal-real-part zero
package, at any height or evaluation point. -/
theorem dynamicEqualRealPartZeroPackage_eq_empty_of_globalRightEdgeZeroFree
    {H : ℝ → ℝ} {beta x : ℝ}
    (hzeroFree : GlobalRightEdgeZeroFree beta) :
    dynamicEqualRealPartZeroPackage H beta x = ∅ := by
  ext rho
  constructor
  · intro hrho
    rcases mem_dynamicEqualRealPartZeroPackage.mp hrho with
      ⟨hzero, _, hre⟩
    have hstrict := hzeroFree rho hzero
    exfalso
    linarith
  · simp

/-- Zero-free region to actual PNT upper transfer.

For `3/4 < beta < 1`, one strict global zero-free line automatically selects
the strip threshold, balanced truncation exponent, Carlson slack, canonical
good height, actual explicit-formula remainder certificate, coefficient
cap, and both pointwise right-edge inputs.
-/
theorem actualDynamicBoundaryCanonicalBetaZeroFreePNTUpperTransfer
    {beta eta : ℝ}
    (hbeta : 3 / 4 < beta)
    (hbetaOne : beta < 1)
    (hzeroFree : GlobalRightEdgeZeroFree beta)
    (heta : 0 < eta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant
            (pntHybridCanonicalBetaThreshold beta) + eta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  rcases
      globalRightEdgeZeroFree_dynamicBoundaryRightEdges
        (sigma := pntHybridCanonicalBetaThreshold beta) hzeroFree with
    ⟨hpositiveRightEdge, hrealRightEdge⟩
  exact
    actualDynamicBoundaryCanonicalBetaPNTUpperTransfer
      hbeta hbetaOne hpositiveRightEdge hrealRightEdge heta

/-- The same zero-free input yields the prime number theorem along natural
points: the actual relative Chebyshev error tends to zero. -/
theorem actualDynamicBoundaryCanonicalBetaZeroFree_relativePNT_tendsto_zero
    {beta eta : ℝ}
    (hbeta : 3 / 4 < beta)
    (hbetaOne : beta < 1)
    (hzeroFree : GlobalRightEdgeZeroFree beta)
    (heta : 0 < eta) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hupper :=
    actualDynamicBoundaryCanonicalBetaZeroFreePNTUpperTransfer
      hbeta hbetaOne hzeroFree heta
  have htargetReal :
      Tendsto (targetZeroPowerAmplitude beta) atTop (nhds 0) := by
    simpa only [targetZeroPowerAmplitude, neg_sub] using
      tendsto_rpow_neg_atTop
        (show 0 < 1 - beta by linarith)
  have htargetNat :
      Tendsto
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        atTop (nhds 0) :=
    htargetReal.comp tendsto_natCast_atTop_atTop
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          (actualCarlsonDynamicBoundaryCoefficientCapConstant
              (pntHybridCanonicalBetaThreshold beta) + eta) *
            targetZeroPowerAmplitude beta (m : ℝ))
        atTop (nhds 0) :=
    by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul htargetNat :
          Tendsto
            (fun m : ℕ =>
              (actualCarlsonDynamicBoundaryCoefficientCapConstant
                  (pntHybridCanonicalBetaThreshold beta) + eta) *
                targetZeroPowerAmplitude beta (m : ℝ))
            atTop
            (nhds
              ((actualCarlsonDynamicBoundaryCoefficientCapConstant
                  (pntHybridCanonicalBetaThreshold beta) + eta) * 0)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards with m
    exact norm_nonneg _
  · filter_upwards [hupper] with m hm
    simpa [Real.norm_eq_abs] using hm.le

/-- Non-strict global right-edge cap to actual bidirectional PNT transfer.

Unlike strict zero-freeness, the cap permits zeros with real part exactly
`beta`; those zeros form the moving main package.  Every supplied package
witness with coefficient `c` transfers with arbitrary loss
`0 < loss < c`.
-/
theorem actualDynamicBoundaryCanonicalBetaCappedPNTBidirectionalTransfer
    {beta eta c loss : ℝ}
    (hbeta : 3 / 4 < beta)
    (hbetaOne : beta < 1)
    (hcap :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.re ≤ beta)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight
              (actualDynamicBoundaryBalancedGoodHeightExponent
                (pntHybridCanonicalBetaThreshold beta)))
            (dynamicEqualRealPartZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight
                (actualDynamicBoundaryBalancedGoodHeightExponent
                  (pntHybridCanonicalBetaThreshold beta)))
              beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant
              (pntHybridCanonicalBetaThreshold beta) + eta) *
            targetZeroPowerAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x => (c - loss) * targetZeroPowerAmplitude beta x) ∧
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x => (c - loss) * x ^ beta) := by
  rcases
      globalNontrivialZeroRealPartCap_dynamicBoundaryRightEdges
        (sigma := pntHybridCanonicalBetaThreshold beta) hcap with
    ⟨hpositiveRightEdge, hrealRightEdge⟩
  exact
    actualDynamicBoundaryCanonicalBetaPNTBidirectionalTransfer
      hbeta hbetaOne hpositiveRightEdge hrealRightEdge
        heta hloss hlossC hmain

end PrimeNumberTheorem
