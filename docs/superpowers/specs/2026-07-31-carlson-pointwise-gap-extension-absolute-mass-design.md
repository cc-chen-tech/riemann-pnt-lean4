# Carlson Pointwise-Gap Extension Absolute-Mass Design

## Objective

Replace stack83/84's uniform outside-cluster real-part cap by the strictly
weaker condition that every individual residual Carlson-indexed zero lies to
the left of the target line.  The conclusion must control termwise absolute
mass, not merely the norm of a signed total sum, so that every moving finite
subcluster is controlled without cancellation.

## Existing inputs

The repository already proves:

- summability of multiplicity-over-norm weights in every fixed strict Carlson
  strip `1/2 < sigma < 1`;
- decay of the infinite outside-cluster normalized kernel `tsum` under only
  pointwise `Re rho < beta` outside a finite cluster;
- every finite high-strip sum of kernel norms is bounded by that `tsum`;
- the canonical low real-part layer has a two-height absolute-mass bound;
- full outside absolute mass is two positive masses plus the real-ordinate
  mass under conjugation invariance;
- a negligible moving extension transfers signed fixed-seed witnesses to the
  actual PNT error with coefficient `c / 4`.

The missing bridge is the finite selected-height absolute-mass split joining
these inputs.

## New pointwise inequality

For a selected height `T`, canonical low bucket `L`, and high set

```text
H = {rho outside S : 0 < Im rho <= T and sigma < Re rho},
```

prove

```text
sum_{rho outside S, 0 < Im rho <= T} ||K_x(rho)|| / A_beta(x)
  <=
sum_{rho in L} ||K_x(rho)|| / A_beta(x)
  + actualCarlsonOutsideClusterNormalizedKernelTail(sigma,beta,S,x).
```

The low/high partition is exact.  The high finite family is embedded
injectively into `ActualCarlsonPositiveZeroIndex sigma`, and its finite sum is
bounded by the summable outside-cluster `tsum`.

## Decay chain

1. Use the canonical two-height low-layer theorem to show the selected low
   absolute mass is target-negligible.
2. Use dominated convergence for the infinite Carlson outside-cluster tail;
   only pointwise strict separation is required.
3. Squeeze the selected positive outside absolute mass by the sum of those two
   decaying majorants.
4. Add the conjugate negative mass and the concrete real-ordinate mass to
   obtain full outside absolute-mass decay at natural points.
5. Dominate any moving right-edge extension by the full outside absolute mass.
6. Feed the eventual extension bound with loss `c / 2` into the existing
   signed moving-seed transfer, yielding actual PNT witnesses at `c / 4`.

## Automatic parameters

For `2/3 < beta < 1`, use
`exists_jointTwoHeightTargetAmplitudeParameters_above_cap` with the harmless
arithmetic anchor `theta = 1/2`.  Its `sigma`, `alpha`, `gammaLow`, and
`epsilonLow` close the low absolute-mass margins.  The returned fixed
`transferTau` remains the threshold defining the moving exceptional cluster.

The high strip no longer uses the returned fixed Carlson exponent margins;
it uses the dyadic reciprocal tail and pointwise strict real-part separation.
The fixed margins remain available to the inherited actual-PNT transfer.

## Public theorem chain

The module exposes:

1. `truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail`.
2. `selectedPositiveOutsideClusterPNTAbsoluteMass_naturalPointNegligible_of_CarlsonPointwiseGap`.
3. `selectedFullOutsideClusterPNTAbsoluteMass_naturalPointNegligible_of_CarlsonPointwiseGap`.
4. `selectedMovingRightEdgeExtension_naturalPointNegligible_of_CarlsonPointwiseGap`.
5. `exists_automaticGoodHeight_CarlsonPointwiseGapMovingSeedSignedNaturalTargetTransfer`.

The exact spelling may add `TargetAmplitude` if needed for consistency, but
the hypotheses and conclusions must not weaken.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCarlsonPointwiseGapExtensionAbsoluteMass.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCarlsonPointwiseGapExtensionAbsoluteMassContract.lean`
- `Test/ZeroDensityLayerBudgetActualCarlsonPointwiseGapExtensionAbsoluteMassAxiomAudit.lean`

No existing Lean file is modified.  The frozen complementary-bound file and
the Sharp, localized pi/2, VK-edge, and zero-reproduction modules remain
untouched.

## Verification and publication

Compile the main module and contract directly, then run the focused axiom
audit.  Commit design, plan, and implementation separately.  Publish a Draft
PR stacked on PR #139.

## Claim boundary

This theorem does not construct positive or negative fixed-seed witnesses.  It
also requires every residual Carlson-indexed zero to have real part strictly
less than `beta`; zeros on the target line must already be included in the
finite cluster.  Therefore it does not prove an unconditional `Omega_+-`
theorem or RH.  Its advance is removal of every uniform outside real-part gap
from the cancellation-free moving-extension estimate.
