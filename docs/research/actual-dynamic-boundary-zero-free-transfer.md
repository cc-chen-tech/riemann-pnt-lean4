# Zero-free and capped right-edge transfer

## One global input replaces two indexed inputs

The beta-only actual dynamic-boundary transfer previously required separate
right-edge proofs for:

- every Carlson-indexed positive zero;
- every fixed real-ordinate nontrivial zero.

`globalNontrivialZeroRealPartCap_dynamicBoundaryRightEdges` proves that both
follow from the single global cap

```text
forall rho, IsNontrivialZero rho -> rho.re <= beta.
```

The strict interface `GlobalRightEdgeZeroFree beta` implies this cap
automatically.

## Zero-free region to PNT upper bound

For `3/4 < beta < 1`,
`actualDynamicBoundaryCanonicalBetaZeroFreePNTUpperTransfer` turns

```text
GlobalRightEdgeZeroFree beta
```

into the eventual actual PNT estimate

```text
|relativeChebyshevPsi0Error m|
  < (actualCarlsonDynamicBoundaryCoefficientCapConstant
        (beta - 1 / 4) + eta)
      * m ^ (beta - 1).
```

The strip threshold, truncation exponent, Carlson slack, good-height
schedule, contour certificate, coefficient cap, and indexed right-edge
proofs are all constructed internally.

Because `beta < 1`, the displayed target power tends to zero.  The theorem
`actualDynamicBoundaryCanonicalBetaZeroFree_relativePNT_tendsto_zero`
therefore closes the natural-point PNT consequence:

```text
relativeChebyshevPsi0Error m -> 0.
```

## Why strict zero-freeness is not the lower hypothesis

`dynamicEqualRealPartZeroPackage_eq_empty_of_globalRightEdgeZeroFree` proves
that strict zero-freeness at `beta` makes the package

```text
{rho : zeta(rho) = 0 and rho.re = beta and |rho.im| <= H(x)}
```

empty at every height.  Therefore a nontrivial lower witness at the same
`beta` cannot honestly be paired with strict zero-freeness.

The compatible lower-side input is instead the non-strict global cap

```text
forall rho, IsNontrivialZero rho -> rho.re <= beta,
```

which permits boundary zeros.  Under this cap and a moving-package
anti-cancellation witness,
`actualDynamicBoundaryCanonicalBetaCappedPNTBidirectionalTransfer` gives
both the automatic upper bound and the relative/unnormalized PNT lower
witnesses.

The anti-cancellation witness is still external.  No unconditional Omega
theorem or RH is claimed.
