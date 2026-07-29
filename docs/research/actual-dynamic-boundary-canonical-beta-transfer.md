# Beta-only canonical dynamic-boundary transfer

## Canonical parameters

Assume

```text
3 / 4 < beta < 1.
```

The existing threshold

```text
sigma = pntHybridCanonicalBetaThreshold beta = beta - 1 / 4
```

satisfies:

```text
1 / 2 < sigma < 1
1 + sigma < 2 * beta.
```

The balanced dynamic-boundary module then determines

```text
alpha   = (1 - sigma) / 2
epsilon = (2 * beta - sigma - 1) / 4
```

and the canonical uniform selector determines the actual good-height
schedule.

## Actual upper transfer

`actualDynamicBoundaryCanonicalBetaPNTUpperTransfer` proves, eventually at
natural points,

```text
|relativeChebyshevPsi0Error m|
  < (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta)
      * m ^ (beta - 1).
```

The upper side no longer asks for an external:

- strip threshold;
- truncation exponent;
- Carlson epsilon;
- height schedule;
- contour remainder certificate;
- dynamic-package coefficient cap.

It still requires the stated positive-zero and real-ordinate-zero
right-edge bounds.

## Bidirectional transfer

`actualDynamicBoundaryCanonicalBetaPNTBidirectionalTransfer` uses the same
actual explicit formula and moving equal-real-part package for the upper and
lower statements.  A package witness of coefficient `c` gives arbitrarily
large relative and unnormalized PNT witnesses with coefficient `c - loss`.

The package witness remains an explicit input.  This module does not prove
anti-cancellation, an unconditional Omega theorem, or RH.
