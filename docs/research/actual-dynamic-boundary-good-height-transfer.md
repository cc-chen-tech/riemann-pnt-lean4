# Canonical good-height dynamic-boundary transfer

## Result

`actualDynamicBoundaryCanonicalSelectedGoodHeight alpha` fixes the global
uniform natural-point good-height selector at polynomial scale `x ^ alpha`.
The theorem
`actualDynamicBoundaryCanonicalSelectedGoodHeight_spec` constructs, rather
than assumes:

- eventual natural-point height control `H(m) <= m ^ alpha`;
- cofinality `H(m) -> infinity`;
- an actual explicit-formula remainder certificate normalized by
  `m ^ (beta - 1)`.

The construction requires the sharp contour conditions

```text
0 < alpha <= 1
1 - beta < alpha.
```

## Transfer

`actualDynamicBoundaryCanonicalGoodHeightPNTUpperTransfer` combines this
height package with the automatic dynamic-boundary coefficient cap.  Its
eventual conclusion is

```text
|relativeChebyshevPsi0Error m|
  < (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta)
      * m ^ (beta - 1).
```

No externally supplied height schedule, contour remainder certificate, or
dynamic-package coefficient cap remains.

`actualDynamicBoundaryCanonicalGoodHeightPNTBidirectionalTransfer` uses the
same explicit formula and the same moving equal-real-part package for this
upper bound and for the lower witness transfer.  Given a package witness with
coefficient `c`, every `0 < loss < c` produces:

```text
|relativeChebyshevPsi0Error x| >= (c - loss) * x ^ (beta - 1)
|chebyshevPsi0Error x|         >= (c - loss) * x ^ beta
```

at arbitrarily large real points.

## Honest boundary

The Carlson side still assumes the stated positive and real-zero right-edge
bounds.  The lower side still assumes a far natural-point witness for the
moving equal-real-part package.  This module neither proves the package
anti-cancellation theorem nor claims an unconditional Omega theorem or RH.
