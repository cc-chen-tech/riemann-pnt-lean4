# Bidirectional dynamic-boundary PNT transfer

## Unified theorem

`actualDynamicBoundaryAutomaticPNTBidirectionalTransfer` uses one height
schedule, one Carlson strip margin, one pair of right-edge hypotheses, and one
selected-height remainder certificate.

Its package-side upper input is

```text
finiteVisibleClusterCoefficientMass(dynamic package m) <= C
```

eventually.  Its package-side lower input is a far witness at

```text
c * m^(beta - 1).
```

For arbitrary `eta > 0` and `0 < loss < c`, it returns:

```text
|relative PNT error(m)| < (C + eta) * m^(beta - 1)
```

eventually, and arbitrarily far lower witnesses at

```text
(c - loss) * x^(beta - 1)
```

for the relative error and

```text
(c - loss) * x^beta
```

for `psi0(x) - x`.

## Meaning

This is a literal upper/lower transfer machine acting on the same actual PNT
error and the same dynamic zero package.  It does not identify `C` with `c`:
an upper coefficient-mass cap and a lower anti-cancellation witness are
different mathematical statements.

The remaining automatic upper-side task is to dominate the dynamic package
mass by a global summable Carlson boundary weight, including conjugate and
real-ordinate contributions.  The remaining lower-side task is the independent
local oscillation theorem for the moving package.
