# Balanced canonical good-height transfer

## Exact feasibility

The target-normalized contour remainder requires

```text
1 - beta < alpha,
```

while the Carlson low-layer decay requires a positive `epsilon` with

```text
sigma - beta + alpha + epsilon < 0.
```

For `1/2 < sigma < 1`, such `alpha` and `epsilon` exist exactly when

```text
1 + sigma < 2 * beta.
```

This equivalence is formalized by
`actualDynamicBoundaryGoodHeightMargins_feasible_iff`.

## Explicit choice

The module uses

```text
alpha   = (1 - sigma) / 2
epsilon = (2 * beta - sigma - 1) / 4.
```

`actualDynamicBoundaryBalancedGoodHeightParameters_spec` proves that this
choice has:

- `0 < beta`;
- `0 < alpha <= 1`;
- `1 - beta < alpha`;
- `0 < epsilon`;
- `sigma - beta + alpha + epsilon < 0`.

Thus the selected truncation height and both strict margins are determined
by `beta` and `sigma`, rather than supplied as independent inputs.

## PNT transfer

`actualDynamicBoundaryBalancedGoodHeightPNTUpperTransfer` gives the actual
relative PNT upper bound

```text
|relativeChebyshevPsi0Error m|
  < (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta)
      * m ^ (beta - 1)
```

at all sufficiently large natural points.

`actualDynamicBoundaryBalancedGoodHeightPNTBidirectionalTransfer` combines
that upper result with the existing lower witness transfer on the same PNT
error and the same moving equal-real-part package.

## Boundary

The strict gap `1 + sigma < 2 * beta` is not an artifact of the chosen
midpoint: it is necessary for this particular contour-plus-Carlson exponent
system.  Removing it requires a stronger contour estimate, a stronger
density exponent, or a different decomposition.

The module still assumes right-edge bounds for positive and real-ordinate
zeros.  Its lower conclusion still assumes the moving package's far witness.
It does not prove anti-cancellation, an unconditional Omega theorem, or RH.
