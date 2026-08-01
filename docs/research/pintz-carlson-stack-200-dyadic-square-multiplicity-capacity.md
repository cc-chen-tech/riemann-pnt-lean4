# Stack200: dyadic square-multiplicity capacity for direct L2

This stack is restricted to the density/capacity side of the direct-L2
interface.  It does not contain Sharp energy bounds, Gram/Schur separation,
half-isolated arguments, or final exceptional-set growth.

## Abstract capacity interface

For a finite set, nonnegative weight `w`, multiplicity `m`, and pointwise
bound `m(rho) <= M`, Lean proves

```text
sum m(rho)^2 * w(rho) <= M * sum m(rho) * w(rho).
```

It also proves that deleting any finite set `S` cannot increase the square
capacity.  This is pure nonnegative-mass monotonicity; no density theorem is
reproved for `S`.

## Actual zeta dyadic strip

The real-zeta instance uses

```text
2^n < Im(rho) <= 2^(n+1),
sigma < Re(rho) <= tau.
```

The linear analytic-multiplicity capacity is bounded by the cumulative
Carlson count `N(sigma,2^(n+1))`.  The direct-L2 weight gives

```text
sum m(rho)/|rho|^2
  <= N(sigma,2^(n+1)) / (2^n)^2.
```

The proved fixed-width Jensen estimate supplies the local pointwise bound

```text
m(rho) <= B * (1 + log(2^(n+1) + 6)).
```

Combining them yields the callable acceptance theorem

```text
sum m(rho)^2/|rho|^2
  <= B*(1+log(2^(n+1)+6))
       * N(sigma,2^(n+1))/(2^n)^2.
```

The identical bound holds after deleting every finite exceptional set `S`.

## Exponent and logarithmic-loss ledger

Write Carlson's classical density exponent as

```text
q(sigma) = 4*sigma*(1-sigma).
```

On `0 <= sigma <= 1`, Lean proves `q(sigma) <= 1`.  Therefore the direct-L2
power after `1/|rho|^2` is

```text
q(sigma) - 2 <= -1 < 0.
```

The equality `q(1/2)=1` remains, but it produces L2 exponent `-1`, not zero.
Thus the L1 half-height equality must not be promoted to a general Carlson
impossibility.

The existing Carlson input carries `(log T)^4`.  The local maximum
multiplicity costs one additional explicit logarithm, so this direct-L2
capacity has effective `(log T)^5` loss.  There is no further multiplicity
loss in this stack.

## Half-isolated interface

This module provides only:

- dyadic strip linear count and weighted mass;
- local maximum multiplicity;
- square-multiplicity reciprocal capacity;
- finite-exception deletion monotonicity.

The half-isolated work is responsible for Occupancy or Gram/Schur separation
and may consume these outputs directly.
