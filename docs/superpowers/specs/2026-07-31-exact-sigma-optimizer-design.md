# Exact Sigma Optimizer Design

## Goal

Upgrade the explicit midpoint improvement to an exact global optimization of
the density threshold `sigma` for fixed `beta` and prescribed cap `theta`.

## Mathematical structure

On `1 / 2 < sigma < theta` the two nontrivial ceiling components are

```text
L(sigma) = 2 * (beta - sigma)
C(sigma) = (beta - theta) / balancedSlope(sigma).
```

The low-layer component decreases. The Carlson density exponent
`4 * sigma * (1 - sigma)` decreases on `[1 / 2, 1]`, and the rational map
`q ↦ q^2 / (q + 1)` is increasing for `q ≥ 0`; therefore the balanced slope
decreases and `C(sigma)` increases.

The maximum of `min L C` occurs where the components balance:

```text
2 * balancedSlope(sigma) * (beta - sigma) = beta - theta.
```

## Construction

Clear the positive denominator and define the polynomial

```text
F(sigma)
  = 2 * densityExponent(sigma)^2 * (beta - sigma)
    - (beta - theta) * (densityExponent(sigma) + 1).
```

At `sigma = 1 / 2`, `F = 2 * theta - 1 > 0`. At `sigma = theta`,
the strict slope bound `balancedSlope(theta) < 1 / 2` gives `F < 0`.
The intermediate value theorem therefore supplies an interior zero.

## Global optimality

For any competing `sigma`:

- if `sigma` is to the right of the optimizer, its decreasing low-layer
  component is no larger than the optimum;
- if it is to the left, antitonicity of the balanced slope makes its Carlson
  component no larger than the optimum;
- if `sigma ≥ theta`, the low-layer component is already smaller.

Combining each bound with the unit cap proves the full prescribed-cap ceiling
is globally maximal at every balancing threshold.

## Boundary

The optimizer is characterized implicitly by a polynomial equation. This
slice proves existence and global optimality but does not require a radical
closed form or uniqueness. It makes no analytic zero-density claim beyond
the already formalized Carlson input.
