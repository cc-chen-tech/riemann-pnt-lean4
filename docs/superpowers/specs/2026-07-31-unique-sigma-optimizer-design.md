# Unique Sigma Optimizer Design

## Goal

Strengthen the exact optimizer theorem from existence and global optimality to
existence of exactly one balancing density threshold.

## Strict monotonicity

For `1 / 2 < sigma₁ < sigma₂`, the factorization behind the Carlson density
exponent gives

```text
densityExponent(sigma₂) < densityExponent(sigma₁).
```

When `sigma₂ < 1`, both density exponents are positive. Cross multiplication
then shows

```text
balancedSlope(sigma₂) < balancedSlope(sigma₁).
```

## Uniqueness

The balance map is

```text
balancedSlope(sigma) * (beta - sigma).
```

On the optimizer interval both factors are positive and strictly decrease.
Therefore the product strictly decreases. Two thresholds cannot both satisfy

```text
2 * balancedSlope(sigma) * (beta - sigma) = beta - theta.
```

Combining this at-most-one result with stack57's IVT existence theorem yields
`ExistsUnique`.

## Boundary

This slice proves uniqueness of the implicit optimizer. It does not introduce
a closed-form expression, differentiate the ceiling, or add new analytic
zero-density input.
