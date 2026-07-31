# Actual Dynamic-Boundary Reciprocal Low-Layer Design

## Goal

Remove the artificial full polynomial-height cost from the dynamic-boundary
low zero layer by retaining each reciprocal zero denominator inside the sum
and applying the proved global `O(log^2 H)` reciprocal-multiplicity estimate.

## Existing loss

The existing automatic low-layer proof uses a uniform denominator guard
`kappa <= |rho|` and bounds the remaining multiplicity mass by

```text
GlobalZeroMultiplicity(H) = O(H log H).
```

With `H <= x^alpha`, normalization by the target amplitude therefore produces

```text
x^(sigma - beta + alpha) * polylog(x).
```

The strict margin must pay one full `alpha`.

## Reciprocal-mass replacement

For every zero in a layer with `Re rho <= sigma`, keep the exact denominator:

```text
|m(rho) x^(rho - 1) / rho|
  <= x^(sigma - 1) * m(rho) / |rho|.
```

Every outside-cluster layer is a subset of the global nontrivial-zero
truncation. Hence

```text
norm(layer sum)
  <= x^(sigma - 1) * GlobalReciprocalZeroMultiplicity(H).
```

The repository already proves

```text
GlobalReciprocalZeroMultiplicity(H) = O((1 + log(H + 6))^2).
```

Under `H <= x^alpha`, this gives a conservative explicit majorant

```text
C * (alpha + 2)^2 * x^(sigma - beta) * log(x)^8.
```

The power-decay condition is now

```text
sigma - beta + epsilon < 0,
```

independent of `alpha`.

## Theorem chain

1. A generic pointwise reciprocal-mass bound for any finite outside-cluster
   bucket layer.
2. Decay of the explicit `x^(sigma-beta) log^8 x` majorant.
3. Improved decay of the canonical dynamic low normalized sum.
4. Improved complete dynamic positive-tail decay using the unchanged high
   Carlson layer.

## Compatibility and claim boundary

The old unit-slope theorem remains untouched. The new theorem is a parallel,
strictly stronger low-layer route and can be installed incrementally into the
upper/signed transfer chain. This does not prove visible-main witnesses, RH,
or an unconditional Omega theorem, and it does not modify protected, Sharp,
or VK-edge modules.
