# Automatic dynamic-boundary PNT witness transfer

## Result

The theorem
`actualDynamicBoundaryAutomaticPNTWitnessTransfer`
is the single-entry endpoint of the current density/explicit-formula chain.

It accepts:

1. a polynomially bounded height schedule tending to infinity;
2. a Carlson strip parameter with a strictly negative low-layer margin;
3. non-strict right-edge bounds for positive and real-ordinate zeros;
4. a natural-point selected-height contour remainder certificate; and
5. a far natural-point witness for the moving equal-real-part zero package.

It returns a genuine far witness for the relative Chebyshev error at

```text
(c - loss) * x^(beta - 1)
```

for every `0 < loss < c`.

## Why the boundary inequalities are non-strict

A zero with real part strictly below `beta` decays after normalization by
`x^(beta - 1)`.  A zero with real part exactly `beta` need not decay, but the
dynamic package absorbs it once the selected height exceeds its ordinate.
This is why the high-tail and real-ordinate hypotheses use `re <= beta`, while
the canonical low-layer estimate still requires a strict exponent margin.

## Interface with local oscillation

The remaining oscillatory input is exactly the package witness with
coefficient `c`.  A local theorem may encode multiplicity, `1 / |rho|`, and a
constant strictly larger than `pi / 2` in `c`.  This facade preserves that
coefficient up to an arbitrarily small fixed `loss`.

No package witness, sharp pi-over-two theorem, zero-reproduction argument, RH,
or unconditional Omega statement is asserted here.
