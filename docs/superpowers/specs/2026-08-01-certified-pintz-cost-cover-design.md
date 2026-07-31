# Certified Pintz Cost-Cover Transfer

## Goal

Identify the actual certified good-height grid with the original Pintz dynamic
grid interface and upgrade finite-family optimality to additive-slack
optimality against every admissible height.

## Design

Given an eventual proof that every certified candidate satisfies a predicate
`zeroFree x T`, construct `PintzEnvelopeDynamicGridInput zeroFree` using:

- `actualPintzCandidateLowerEnvelope` as the diverging envelope;
- `actualPintzCandidateFiniteGrid` as the candidates;
- the Stack119 lower-envelope theorem;
- finite-image witness recovery for eventual candidate zero-freeness.

Its `toDynamicFiniteHeightGrid` is definitionally the Stack119 certified grid.
Therefore the existing Pintz theorem gives eventual zero-freeness of the same
optimized height used by Stack121.

Separately, name the required `DynamicFiniteGridCostCover` certificate for
this grid. The existing optimizer theorem then gives

```text
cost x H(x) <= cost x T + slack(x)
```

for every admissible `T`.

## Boundary

The analytic proof of a particular cost cover remains an input. This module
does not invent a discretization rate, a concrete zero-free region, signed
main witnesses, unconditional Omega, or RH.
