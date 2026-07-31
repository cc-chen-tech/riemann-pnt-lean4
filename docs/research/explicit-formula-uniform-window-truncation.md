# Uniform-window truncation research boundary

## Goal

Turn the existing common-good-height natural-point explicit formula into a
bound that is uniform for every real point in a logarithmic window.

The existing theorem already selects one height `T` that works for every
natural `m >= 3`.  The first missing input is therefore spatial variation at
fixed `T`, not another height-selection theorem.

## First unconditional milestone

For a nontrivial zero `rho`, the function

```text
x |-> x^rho / rho
```

has derivative `x^(rho - 1)` on `x > 0`.  Since every nontrivial zeta zero has
`rho.re < 1`, this derivative has norm at most one on `x >= 1`.  Consequently

```text
norm (x^rho / rho - m^rho / rho) <= |x - m|.
```

After summing analytic multiplicities, the complete finite zero sum satisfies

```text
norm (finiteZeroSum x T - finiteZeroSum m T)
  <= globalZeroMultiplicity T * |x - m|.
```

This is unconditional and uses actual zeta zeros with analytic multiplicity.

## Later assembly

Combining the spatial estimate with the existing natural-point Perron error
suggests the normalized error scales

```text
x^(1-beta) log(x)^2 / T + T log(T) / x^beta.
```

For an off-line zero `beta > 1/2`, a power choice `T = x^theta` can make both
terms decay whenever

```text
1 - beta < theta < beta.
```

The present milestone does not yet prove this continuous-window estimate.  In
particular it does not control the midpoint jump, choose the power height, or
bound the complementary zero package.

## Claim boundary

- No RH conclusion.
- No Carlson contradiction.
- No unconditional local oscillation theorem.
- No new project axiom, `sorry`, or `admit`.
