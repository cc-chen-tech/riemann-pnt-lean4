# Anchored moving-sigma Carlson transfer

## Problem

The proved Carlson estimate fixes `sigma` before choosing its coefficient and
eventual cutoff.  A direct substitution `sigma = sigma(x)` would reverse this
quantifier order and is not justified.

## Anchor mechanism

Fix

```text
1 / 2 < sigma0 < 1.
```

Require every moving threshold to satisfy either

```text
sigma(T, i) <= 1 / 2
```

or

```text
sigma0 <= sigma(T, i).
```

For a high layer, antitonicity of the multiplicity-weighted zero count gives

```text
N(sigma(T, i), T) <= N(sigma0, T).
```

Consequently all moving high layers use one fixed Carlson theorem at
`sigma0`; no Carlson coefficient is required to be uniform in a moving
threshold.  Every low layer is charged to the global zero multiplicity count.

## Formal chain

The main declarations are:

```text
MovingSigmaAnchoredAt
pintzCarlsonHybridDensityBudget_le_anchoredMajorant
exists_pintzConstant_anchoredUniformMovingSigmaDensityDecay
exists_fixedRate_anchoredMovingSigma_relativeChebyshevPsi0Error_tendsto
```

The last theorem proves that an arbitrary height-dependent bucket family with
anchored high thresholds admits a positive fixed truncation rate for which

```text
relativeChebyshevPsi0Error m -> 0.
```

This is an actual explicit-formula transfer to the PNT error, not an assertion
that the fixed-`sigma` Carlson theorem is uniform.

## Remaining limitation

The anchor leaves a forbidden moving-threshold gap
`(1 / 2, sigma0)`.  Removing that gap requires either a compact-uniform
Carlson estimate or a multiscale anchor family.  The present theorem isolates
that next analytic decision without introducing an invalid quantifier swap.
