# Uniform real-sample explicit-formula height

## Verified endpoint

For every base height `A >= 8`, one height `T in [A, A + 1]` is selected
before the real sample `x`.  That same height controls every `x >= 3`:

```text
norm (explicitFormulaApproxWithMultiplicity x T - psi0 x)
  <= C * x * ((1 + log x)^2 + (1 + log (A + 6))^2) / T
     + (1 + D * T * (1 + log (T + 6)))
     + 2 * closedUniformBound
     + log x.
```

The proof combines the common-height natural-sample contour theorem with the
real floor interpolation and the global multiplicity count.

## Claim boundary

This is an unconditional fixed-height approximation theorem.  It does not yet
choose `A` as a power of the logarithmic-window center, prove normalized
decay, bound the complementary zero package, derive a zero-density
contradiction, or prove RH.
