# Actual zero-package natural sampling

`ZeroDensityLayerBudgetActualZeroPackageNaturalSampling.lean` proves that the
actual equal-real-part zeta-zero package is stable when a real scale `x` is
replaced by `floor x`.

The exact conclusion is

```text
‖M(floor x) - M(x)‖ / x^(beta - 1) -> 0,
```

where `M` is the complex PNT main term contributed by the finite package.

The proof has two independent inputs:

1. `x^(beta - 1)` has floor ratio tending to one.
2. A finite pure-phase sum is uniformly bounded and its logarithmic floor
   displacement tends to zero.

This result does not use a zero-density estimate, zero separation, or a
zero-reproduction argument. It also does not by itself prove an Omega theorem.
Its role is to transfer the already established continuous far-witness for the
actual package to natural-number evaluation points without losing the target
power scale.
