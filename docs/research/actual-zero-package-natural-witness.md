# Actual zero-package natural witness

This module closes the discretization step for the actual equal-real-part
zeta-zero package.

Assume

```text
E = actualEqualRealPartZeroPackageEnergy T beta L > 0,
L > 0,
H(x) -> infinity,
q < 1.
```

Then the dynamic visible-cluster PNT main term has arbitrarily far natural
points at which its absolute value is at least

```text
q * sqrt(E) * m^(beta - 1).
```

The strict factor `q < 1` is the exact loss required by floor sampling.  The
proof first controls the real part by the complex norm, then divides by the
positive energy coefficient, and finally uses cofinality of `H` to identify
the dynamic visible cluster with the fixed actual zero package at both `x`
and `floor x`.

This is a main-term witness.  A full PNT-error lower bound still requires all
real-axis, complementary-zero, and contour remainders to be negligible at the
same scaled amplitude.

