# Actual zero-package natural PNT lower transfer

This module assembles the actual equal-real-part zeta-zero package with the
same selected-height explicit formula used by the upper-bound chain.

Under:

```text
beta > 0,
L > 0,
0 < q < 1,
actual package energy E > 0,
H(x) -> infinity,
a Carlson outside-cluster good-height certificate,
an actual natural-point contour remainder certificate,
```

it proves a far-witness lower bound for the full relative Chebyshev error at
the scale

```text
q * sqrt(E) * x^(beta - 1) / 2.
```

The factor `q` is the strict loss from real-to-natural floor sampling. The
factor `1/2` absorbs the three target-negligible residuals. The energy
coefficient is not discarded or normalized away.

This is a conditional transfer theorem. It does not assert that the Carlson
certificate exists for every zero package, and it does not imply RH.
