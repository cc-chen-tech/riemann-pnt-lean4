# Threshold-driven actual zero-package transfer

This theorem removes the abstract Carlson finite-strip certificate from the
concrete-zero natural lower transfer.

For each finite strip it accepts endpoints `sigma_i`, real-part bounds
`tau_i`, and the explicit inequality

```text
carlsonStripEndpointTargetThreshold(sigma_i, tau_i) < Re rho.
```

Those inequalities automatically choose:

```text
the common polynomial height exponent,
the selected good-height schedule,
positive strip slacks,
all negative normalized exponent margins,
the natural-point contour remainder certificate.
```

The theorem also uses the concrete nontrivial zero to choose a positive-energy
window for its equal-real-part package. The resulting full relative-Chebyshev
far witness retains

```text
q * sqrt(E) * x^(Re rho - 1) / 2
```

for every `0 < q < 1`.

## Remaining mathematical input

The remaining hypotheses are geometric statements about the actual
outside-package zeros:

```text
every layer is covered by the chosen bucket input,
norms in each layer have a positive lower bound,
Re z <= tau_i in each layer,
real-ordinate outside-package zeros satisfy Re z < Re rho.
```

Carlson density bounds how many zeros occur in a strip. It does not by itself
give the strict real-part separation encoded by the last two conditions.
Eliminating them would require either enlarging the main package to include
all boundary zeros or proving a new boundary-mass/anti-cancellation theorem.

