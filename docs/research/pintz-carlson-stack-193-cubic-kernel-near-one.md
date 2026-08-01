# Stack 193: quantitative cubic multiplier near one

## Result

Let

```text
M(rho,h) = ((exp(h rho) - 1) / (h rho))^2.
```

Using the complex exponential Taylor remainder, this slice proves the explicit
local estimate

```text
|M(rho,h) - 1| <= 3 h |rho|    when h > 0 and h |rho| <= 1.
```

Combined with Stack 192, this gives two-sided bounds for the normalized cubic
zero kernel at the exact scale

```text
m(rho) x^(Re rho) / |rho|.
```

For every finite set of nonzero poles and every positive epsilon, the module
also constructs one positive step-size threshold that makes all multipliers
epsilon-close to one simultaneously.

## Mathematical role

This is the finite-cluster uniformity needed to pass from the cubic smoothed
explicit formula back to the classical simple zero kernel without losing its
amplitude scale.  It is quantitative rather than merely a pointwise limit.

## Claim boundary

The threshold depends on the finite pole set.  No uniform estimate over an
unbounded zero family is claimed, and the contour second difference remains
uncontrolled.  This does not prove an unconditional oscillation theorem or RH.
