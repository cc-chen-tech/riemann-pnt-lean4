# Stack 192: cubic kernel factorization

## Result

The normalized discrete cubic zero kernel now factors exactly as

```text
classical simple zero kernel
* ((exp(h rho) - 1) / (h rho))^2.
```

The simple factor is `-m(rho) x^rho / rho`.  Its norm is proved to be exactly

```text
m(rho) * x^(Re rho) / |rho|.
```

Thus the cubic de-smoothing route preserves the correct zero amplitude scale;
all kernel distortion is isolated in one explicit multiplier.

The pole at one is also factored as `x` times the real multiplier
`((exp h - 1) / h)^2`, which identifies the deterministic centering error in
the passage from `psi` to `psi - x`.

## Claim boundary

This slice proves exact identities.  It does not yet prove a uniform bound or
limit for the multiplier, nor does it estimate the contour second difference.
It does not prove an unconditional oscillation theorem or RH.
