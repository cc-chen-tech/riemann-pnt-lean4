# Canonical Polynomial Sigma-Only Unified Transfer

## Objective

Eliminate the target anchor and real-ordinate separation from Stack143 using
the exact critical-half threshold and the finite real-zero bottleneck.

## Construction

```text
B(sigma) = max(real-zero bottleneck, (1 + sigma) / 2)
beta0    = (B(sigma) + 1) / 2
```

Because both entries of the maximum are strictly below one, `beta0` is
strictly between the joint obstruction and one. It therefore satisfies the
canonical polynomial target condition and excludes every real-ordinate zero.

This improves the previous sigma-only bookkeeping obstruction
`sigma + alpha + epsilon = (3 + sigma) / 4` to the exact canonical threshold
`(1 + sigma) / 2` before adjoining the real-zero bottleneck.

## Remaining inputs

Only positive and negative natural-point witnesses for the concrete visible
running-boundary package remain.

## Claim boundary

Those witnesses are not constructed here. The theorem is therefore a fully
automatic analytic/density transfer conditional on anti-cancellation, not an
unconditional Omega theorem or RH.
