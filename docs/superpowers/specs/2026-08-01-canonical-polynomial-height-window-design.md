# Canonical Polynomial-Height Window

## Objective

Replace manually chosen polynomial exponents and logarithmic slack in the
power-scale transfer by an explicit, balanced construction.

## Construction

For the feasible interval `(1 - beta, beta - sigma)`, define

```text
G       = 2 beta - 1 - sigma
inner   = 1 - beta + G / 3
outer   = 1 - beta + 2 G / 3
epsilon = G / 6
```

The hypothesis `beta > (1 + sigma) / 2` is exactly `G > 0`.

The first third ensures target-amplitude contour decay. The gap between inner
and outer absorbs the selected-height unit window. The final half-third gives
strict negativity after the logarithmic loss.

## Output

The selected height at `inner` is eventually below `x^outer`, tends to
infinity, and carries the actual multiplicity-aware explicit-formula remainder
certificate at the power amplitude `x^(beta-1)`.

## Claim boundary

This constructs the analytic height and remainder certificate only. It does
not construct moving right-edge geometry or positive/negative cluster
witnesses, and therefore does not itself prove Omega or RH.
