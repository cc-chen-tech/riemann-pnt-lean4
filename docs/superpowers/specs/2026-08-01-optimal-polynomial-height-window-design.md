# Minimax-Optimal Polynomial-Height Window

## Objective

Optimize the strict polynomial-height transfer rather than merely exhibit a
feasible exponent.

## Four-margin model

The width

```text
G = (beta - sigma) - (1 - beta) = 2 beta - 1 - sigma
```

must pay for four independent strict margins:

1. contour threshold to the inner selected exponent;
2. inner-to-outer selected-height separation;
3. logarithmic slack `epsilon`;
4. final density exponent slack.

If all four margins are at least `r`, adding the constraints gives `4r <= G`.
Thus `r <= G/4`.

## Optimal construction

```text
r       = G / 4
inner   = 1 - beta + r
outer   = 1 - beta + 2r
epsilon = r
```

All four constraints hold with equality, so the common safety margin is
minimax optimal. The resulting selected height also carries the actual
power-normalized explicit-formula remainder certificate.

## Claim boundary

Optimality is for this explicit four-margin linear model. It does not optimize
Sharp's anti-cancellation constants, construct signed witnesses, prove Omega,
or imply RH.
