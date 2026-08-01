# Near-optimal prescribed-height anchor design

## Objective

Optimize the target anchor while keeping the polynomial height exponent
`alpha` fixed.  Stack156 used the conservative anchor constraint
`beta >= 1 - alpha / 2`; the sharp contour constraint is only
`beta > 1 - alpha`.

## Frontier

Define

```text
beta_floor = max(beta_mid(sigma), 1 - alpha).
```

Every feasible contour window with outer exponent `alpha` and anchor at least
`beta_mid(sigma)` satisfies `beta_floor <= beta`.

For `0 < delta < alpha`, define

```text
beta_delta = max(beta_mid(sigma), 1 - alpha + delta).
```

Then

```text
beta_floor <= beta_delta <= beta_floor + delta
```

and `beta_delta < 1`.  The midpoint between `1 - beta_delta` and `alpha`
provides a strict selected-height window.

## Transfer and boundary

The resulting actual selected height remains eventually bounded by
`x^alpha`, while the running visible-zero boundary uses the improved anchor
`beta_delta`.  The full PNT upper and conditional signed transfer therefore
holds at a target anchor arbitrarily close to the fixed-height frontier.

The signed conclusion still assumes positive and negative visible-main
witnesses.  No anti-cancellation theorem, unconditional Omega result, or RH
claim is made.
