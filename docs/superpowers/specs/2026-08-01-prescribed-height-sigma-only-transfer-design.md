# Prescribed-height sigma-only transfer design

## Objective

For every prescribed polynomial exponent `0 < alpha < 1`, construct an actual
selected height eventually bounded by `x^alpha` and install it in the audited
reciprocal sigma-only PNT transfer.

## Automatic anchor

Let `beta_mid(sigma)` be the Stack153 automatic anchor and set

```text
beta_alpha = max(beta_mid(sigma), 1 - alpha / 2).
```

Then `beta_alpha` remains strictly to the right of `sigma` and every fixed
real-ordinate nontrivial zero.  Moreover,

```text
1 - beta_alpha <= alpha / 2 < alpha.
```

Choose the inner selected-height exponent as the midpoint

```text
inner = (1 - beta_alpha + alpha) / 2.
```

This gives the strict contour window

```text
1 - beta_alpha < inner < alpha.
```

The selected good height is therefore eventually at most the prescribed
Carlson polynomial height `x^alpha`, while the actual contour-remainder
certificate still applies.

## Transfer

The reciprocal low-layer slack is

```text
epsilon = (beta_alpha - sigma) / 2,
```

so `sigma - beta_alpha + epsilon < 0`.  All hypotheses of the existing
monotone variable-boundary reciprocal transfer are then automatic except the
positive and negative visible-main witnesses.

## Tradeoff and claim boundary

This is a Pareto statement, not a free reduction of height.  As `alpha`
decreases, the automatic anchor is forced toward one, and therefore the target
amplitude and visible-zero boundary also change.  The theorem does not hold a
fixed target zero layer while sending `alpha` to zero.

The signed conclusion remains conditional on visible-main witnesses.  No
anti-cancellation theorem, unconditional Omega result, or RH claim is made.
