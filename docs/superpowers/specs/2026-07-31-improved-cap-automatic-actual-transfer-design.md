# Improved Cap Automatic Actual Transfer Design

## Goal

Apply the strict improvement in the admissible real-part cap range directly
to the actual PNT transfer.

## Inputs

- `2 / 3 < beta < 1`;
- `1 / 2 < theta < beta`;
- `theta < jointTwoHeightImprovedGlobalCapThreshold beta`;
- a conjugation-invariant base cluster;
- a global positive nontrivial-zero bound `rho.re <= theta`.

## Construction

The exact cap criterion from stack62 proves

```text
1 - beta < jointTwoHeightGlobalOuterExponentCeiling beta theta.
```

Choose a positive `eta` strictly inside this gap. Stack60 then supplies:

- the unique globally optimal density threshold;
- a strip endpoint above both `sigma` and `theta`;
- an exponent `alpha = globalCeiling - eta`;
- the actual selected-good-height explicit-formula transfer.

## Result

For every uniform natural-point good-height selection, a unit target-amplitude
visible-cluster witness implies both:

- natural-point relative Chebyshev error convergence to zero;
- an actual relative-error far witness at half target amplitude.

The selected strict loss and exact truncation identity are returned.

## Boundary

The new threshold automatically closes the upper/remainder arithmetic. The
visible-cluster witness remains the explicit anti-cancellation boundary.
