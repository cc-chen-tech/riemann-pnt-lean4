# Actual explicit-formula unified target transfer design

## Scope

This stack is the first concrete composition of:

- the actual zeta-zero target-amplitude tail from stacks36-39;
- the closed real-axis explicit-formula term;
- a polynomial-height explicit-formula remainder certificate;
- the existing abstract unified PNT upper/lower transfer.

It does not prove the remainder certificate or the visible-cluster
oscillation witness internally.  Those remain explicit inputs.

## Exact decomposition

The repository already proves

```text
relative PNT error
  = visible cluster main
    + (closed real-axis term
       + explicit-formula remainder
       + signed outside-cluster complement).
```

The three residual terms are negligible relative to
`targetZeroPowerAmplitude beta`:

- the closed real-axis term when `0 < beta`;
- the explicit-formula remainder from
  `ActualPolynomialExplicitFormulaRemainderCertificate alpha` and
  `1 - beta < alpha`;
- the signed outside-cluster complement because its absolute value is
  bounded by the stack39 full tail.

## Unified output

Given a far target-amplitude witness for the visible cluster main, the
existing abstract transfer returns simultaneously:

```text
some fixed-rate natural-point PNT convergence
```

and

```text
a far target-amplitude witness for the actual relative PNT error
at half the original amplitude.
```

Thus the same theorem combines the upper and lower directions for the same
explicit-formula object.

## Claim boundary

The result is conditional on:

- the explicit high-layer real-part cap;
- the stack36/37 exponent margins;
- conjugation invariance and the strict real-ordinate condition;
- an actual polynomial remainder certificate;
- a visible-cluster oscillation witness.

It is not RH and does not yet construct the cluster witness from a zeta zero.
