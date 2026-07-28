# Window second moment to bad-point count

## Verified arithmetic implication

For a finite natural-number window `G`, a real sequence `u`, and
`threshold > 0`, define the bad subset by

```text
B = {m in G | threshold <= |u m|}.
```

The verified finite inequality is:

```text
sum (u m)^2 over B < card(G) * threshold^2
  -> card(B) < card(G).
```

Every bad point contributes at least `threshold^2`, so the conclusion is a
strict counting consequence of the second-moment budget.

The far-window wrapper preserves an arbitrary seed-good predicate and produces
the `HasFarWindowCardAdvantage` premise consumed by the window-count
anti-cancellation transfer.

## Intended normalization

In an actual-PNT application, `u(m)` should be a complementary zero-cluster
contribution normalized by the target zero amplitude.  The constant threshold
then represents the allowed loss.  Establishing that normalization and its
second-moment estimate is a separate analytic task.

This module contains no Carlson, Guth-Maynard, or zeta second-moment theorem.
