# Moving-Cluster Complement Majorant Design

## Goal

Prove that the actual signed zero complement outside the moving right-edge
exceptional cluster is negligible on the target-zero amplitude scale.

## Uniform low-layer majorant

The fixed-cluster proof chooses a norm lower bound depending on one fixed
cluster `S`. That argument cannot be applied directly to `S(x)`.

Instead, at every scale the selected low layer outside `S(x)` is a subset of
the polynomial-envelope low layer outside the empty cluster. Consequently all
moving low layers are controlled by one fixed `S = empty` two-height mass.
The existing Carlson limit for that empty-cluster mass is therefore uniform in
the moving cluster.

## High layer

For a general moving cluster family, assume a pointwise cap on its selected
high layer. This embeds every moving high layer in the same actual Carlson
strip and supplies the existing strip-mass limit.

For

```text
S(x) = movingRightEdgeExceptionalCluster height tau x,
```

the cap is automatic: every visible positive zero outside `S(x)` has real
part strictly below `tau`.

## Full signed complement

The moving right-edge cluster is pointwise conjugation invariant and contains
the complete real-ordinate zero slice. Hence:

- the real-ordinate outside tail is identically zero at nonnegative heights;
- the full nonreal tail is bounded by twice the positive tail;
- the signed complement is bounded by the full tail norm.

These bounds transfer positive-tail negligibility to the actual signed moving
complement.

## Output

The final theorem proves

```text
TargetAmplitudeNegligible
  (targetZeroPowerAmplitude beta)
  (movingRightEdgeOutsideClusterPNTComplement height tau).
```

## Boundary

This closes the moving complementary-zero estimate. A lower oscillation
theorem still needs a far target-amplitude witness for the moving visible
cluster.
