# Moving Right-Edge Exceptional Cluster Design

## Goal

Replace the fixed exceptional cluster by a finite cluster that grows with the
explicit-formula truncation height.

## Definition

For a height schedule `height`, target exponent `beta`, and scale `x`, define

```text
movingRightEdgeExceptionalCluster height beta x
```

as the union of:

- every nontrivial zero with `abs(rho.im) <= height x` and
  `beta <= rho.re`;
- every real-ordinate nontrivial zero.

The second component is the existing real-ordinate adjoin used by the actual
transfer chain.

## Pointwise properties

At every scale:

- the cluster is conjugation invariant;
- every real-ordinate nontrivial zero is captured;
- every positive-ordinate zero visible below `height x` but outside the
  cluster satisfies `rho.re < beta`;
- increasing the height enlarges the cluster.

Thus the moving positive outside-cluster cap is automatic. It does not become
a global zero-free hypothesis because the exceptional cluster itself grows
with height.

## Exact explicit formula

Define the moving visible main and moving signed complement by substituting
the scale-dependent cluster into the existing actual zero sums. The actual
relative PNT error then has the pointwise exact decomposition

```text
error(x)
  = movingMain(x)
  + closedRealAxis(x)
  + explicitFormulaRemainder(x)
  + movingComplement(x).
```

## Next bridge

The remaining theorem is a uniform target-amplitude bound for the moving
complement. The fixed-cluster proof chooses a norm lower bound depending on
one fixed finset; the moving proof must dominate every low layer by the
empty-cluster polynomial-envelope mass and treat the high layer using the
automatic pointwise cap.

## Boundary

This module constructs the dynamic decomposition but does not yet prove the
moving complement negligible or supply moving-cluster anti-cancellation.
