# Fixed-cluster reciprocal boundary-mass design

## Objective

Combine the Stack158 reciprocal low layer with the existing Carlson high-tail
boundary limit for an arbitrary fixed cluster.

## Result

The selected positive-ordinate zero sum outside `S`, normalized by the target
`x^(beta-1)` scale, is eventually below

```text
actualCarlsonOutsideClusterBoundaryMass sigma beta S + delta
```

for every positive `delta`.

The low layer now requires only

```text
sigma - beta + epsilon < 0,
```

and no longer requires a uniform zero-norm lower bound or the old
`sigma - beta + alpha + epsilon < 0` margin.

## Next slice

Conjugation and the real-ordinate tail will convert this positive-zero bound
into a complete fixed-cluster zero-sum bound.  The explicit formula can then
transfer the actual equal-real-part package's mean-square sign alternative at
the weaker threshold `sigma < beta`.
