# Fixed-cluster reciprocal full residual design

Stack159 controls the positive-ordinate zero sum outside a fixed cluster by
`boundaryMass + delta`.  This slice doubles that coefficient by conjugation,
absorbs the strictly-left real-ordinate tail, and then uses the actual explicit
formula to include the closed-axis and contour terms.

The final residual coefficient is

```text
2 * actualCarlsonOutsideClusterBoundaryMass sigma beta S + delta.
```

The low-layer margin remains `sigma - beta + epsilon < 0`; no `+ alpha` term
or uniform reciprocal-denominator guard is reintroduced.

The module supplies normalized and unnormalized residual forms.  The latter is
the direct input for the finite zero-package sign-alternative transfer.  This
slice itself does not yet claim that sign alternative, an unconditional Omega
theorem, or RH.
