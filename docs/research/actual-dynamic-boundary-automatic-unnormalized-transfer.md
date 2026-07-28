# Dynamic-boundary transfer at the unnormalized PNT scale

## Lean conclusion

`actualDynamicBoundaryAutomaticPsi0ErrorWitnessTransfer` concludes

```text
0 < c - loss
```

and

```text
for every X, there exists x >= X such that
  (c - loss) * x^beta <= |psi0(x) - x|.
```

This is the unnormalized form of the dynamic-boundary transfer.  The preceding
relative theorem has scale `x^(beta - 1)`; multiplication by the positive
sample point gives exactly `x^beta`.

## Zero coefficient

The theorem leaves `c` abstract on purpose.  A local zero theorem may set `c`
to an expression containing analytic multiplicity and the reciprocal-zero
factor `1 / |rho|`.  The density and explicit-formula transfer preserves that
coefficient up to an arbitrary fixed `loss` with `0 < loss < c`.

## Remaining input

The moving equal-real-part package witness remains external.  This module does
not prove sharp pi-over-two oscillation, signed oscillation, a reproduction
tree, RH, or an unconditional Omega theorem.
