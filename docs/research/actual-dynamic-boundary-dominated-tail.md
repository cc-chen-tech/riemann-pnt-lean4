# Actual dynamic boundary tail by dominated convergence

## Main result

Fix a Carlson threshold `sigma > 1/2`.  The repository already proves that
the actual multiplicity weights

```text
analyticMultiplicity(rho) / |rho|
```

are summable over positive nontrivial zeros with `Re rho > sigma`.

For a fixed target boundary `beta`, the new module deletes at scale `m` every
visible zero on `Re rho = beta` by using the cofinal dynamic equal-real-part
package.  Each fixed indexed zero then behaves in one of two ways:

- if `Re rho < beta`, its normalized power tends to zero;
- if `Re rho = beta`, cofinality of the height makes it eventually belong to
  the dynamic package, so its outside-package term is eventually zero.

Every term is bounded by the summable reciprocal-norm weight.  Tannery's
theorem therefore gives convergence of the complete actual high tail.

## Lean conclusion

Under a right-edge hypothesis

```text
forall positive nontrivial rho, Re rho <= beta,
```

the module proves

```text
sum_{rho outside dynamic boundary package}
  ||relative zero contribution at m||
  / m^(beta - 1)
  -> 0
```

for all positive zeros with `Re rho > sigma`.

## Significance

This removes the need for a uniform positive real-part gap in the high
near-boundary tail.  It also explains why the earlier single-bucket
moving-gap obstruction is not the final word: keeping the reciprocal-zero
weights and applying dominated convergence is strictly sharper than first
replacing the entire high tail by a global count times a worst-case kernel.

## Remaining boundary

The theorem assumes that `beta` is a genuine global right edge for positive
nontrivial zeros.  It controls only the high tail `Re rho > sigma`; the
low-real-part layer and explicit-formula contour terms must still be combined
with existing modules.

The dynamic boundary package itself may grow with the height.  Turning its
main term into an oscillation lower bound requires a compatible finite
approximation or an infinite almost-periodic energy argument.  No
unconditional Omega theorem or RH consequence is claimed here.
