# Target-Pair Annihilator Step-Average Audit

## Verified spectral results

The new module proves the exact step multiplier

```text
2 (cos(lambda h) - cos(gamma h))
```

and its exact square integral on `[0,H]`. For fixed positive distinct
frequencies `lambda` and `gamma`, the normalized square integral tends to
`4`. Consequently, every finite collected family of positive non-target
frequencies is separated simultaneously for all sufficiently large `H`.

For a finite exponential polynomial, the coefficientwise annihilator is
connected directly to the repository's existing diagonal/off-diagonal
mean-square theorem. A nonzero collected finite package therefore has
positive step-averaged diagonal energy.

## Conditional zeta interpretation

`SameEdgeResidualPackage` is explicit input data. It represents a finite
nonzero residual frequency package whose frequencies avoid the selected zero
ordinate. Given this package, the positive averaged diagonal-energy theorem is
proved.

The branch does not prove that the Riemann zeta function supplies such a
package for every selected off-critical-line zero. To turn the spectral
statement into a theorem about the complete normalized PNT error, one still
needs both:

1. an independently identified same-edge or arbitrarily near-edge residual
   zero contribution;
2. a uniform explicit-formula tail comparison showing that the complete
   remainder does not erase the finite-package energy.

## No-go boundary

The selected conjugate pair is annihilated pointwise, and the module proves
that this pair alone cannot supply any positive lower bound after the
annihilator is applied.

If the selected pair is the unique rightmost pair and all remaining zero
contributions have real part at most `beta - delta`, the normalized residual
is compatible with decay of order `exp(-delta y)`. Step averaging removes
fixed-step frequency collisions, but it does not remove this real-part decay.

## Claims not made

- No theorem says that one off-line zero forces another zero with the same
  real part.
- No positive lower bound is proved for the complete zeta residual without an
  additional package and tail hypothesis.
- No Carlson zero-density contradiction is proved.
- RH is not proved.
