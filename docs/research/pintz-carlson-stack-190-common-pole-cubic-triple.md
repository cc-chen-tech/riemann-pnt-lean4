# Stack 190: common-pole cubic triple transfer

## Result

The finite-height cubic explicit formula now retains the completeness property
of its pole set: every zeta zero, and the pole at one, inside the rectangle is
included.  Classification plus completeness proves that the pole Finset is
unique and hence independent of the positive sample point `x`.

The main theorem applies the actual cubic formula at

```text
x, x exp(h), x exp(2h)
```

with one common pole set.  It then invokes Stack 189 to produce explicit
endpoint bounds for the unsmoothed Chebyshev function.  The approximants are
the actual cubic zero-residue sum minus the bottom, top, and left contour
remainder, and the error is the actual cubic Perron truncation budget with
weights `1, 2, 1`.

## Mathematical role

This closes a genuine interface gap.  Three unrelated existential pole sets
cannot be second-differenced as one zero sum.  Completeness shows that the sets
are extensionally equal, without assuming a zero enumeration or adding an
analytic hypothesis.

## Claim boundary

The theorem does not yet estimate the twice-differenced contour remainder or
the resulting common-pole zero kernel.  It therefore does not prove an
unconditional Omega theorem or RH.
