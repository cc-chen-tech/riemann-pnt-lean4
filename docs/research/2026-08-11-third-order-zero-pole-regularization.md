# Third-order zero-pole regularization

## Result

The genuine third-order explicit-formula kernel is now regularized on compact
sets that contain zero. It is decomposed into

    analytic remainder
      + finite simple-pole sum
      + quadratic * z^(-2)
      + cubic * z^(-3).

For every nonzero zeta zero p, the simple-pole residue has the correct cubic
Perron scale

    -multiplicity(p) * x^p / p^3.

The cubic coefficient at zero is identified explicitly as

    -zeta'(0) / zeta(0).

The simple residue at zero and the quadratic coefficient are supplied
existentially by the analytic Taylor remainder and the finite nonzero-pole
corrections.

## Why this is needed

The earlier third-order rectangle formula assumed a positive left edge and
therefore avoided zero. The dynamic contour-decay theorem instead uses the
left line Re(s) = -1. Moving that line across zero is not a harmless deletion
of the positivity assumption: division by s^2 turns the logarithmic-derivative
pole at zero into a cubic principal part.

This theorem records that principal part explicitly. Together with the
separate boundary-rectangle lemmas showing that z^(-2) and z^(-3) have zero
closed-boundary integral when the boundary avoids zero, it provides the
correct prerequisite for a negative-left-edge rectangle formula.

## Scope

This slice proves only the local meromorphic decomposition. It does not yet:

- assemble the negative-left-edge boundary rectangle identity;
- identify the remaining simple residue at zero in closed form;
- connect the corrected residue sum to the smoothed Chebyshev function;
- bound the medium/high zero tail;
- prove an Omega theorem or RH.
