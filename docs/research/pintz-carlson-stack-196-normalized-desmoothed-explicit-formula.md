# Stack 196: normalized de-smoothed explicit formula

## Result

The automatically integrable bottom, top, and left paths are assembled into
one de-smoothed contour remainder.  The original cubic contour second
difference divided by `h^2` is proved equal to this actual first-order contour.

The complete normalized expression is then identified exactly as

```text
x * ((exp h - 1) / h)^2
+ sum_rho (-m(rho) x^rho / rho) * M(rho,h)
- de-smoothed first-order contour remainder,
```

where `M(rho,h)` is the quantitative multiplier controlled in Stack 193.

The module also provides a direct norm budget reducing the assembled contour
to the norms of its three edge integrals divided by `2 pi`.

## Mathematical role

The pole at one, the finite zeta-zero sum, and the contour remainder now use
one normalized first-order kernel.  This is the concrete common object on
which Pintz pointwise bounds and Carlson zero-density aggregation can act.

## Claim boundary

The edge-integral norms remain to be bounded using zeta logarithmic-derivative
estimates and the chosen contour geometry.  No unconditional oscillation
theorem or RH is claimed.
