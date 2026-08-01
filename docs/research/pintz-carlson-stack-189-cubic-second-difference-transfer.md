# Stack 189: cubic explicit-formula second-difference transfer

## Result

This slice transports three pointwise complex approximation errors through the
second logarithmic forward difference.  If the errors at
`x`, `x exp(h)`, and `x exp(2h)` are bounded by `E0`, `E1`, and `E2`, then the
real second-difference error is at most

```text
E2 + 2 E1 + E0.
```

Combining this estimate with Stack 188 gives explicit one-sided bounds for the
actual unsmoothed Chebyshev function at the two endpoints.

## Why this is needed

The cubic Perron formula controls the second Riesz mean, while the PNT concerns
`chebyshevPsi`.  Stack 188 supplies the arithmetic de-smoothing sandwich; this
slice proves that contour and truncation errors survive that operation with the
correct `1, 2, 1` loss.

## Claim boundary

This theorem accepts three pointwise approximants.  It does not yet prove that
the three cubic contour shifts use a common pole set, nor does it bound their
twice-differenced contour remainder.  It therefore does not establish an
unconditional oscillation theorem or RH.
