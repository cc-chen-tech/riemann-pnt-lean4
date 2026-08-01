# Stack 191: cubic residue second-difference kernel

## Result

This slice expands the three-point cubic explicit-formula approximant exactly.
After taking the logarithmic second forward difference, it separates into:

```text
zeta pole at one
+ common finite sum of cubic zero kernels
- second difference of the bottom/top/left contour remainder.
```

The final theorem eliminates the three auxiliary residue functions and gives
endpoint Chebyshev bounds directly in terms of this decomposition and the
actual cubic Perron truncation budget.

## Exact zero kernel

For a non-one pole `rho`, the extracted term is

```text
-m(rho) * ((x exp(2h))^rho - 2 (x exp(h))^rho + x^rho) / rho^3.
```

This is the discrete cubic kernel whose small-`h` normalization should recover
the classical simple zero kernel at the correct `x^rho / rho` scale.

## Claim boundary

No small-`h` kernel limit or uniform contour estimate is proved here.  The
result is an exact finite-height identity and endpoint transfer, not an
unconditional oscillation theorem or RH.
