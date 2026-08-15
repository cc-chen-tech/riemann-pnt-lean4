# Third-order dynamic Perron error at target scale

This slice closes the Perron-error side of the separated-height construction.
The exact nonnegative truncation majorant factors as

```text
x^c / (8 * pi^3 * W^2) * vonMangoldtLSeriesNorm (c - 1).
```

For every selected height

```text
T in [x^(3/4), x^(3/4) + 1],  W = T / (2*pi),
```

normalization by `x^beta` gives the uniform power majorant

```text
vonMangoldtLSeriesNorm (c - 1) / (2*pi)
  * x^(c - 3/2 - beta).
```

The exponent is strictly negative whenever `2/3 < beta` and `c <= 2`.
Thus the same high contour window used for the genuine third-order contour
remainder also makes the normalized Perron truncation error tend to zero.

This result concerns analytic errors only. It does not supply Gram/Schur
occupancy, prove an Omega theorem, imply RH, or identify an L2 energy with a
pointwise residue sum.
