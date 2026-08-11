# Synchronized third-order good height

Separate decay theorems are not enough if their height witnesses may differ.
This slice selects one height

```text
T in [x^(3/4), x^(3/4) + 1]
```

that simultaneously satisfies:

- the genuine third-order `goodHeight` condition;
- norm of the negative-left-edge contour remainder below `epsilon`;
- the Perron truncation majorant, normalized by `x^beta`, below `epsilon`.

The proof combines the good-height contour existence theorem with the uniform
Perron majorant valid for every height in the same unit window. The Perron
exponent is `c - 3/2 - beta`, strictly negative for `2/3 < beta` and `c <= 2`.

This theorem is the analytic-error adapter needed by the actual smoothed
explicit formula. It does not provide Gram/Schur occupancy, prove an Omega
theorem, imply RH, or identify L2 strip energy with a pointwise residue sum.
