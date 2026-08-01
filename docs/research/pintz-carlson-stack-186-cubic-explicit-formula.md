# Stack 186: Complete finite-height cubic explicit formula

## Goal

Combine Stack 185's actual cubic zeta residues with Stack 184's complete
third-order Perron approximation to the von Mangoldt second Riesz mean.

## Contour shift

Package the bottom, top, and new left edge into
`thirdOrderContourRemainder`.  The right Perron line then satisfies

```text
right cubic integral
  = finite cubic residue sum - thirdOrderContourRemainder.
```

The finite residues are

```text
x                                  at the pole 1,
-m(rho) x^rho / rho^3             at a zeta zero rho.
```

## Complete explicit formula

Combining the contour identity with the complete right-line Perron estimate
gives

```text
norm((residue sum - contour remainder) - secondRieszChebyshevPsi(x))
  <= tsum_n Lambda(n) (x/n)^c / (8 pi^3 W^2).
```

Thus the actual zeta zeros, actual contour remainder, actual PNT second Riesz
mean, and explicit quadratic Perron truncation error now occur in one theorem.

## Claim boundary

No bound on `thirdOrderContourRemainder` is supplied yet.  The theorem is an
exact finite-height explicit formula with an explicit right-line truncation
error, not yet a twice-de-smoothed PNT Omega theorem.
