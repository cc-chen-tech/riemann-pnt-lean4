# Stack 175: kernel order at the reciprocal-height scale

## General calculation

Assume a kernel produces the relative remainder majorant

```text
C H(x)^(-k) (1 + log x)^2
```

at `H(x) = x^alpha`.  Normalize it by the natural single-high-zero scale

```text
x^(beta - 1) / H(x).
```

The resulting power-log majorant is

```text
C x^(1 - beta - (k - 1) alpha) (1 + log x)^2.
```

It tends to zero under the strict criterion

```text
1 - beta < (k - 1) alpha.
```

## Sharp design consequence

- `k = 1`: the height disappears and the Stack174 obstruction remains.
- `k = 2`: the criterion becomes exactly `1 - beta < alpha`, the contour
  window already required by the current selected-height construction.

Thus a genuine second-order-in-height smoothed remainder is the first kernel
order capable of preserving the `x^beta / |rho|` scale without strengthening
the polynomial-height window.

## Claim boundary

This stack proves the transfer criterion, not the existence of a zeta
explicit-formula kernel with an `H^(-2)` remainder.  Constructing and auditing
that analytic kernel remains the next mathematical task.  No RH, zero
reproduction, or simultaneous signed Omega conclusion is asserted.
