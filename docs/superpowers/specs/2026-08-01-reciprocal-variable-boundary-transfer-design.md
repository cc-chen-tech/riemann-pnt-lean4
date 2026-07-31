# Reciprocal Variable-Boundary Transfer Design

## Goal

Install the reciprocal-zero low-layer estimate in the monotone variable-
boundary PNT transfer, so the moving right edge uses the strict margin

```text
sigma - beta0 + epsilon < 0
```

instead of paying the selected-height exponent `alpha`.

## Construction

The moving target exponent satisfies `beta0 <= beta(m)` eventually. The
physical low-layer sum is bounded by

```text
m^(sigma-1) * GlobalReciprocalZeroMultiplicity(H(m)).
```

The moving amplitude denominator is at least the fixed `beta0` amplitude.
After the proved logarithmic-square reciprocal bound and the polynomial height
ceiling, the normalized majorant is

```text
C * (alpha + 2)^2 * m^(sigma-beta0) * log(m)^8.
```

The existing absorption-or-gap theorem continues to control the high moving
tail. Real zeros, contour remainder, coefficient cap, and signed witness
transfer are reused unchanged.

## Public result

The final theorem simultaneously gives an eventual upper bound for the real
PNT error and conditional positive/negative unnormalized witnesses at the
exact variable scale `x^beta(x)`. The lower conclusion still requires both
visible-main witnesses.

## Claim boundary

This is a genuine improvement of the actual variable-boundary residual, but
does not construct anti-cancellation witnesses, prove RH, or prove an
unconditional Omega theorem. Protected, Sharp, and VK-edge modules remain
untouched.
