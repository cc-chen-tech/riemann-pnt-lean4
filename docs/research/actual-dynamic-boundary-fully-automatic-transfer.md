# Fully automatic dynamic-boundary transfer

## Upper theorem

`actualDynamicBoundaryFullyAutomaticPNTUpperTransfer` derives

```text
|relativeChebyshevPsi0Error(m)|
  <
  (C_Carlson(sigma) + eta) * m^(beta - 1)
```

eventually, where

```text
C_Carlson(sigma)
  =
  2 * sum' positive Carlson reciprocal weights
  + fixed real-ordinate coefficient mass.
```

No moving-package coefficient cap is supplied externally.

## Bidirectional theorem

The bidirectional theorem uses the identical height schedule, strip margin,
right-edge hypotheses, and explicit-formula remainder certificate.  Its only
additional package-side input is a far witness with coefficient `c`.

It simultaneously returns:

```text
upper: (C_Carlson(sigma) + eta) * x^(beta - 1),
lower: (c - loss) * x^(beta - 1),
unnormalized lower: (c - loss) * x^beta.
```

Here `eta > 0` and `0 < loss < c` are arbitrary.

## Remaining mathematical boundary

The upper side is now automatic from the current Carlson and explicit-formula
inputs.  The remaining lower-side input is the local anti-cancellation theorem
for the moving equal-real-part package.  This module does not assert that
input, a sharp pi-over-two result, RH, or an unconditional Omega theorem.
