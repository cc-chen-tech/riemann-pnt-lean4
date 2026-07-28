# Actual Carlson window-energy bidirectional PNT transfer

## Verified transfer shape

The selected finite Carlson cluster `S` extends the prescribed seed `S0`.
At the selected height, normalize both visible-cluster pieces by

```text
targetZeroPowerAmplitude beta m.
```

The external lower input is now one quantitative package:

```text
HasFarWindowEnergySeparation
  normalizedSeed
  normalizedExtension
  c
  loss
  mainCap.
```

Subject to `0 < loss`, `0 < c - loss`, and `c < mainCap`, the theorem returns
the same `S` together with:

```text
relativeChebyshevPsi0Error(m) -> 0;
zero support for S \ S0;
the Carlson complementary real-part gap;
an actual psi0-error witness at ((c - loss) / 2) * x^beta.
```

## Why only unsigned

Square-energy separation counts points where the seed has large absolute
value.  It does not determine how those points split between positive and
negative signs.  Therefore this facade proves only the unsigned transfer.
A signed facade requires separate signed local information and is not claimed.

## Remaining analytic theorem

The unproved input is the normalized far-window energy separation itself:
a local seed square-sum lower bound, a seed pointwise cap, and an extension
bad-point square-sum upper bound with a common quantitative cutoff `K`.
No unconditional Omega theorem or RH consequence is asserted.
