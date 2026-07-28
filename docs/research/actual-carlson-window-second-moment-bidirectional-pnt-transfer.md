# Actual Carlson window-second-moment bidirectional PNT transfer

## Unified verified interface

For the finite zero-supported Carlson extension `S \ S0`, define the
normalized complementary contribution

```text
u(m) =
  dynamicVisibleClusterPNTMain T (S \ S0) m
    / targetZeroPowerAmplitude beta m.
```

The unsigned theorem combines:

```text
far-window second-moment advantage for seed-good points and u
relativeChebyshevPsi0Error(m) -> 0
Carlson support and complementary real-part gap
```

to transfer oscillation to the actual `psi0` error at scale

```text
((c - loss) / 2) * x^beta.
```

The signed theorem requires separate second-moment window certificates for
positive and negative seed-good predicates.  Both use the same normalized
extension and the same selected Carlson cluster.

## Honest boundary

This theorem is conditional on the far-window normalized second-moment
certificate.  It does not prove that certificate for zeta zeros, formalize a
Guth-Maynard estimate, prove an unconditional Omega result, or imply RH.

The remaining analytic task is now explicit: lower-bound the number of
seed-good points in suitable far windows while controlling the normalized
extension square sum strongly enough to satisfy the strict budget.
