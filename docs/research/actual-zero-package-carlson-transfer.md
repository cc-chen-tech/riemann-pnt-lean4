# Actual zero-package energy in the Carlson transfer

This step removes the coefficient mismatch between the actual
equal-real-part package and the existing unified Carlson transfer.

Let

`c = sqrt(actualEqualRealPartZeroPackageEnergy T beta L)`.

Under `0 < c`, the module proves that every residual negligible relative to
`targetZeroPowerAmplitude beta` is also negligible relative to
`c * targetZeroPowerAmplitude beta`.  It then combines:

1. the actual package far witness;
2. the cluster-excluded finite-strip Carlson certificate;
3. the closed real-axis decay;
4. the polynomial-height explicit-formula remainder certificate;
5. the exact actual visible-cluster decomposition.

The resulting PNT witness has coefficient `c / 2` on the relative
`x^(beta-1)` scale.  Equivalently, the unnormalized error scale is
`(c / 2) * x^beta`.

The theorem remains conditional on the finite-strip outside-cluster
certificate and the polynomial explicit-formula remainder certificate.  It
does not assert that these certificates exist for an arbitrary target zero,
does not prove an unconditional Omega theorem, and does not imply RH.
