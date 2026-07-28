# Actual zero package to visible-cluster transfer

This step closes the representation mismatch between the fixed
equal-real-part package used by the mean-square argument and the dynamic
visible-cluster main used by the Carlson transfer.

The theorem chain proves:

1. `equalRealPartZeroPackage T beta` is invariant under conjugation.
2. Its multiplicity-weighted contribution on the positive real axis is real.
3. Once `T <= H x`, the dynamic visible relative PNT zero sum is exactly
   `-x^-1` times that fixed package contribution.
4. The mean-square witness therefore has the exact visible-main scale
   `sqrt(actualEqualRealPartZeroPackageEnergy T beta L) * x^(beta - 1)`.

The energy coefficient is not replaced by `1`.  A nontrivial downstream
oscillation statement must retain its positivity and compare all Carlson and
explicit-formula losses with this same coefficient.

This module does not estimate the outside-cluster tail, does not prove a
Guth--Maynard density theorem, and does not assert RH or an unconditional
Omega theorem.
