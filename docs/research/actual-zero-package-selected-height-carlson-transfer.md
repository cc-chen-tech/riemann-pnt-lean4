# Actual zero-package energy at a selected Carlson height

This module closes the height-interface mismatch between the actual
equal-real-part zero-package witness and the repository's constructible
Carlson good-height certificates.

The theorem consumes:

- a cofinal selected height `H(x)`;
- an existing
  `ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate`;
- an `ActualSelectedHeightExplicitFormulaRemainderCertificate`;
- a nonempty actual package `equalRealPartZeroPackage T beta`.

It produces both natural-point relative PNT decay and a far-point lower
witness at the exact scale

```text
sqrt(actualEqualRealPartZeroPackageEnergy T beta L)
  * x^(beta - 1) / 2.
```

The logarithmic window `L` is chosen internally from package nonemptiness.
The theorem does not construct the selected-height remainder certificate,
does not remove the strict outside-cluster real-part condition embedded in
the Carlson certificate, and does not claim an unconditional Omega theorem
or RH.
