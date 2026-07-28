# Positive coefficient mass below the Carlson total weight

## New comparison direction

For a finite family `s` of actual nontrivial zeta zeros satisfying

```text
0 < Im rho
sigma < Re rho,
```

the theorem
`finite_actualCarlsonHighPositiveZeroCoefficientMass_le_tsum`
proves

```text
sum_{rho in s} multiplicity(rho) / |rho|
  <=
sum'_{Carlson positive indices i}
  multiplicity(rho_i) / |rho_i|.
```

The right side is finite when `1/2 < sigma < 1`.

The ordinary-finset facade
`finiteVisibleClusterCoefficientMass_le_actualCarlsonPositiveZeroWeight_tsum`
accepts the three pointwise properties directly, so later dynamic-package
modules do not need to expose subtype encodings.

## Proof mechanism

The Carlson shell construction covers every high positive zero.  The chosen
index map is injective, so the finite zero family maps to a finite subset of
the Carlson index.  Exact coefficient preservation identifies the finite
cluster mass with the mapped finite index sum, and summability bounds that sum
by the full `tsum`.

## Role in the dynamic cap

This is the previously missing upper-comparison direction.  To obtain a full
dynamic package cap, the next steps are to:

1. instantiate the finite family with the positive part of the moving
   equal-real-part package;
2. bound the negative part by conjugation; and
3. add the fixed finite real-ordinate coefficient mass.
