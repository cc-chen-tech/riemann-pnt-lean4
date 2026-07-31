# Natural Running-Maximum Zero Boundary Design

## Objective

Construct the moving exponent used by the unified Pintz-Carlson-explicit-formula
transfer instead of accepting it as an external function.  The construction
must work with the canonical selected good heights even though that height
schedule is not known to be monotone.

## Pointwise bottleneck

At natural sample `m`, form the finite set of real parts of
`positiveNontrivialZerosFinset (H m)`.  Insert `0` to handle an empty zero set
and take `Finset.max'`.  The resulting
`visiblePositiveZeroRealPartBottleneck H m` bounds every positive nontrivial
zero visible at the current height.

## Running boundary

Given a fixed lower anchor `beta0`, define recursively

```text
B(0)     = max beta0 bottleneck(0)
B(m + 1) = max B(m) bottleneck(m + 1).
```

This simultaneously gives:

- `beta0 <= B(m)` for every `m`;
- `B(m) <= B(m + 1)`, hence sampled monotonicity;
- every zero visible at `H(m)` has real part at most `B(m)`.

Extend the natural sequence to `Real -> Real` by

```text
beta(x) = B(Nat.floor x).
```

`Nat.floor_natCast` makes all natural samples definitionally recover `B(m)`.
No arbitrary-real right-edge statement is claimed or needed.

## Unified transfer

Specialize the Stack 113 canonical-good-height theorem with

```text
beta = naturalRunningVisibleZeroBoundaryReal
  (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha) beta0.
```

The construction automatically discharges:

- the eventual lower anchor;
- sampled monotonicity;
- the indexed visible right-edge hypothesis.

The theorem retains the Carlson numerical margin, the strict real-ordinate
zero gap below `beta0`, and independent positive and negative main-package
witnesses.

## Public declarations

- `visiblePositiveZeroRealPartBottleneck`
- `visiblePositiveZero_re_le_bottleneck`
- `naturalRunningVisibleZeroBoundary`
- `naturalRunningVisibleZeroBoundaryReal`
- lower-anchor and sampled-monotonicity lemmas
- indexed visible right-edge lemma
- `actualNaturalRunningMaximumBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega`

## Claim boundary

This is a canonical finite-height moving right-edge construction and closes the
three boundary-interface assumptions left by Stack 114.  It does not construct
positive or negative anti-cancellation witnesses for the resulting changing
finite zero package.  Therefore the signed conclusion remains conditional; no
unconditional Omega theorem or RH consequence is claimed.

Only `ZeroDensityLayerBudget*`, matching contract/audit files, and task
documents are in scope.  The protected complementary-bound and Sharp/VK-edge
modules remain untouched.

## Verification

Compile implementation, contract, and axiom audit directly and sequentially
with the existing overlay.  The audit may use only `propext`,
`Classical.choice`, and `Quot.sound`.
