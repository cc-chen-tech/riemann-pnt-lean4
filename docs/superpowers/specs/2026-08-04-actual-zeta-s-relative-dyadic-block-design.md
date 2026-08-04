# Actual-zeta S-relative dyadic block Gram design

## Objective

Build one main-based, actual-zeta theorem for a single positive-ordinate
dyadic block.  For an arbitrary finite exclusion set `S`, a lower real-part
threshold `sigma`, and a target real part `beta`, the theorem must return one
of exactly two outcomes:

1. a surviving genuine zeta zero in the block with real part strictly larger
   than `beta`; or
2. a whole-Gram Gaussian upper bound for the surviving block, normalized at
   `beta`, by the actual S-relative reciprocal-square multiplicity capacity.

This is the missing main-based single-block component of E2.  It is not a
finite-range or infinite-tail theorem.

## Fixed scope

The slice owns only:

- actual zeta-zero membership in one dyadic block;
- deletion of an arbitrary finite set `S`;
- the strict farther-right alternative `beta < rho.re`;
- target-normalized forward drift on the complementary branch;
- a whole Gram-matrix Schur estimate;
- an exact square-reciprocal-capacity bound; and
- a single-block Carlson-count corollary using the multiplicity and occupancy
  estimates already present on `main`.

The slice does not add finite-range aggregation, a summable high tail,
smoothing, a two-height transfer, a D1 cluster-mass interface, a Witness or
Sharp lower bound, set growth, or a zero-free conclusion.  It does not change
an existing occupancy definition, a global constant, or a mathematical
assumption.

## Main-based dependencies

The production module will import only modules already on `main`, principally:

- `MathlibAux.DyadicDriftingGaussianSchur` for the whole-Gram Schur theorem;
- `PrimeNumberTheorem.HalfIsolatedZetaDyadicAdapter` for genuine bucket-labelled
  zeta zeros and the injective projection from labels to zeros;
- `PrimeNumberTheorem.VKEdgeHighZeroGaussianEnergy` for
  `zeroReciprocalMultiplicityCoefficient` and the local unit-bucket
  multiplicity estimate; and
- `PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity`
  for the actual Carlson strip, S-relative square capacity, the logarithmic
  multiplicity upgrade, and the Carlson-count bound.

No theorem or definition will be imported from the old exceptional-zero stack
behind PRs #268, #289, #294, or #304.

## Production module

The proposed module is:

`PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetDyadicBlockGram.lean`.

It remains in namespace `PrimeNumberTheorem.VKEdgePiOverTwo`, matching the
existing actual-zeta Gaussian adapter.

## Finite actual sets

### Surviving source pairs

Define a bucket-labelled finite set by filtering `zetaDyadicBucketPairs k` to
zeros which lie in

`actualCarlsonDyadicZeroShell sigma k \ S`.

Call this set `actualSRelativeDyadicBucketPairs S sigma k`.  Membership must
expose all of the following facts:

- the bucket label lies in `[2^k, 2^(k+1))`;
- the second projection is a genuine nontrivial zeta zero;
- its imaginary part is positive and lies in the same dyadic block;
- `sigma < rho.re`; and
- `rho` is not in `S`.

The second projection remains injective because the set is a subset of
`zetaDyadicBucketPairs k`.

### Target-side pairs

Define

`actualTargetDyadicBucketPairsExcluding S sigma beta k`

by further filtering the surviving source pairs by `rho.re <= beta`.
Its second projections are contained in

`actualCarlsonDyadicZeroStrip sigma beta k \ S`.

This is a subset theorem, not an equality theorem: `zetaDyadicBucketPairs k`
uses the absolute-ordinate interval `[2^k, 2^(k+1))`, while the actual Carlson
shell uses `(2^k, 2^(k+1)]`.  Filtering the former by the latter can therefore
omit a zero exactly at the Carlson shell's upper endpoint.  The subset is all
that the capacity proof needs: injectively reindex the pair sum over its second
projections, then enlarge that nonnegative sum to the full S-relative actual
strip.  Equality at `rho.re = beta` belongs to the target-side filter; only
strict inequality `beta < rho.re` belongs to the farther-right branch.

## Target-normalized Gram energy

For a labelled zero `p`, define the base mass at forward-window origin `a` by

`zeroReciprocalMultiplicityCoefficient p.2 *
  Real.exp ((p.2.re - beta) * a)`.

Define forward drift by `p.2.re - beta`, frequency by `p.2.im`, and bucket by
`p.1`.  The resulting full energy is an instance of
`MathlibAux.dyadicDriftingGaussianGram` on the entire surviving source set.
It therefore contains every within-block Gram entry, including all
cross-bucket interactions.

On the no-farther-right branch, every drift is nonpositive.  For `0 <= a` and
`0 <= t`, the individual moved mass is at most

`analyticOrderNatAt riemannZeta rho / ||rho||`.

Consequently its squared sum is bounded by

`actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
  sigma beta k S`.

The proof must use the existing whole-matrix Schur theorem.  It must not bound
cross terms one pair at a time.

## Actual occupancy

Define a new actual, S-relative block occupancy from the maximum cardinality
of the unit-bucket fibres of
`actualTargetDyadicBucketPairsExcluding S sigma beta k`.

This definition is local to the new actual adapter.  It does not alter or
reinterpret any occupancy object in another branch or module.  Its basic
contract is:

`card fibre <= actualTargetDyadicOccupancy S sigma beta k`.

The Schur theorem may deliberately use the harmless factor
`1 + actualTargetDyadicOccupancy S sigma beta k`, matching the agreed public
shape even when the exact maximum alone would suffice.

Deleting `S` cannot increase occupancy.  The existing
`exists_zeroOrdinateUnitBucketMultiplicity_le_log` theorem supplies a uniform
logarithmic upper bound because cardinality is at most analytic multiplicity.
No constant introduced here may depend on `S` or `S.card`.

## Public theorems

### Exact capacity dichotomy

The primary theorem has the following semantic form for `0 <= a`, `0 <= t`,
and `1 <= m`:

```text
(exists rho,
    rho is in actualCarlsonDyadicZeroShell sigma k \ S
    and beta < rho.re)
or
actual S-relative target-normalized dyadic Gram energy
  <= gaussianBucketSchurConstant
       * (1 + actualTargetDyadicOccupancy S sigma beta k)
       * actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
           sigma beta k S.
```

The witness branch also exposes genuine-zero membership, the positive dyadic
height bounds, and `rho notin S` through a companion specification theorem or
the exact conjunction in the theorem result.

The proof splits on the existence of a surviving source zero with
`beta < rho.re`.  In the negative branch, the source pair set equals the
target pair set, all forward drifts are nonpositive, and the capacity theorem
applies.  There is no hidden assumption that farther-right zeros do not exist.

### Single-block Carlson corollary

A second theorem combines the exact dichotomy with:

- the uniform logarithmic occupancy bound; and
- `exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count`.

For sufficiently high blocks, it returns the same farther-right witness or a
bound by a uniform constant times the appropriate logarithmic factors and

`actualCarlsonDyadicCount sigma (k + 1) / ((2 : Real) ^ k)^2`.

This theorem stops at one block.  It does not sum over `k`.  All existential
constants are chosen before `S`; hence they are uniform in `S` and `S.card`.

## Contracts and axiom audit

Add:

- `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean`; and
- `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramAxiomAudit.lean`.

The contract uses exact typed `example` statements rather than bare `#check`
for every public definition and theorem.  It covers:

- empty `S`;
- deleting the complete actual block;
- preservation of the boundary case `rho.re = beta` in the energy branch;
- strictness of the farther-right branch;
- the existing bucket interval `[2^k, 2^(k+1))` and the actual shell interval
  `(2^k, 2^(k+1)]`, including the projection-subset boundary behavior;
- retention of analytic multiplicity squared and `1 / ||rho||^2`; and
- the fact that the final constant is quantified before `S`.

The axiom audit prints every public theorem in the production module.  The
allowlist must contain exactly those public declarations and no accidental
new axiom.

## Repository wiring

The eventual implementation PR may modify only:

- the new production module;
- its Contract and AxiomAudit modules;
- `RiemannPNT.lean`;
- `lakefile.lean`;
- `scripts/check_axiom_allowlist.py`; and
- this spec plus the later implementation plan.

No old stacked module is copied, renamed, or edited.

## Verification

After an explicit Lean resource window is granted, verification is serial:

1. production module;
2. Contract;
3. AxiomAudit;
4. allowlist and forbidden-declaration scans; and
5. full baseline only in the controlled integration window.

Results from any base before the then-current `origin/main` are historical
only and cannot serve as merge evidence.

## Acceptance boundary

The slice is complete only when the actual source set, strict farther-right
alternative, forward-drift whole-Gram bound, S-relative square capacity, and
single-block Carlson-count corollary all compile together on current `main`.

It does not establish finite dyadic aggregation, a uniform summable high tail,
the two-height transfer, a repeatable Sharp lower bound, exclusion of any
fixed half-plane, or RH.
