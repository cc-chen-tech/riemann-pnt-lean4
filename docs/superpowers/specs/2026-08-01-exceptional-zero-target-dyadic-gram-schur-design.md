# Exceptional-zero target dyadic Gram/Schur design

## Scope

Establish the first complete E2 milestone on top of Draft PR #265: an
actual-zeta, target-normalized, right-higher, finite-`S`-relative upper bound
for one dyadic ordinate block.  The proof must apply Schur control to the
whole Gram matrix and must expose, rather than discard, a zero with real part
strictly larger than the target `beta`.

This stage does not:

- sum all dyadic blocks;
- invoke Carlson density;
- transfer an outer explicit formula to the low-height energy;
- add a Witness or Sharp hypothesis;
- claim a zero-free half-plane.

## Existing components

- `dynamicComplementGaussianMajorantEnergy_le` already gives whole-Gram
  Gaussian Schur control for actual zeta zeros, an arbitrary finite excluded
  set, target-normalized coefficients, and a finite set of unit buckets.
- `dynamicComplementPacketCoefficientMass` is the coefficient mass used by
  the quantitative Detect branch.
- `actualZetaDyadicZeroBlock_eq_biUnion_unitBuckets` identifies a dyadic
  ordinate block with its unit buckets.
- `actualZetaDyadicSquareReciprocalCapacity` and its multiplicity theorem
  supply the later `m^2 -> (log T)m` conversion.
- `rightHigherExclusionSet` and
  `directedWitness_of_not_mem_rightHigherExclusionSet` encode the required
  `S`-relative, right-higher complement.

## Considered approaches

### A. Specialize the existing dynamic whole-Gram theorem (selected)

Apply `dynamicComplementGaussianMajorantEnergy_le` to the dyadic bucket
interval, then bound each packet mass square by packet cardinality times the
sum of coefficient squares.  A maximum unit-bucket cardinality supplies the
local occupancy.

This keeps exactly the packet and coefficient objects shared with D1 and
avoids rebuilding Schur estimates.

### B. Apply the generic Gaussian bucket theorem to a dyadic union

This is mathematically equivalent, but would require reconstructing the
actual-zeta packet, target normalization, and `S`-deletion adapters already
present in the dynamic theorem.

### C. Reassemble pairwise near/far estimates

This would duplicate the proven whole-Gram row-sum argument and would make it
too easy to replace an operator bound by unsupported pairwise heuristics.

## Public objects

Define the dyadic unit-bucket index set

```lean
Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)
```

and the local occupancy as the maximum cardinality of
`dynamicComplementZeroPacket S T n` on that set.  Empty packets have
cardinality zero.  Public theorems use the requested robust factor
`1 + Occ`; the internal estimate may retain the sharper factor `Occ`.

Define the target-weighted square capacity over the same packets by summing

```text
(analyticOrderNatAt riemannZeta rho)^2 / ‖rho‖^2
  * exp (2 * (rho.re - beta) * a).
```

The coefficient identity is proved exactly from
`finiteZeroClusterCoefficientAt`; it is not introduced as a new assumption.

## Main theorem

For `1 <= m`, the dynamic complement energy of one dyadic block is at most

```text
gaussianBucketSchurConstant * (1 + Occ_k) * weightedSquareCapacity_k.
```

Specializing the excluded set to
`rightHigherExclusionSet S Told sigma T` yields the public actual-zeta,
target-normalized, right-higher, `S`-relative theorem.  Its constant contains
no occurrence of `S.card`.

## Real-part dichotomy

The weighted theorem is unconditional.  A separate public dichotomy states:

1. either a zero in the dyadic complement satisfies `beta < rho.re`; the
   result returns its actual-zeta membership, dyadic height location, and the
   directed witness facts obtained from non-membership in the right-higher
   exclusion set;
2. or every zero in the block satisfies `rho.re <= beta`.  If `0 <= a`, each
   exponential weight is at most one, so the target-weighted capacity is
   bounded by the unweighted dyadic square reciprocal capacity.

Thus no maximality or absence of farther-right zeros is hidden in the upper
bound.

## D1 alignment

Near-frequency occupancy is defined from the same
`dynamicComplementZeroPacket` used by D1.  The Gram bound consumes its packet
coefficient mass before Cauchy--Schwarz, so a later theorem can compare large
occupancy or large packet mass directly with D1's quantitative cluster
branch.  This PR does not duplicate D1 or add a new cluster-mass interface.

## Verification and claim boundary

- Start with exact-type contracts that fail before the implementation exists.
- Build the implementation, contract, and dedicated axiom audit.
- Scan for `sorry`, `admit`, prohibited declarations, and unexpected axioms.
- Test empty and singleton blocks, a farther-right zero branch, and the
  `rho.re <= beta` unweighted branch where expressible as theorem contracts.

Passing this stage proves one-block Gram/Schur control only.  Dyadic
aggregation, Carlson capacity, smoothing/two-height transfer, and Sharp's
uniform cofinal lower bound remain separate milestones.
