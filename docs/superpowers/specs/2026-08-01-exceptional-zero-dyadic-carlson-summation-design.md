# Exceptional-zero dyadic Carlson summation design

## Scope

Complete the centered-frozen E2 upper-bound layer on top of Draft PR #268.
The result must connect the packet capacity to the existing actual-zeta
dyadic block, reuse the proved multiplicity-square reduction, apply Carlson's
fixed-strip zero-density estimate, and control an arbitrary finite high
dyadic range by a summable majorant whose constants are independent of the
finite excluded set `S` and of the outer truncation height `T`.

This stage does not:

- transfer a moving or smoothed explicit-formula energy to the centered
  frozen energy;
- introduce a two-height parameter interface;
- introduce a Sharp or Witness lower-bound hypothesis;
- claim a Carlson contradiction or a zero-free half-plane.

## Selected architecture

### 1. Exact packet-to-block reindexing

For a dyadic block `k`, assume

```text
(2 : ℝ) ^ (k + 1) ≤ T.
```

Then every unit bucket in `dyadicUnitBucketIndexSet k` is already contained
in `nontrivialZerosFinset T`.  The dynamic packet is therefore exactly the
unit bucket with `S` deleted.  Since distinct absolute-ordinate unit buckets
are disjoint and PR #265 proves their union is `actualZetaDyadicZeroBlock k`,
prove

```text
dynamicComplementDyadicSquareReciprocalCapacity S T k
  = actualZetaDyadicSquareReciprocalCapacityExcluding k S
```

and the analogous linear-capacity identity.  No new zero or mass object is
introduced.

### 2. Local occupancy and multiplicity-square losses

For every dynamic packet, distinct-cardinality is bounded by its total
analytic multiplicity.  Reuse
`exists_zeroOrdinateUnitBucketMultiplicity_le_log` to obtain, uniformly for
`k ≥ 2`,

```text
dynamicComplementDyadicOccupancy S T k
  ≤ Cocc * (1 + log ((2 : ℝ) ^ (k + 1) + 7)).
```

This remains the same local packet occupancy used by D1; it is not replaced
by a global zero count.

For the square reciprocal capacity, reuse
`exists_actualZetaDyadicSquareReciprocalCapacityExcluding_le_log_linear`.
When the excluded set is

```text
rightHigherExclusionSet S Told sigma T
```

the assumptions `4 ≤ Told` and `(2 : ℝ)^(k+1) ≤ T` place every zero of
absolute ordinate below `4` into the exclusion set.  Hence

```text
square capacity ≤ Cmult * log(2^(k+1)) * linear capacity.
```

Neither constant depends on `S`.

### 3. S-relative linear Carlson capacity

A zero surviving the right-higher exclusion set is an actual positive-
ordinate zero with real part strictly larger than `sigma`.  In block `k`,

```text
‖rho‖⁻² ≤ ((2 : ℝ) ^ k)⁻².
```

Therefore prove

```text
actualZetaDyadicLinearReciprocalCapacityExcluding k
    (rightHigherExclusionSet S Told sigma T)
  ≤ ((2 : ℝ) ^ k)⁻² *
      (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ (k + 1)) : ℝ).
```

The count is taken at the block endpoint, not at the outer height `T`.  This
is essential for a summable dyadic bound and makes the constant independent
of `T` and `|S|`.

### 4. Whole-Gram finite dyadic aggregation

Do not bound the energy of a union by summing isolated block energies: that
would omit cross-block Gram entries.  Define the finite bucket range

```text
dyadicUnitBucketRange K L =
  Finset.Icc (2 ^ K) (2 ^ L - 1)
```

for `K < L`.  Apply `dynamicComplementGaussianMajorantEnergy_le` once to
this entire range.  Reindex only its diagonal packet-mass-square sum into
dyadic blocks.  Within each block apply finite Cauchy--Schwarz with that
block's own `dynamicComplementDyadicOccupancy`.

This yields a bound for the actual centered frozen Gaussian energy over the
whole range, including all cross-block interactions:

```text
E_[K,L),S ≤ gaussianBucketSchurConstant *
  ∑ k ∈ Finset.Ico K L,
    (1 + Occ k) * squareCapacity k.
```

The right-higher specialization preserves the farther-right alternative.  It
either returns a surviving packet zero with `beta < rho.re`, together with
its Carlson-strip, positive-height, and non-exclusion facts, or consumes the
occupancy, square-to-linear, and linear-to-Carlson bounds above to control the
whole-range energy.

### 5. Carlson majorant and uniform high tail

For fixed `sigma` with `1/2 < sigma < 1`, set

```text
q = 4 * sigma * (1 - sigma).
```

Prove `q < 1`, then specialize
`CarlsonZeroDensity.carlson_zeroDensity_isBigO` along
`k ↦ (2 : ℝ)^(k+1)`.  After the two logarithmic losses from occupancy and
multiplicity-square reduction, obtain constants `A ≥ 0` and `K0 ≥ 2` such
that for `K0 ≤ k`,

```text
(1 + Occ k) * squareCapacity k
  ≤ A * ((k + 1 : ℝ) ^ 6) *
      (((2 : ℝ) ^ (q - 2)) ^ k).
```

Because `0 < (2 : ℝ)^(q-2) < 1`, the polynomial-geometric sequence on the
right is summable.  The public endpoint must include both:

1. an unconditional finite-range whole-Gram bound in terms of the weighted
   block capacities, retaining all cross-block interactions;
2. for every `eta > 0`, a cutoff `Keta` such that every range with
   `Keta ≤ K < L`, `(2 : ℝ)^L ≤ T`, and `4 ≤ Told` satisfies the exact
   dichotomy: either there are `n` and `rho` with `n` in the dyadic range,
   `rho` surviving the right-higher exclusion packet, `beta < rho.re`,
   `rho` in the Carlson zero-density finset, `Told < rho.im`, and `rho ∉ S`;
   or the whole-range centered-frozen energy is less than `eta`.

The high-tail endpoint is this disjunction, not an unconditional energy
inequality and not a zero-exclusion statement.  It introduces no additional
no-farther-right hypothesis.

The constants may depend on the fixed strip parameter `sigma` and the
Gaussian Schur constant, but not on `S`, `T`, `Told`, `K`, or `L`.

## Alternatives rejected

### Sum isolated block energies

This loses cross-block Gram terms and therefore does not control the energy
of the union.  It is not a complete direct-`L²` estimate.

### Stay in packet form

This avoids reindexing but cannot directly reuse the actual-block
`m² -> (log T)m` theorem and leaves the Carlson connection informal.

### Rebuild Schur on the actual block

Applying the generic Schur theorem from scratch would duplicate the packet,
frequency-gap, and target-normalization adapters already proved.  Applying
the existing dynamic whole-Gram theorem once to the complete bucket range is
both narrower and stronger.

## Files and ownership

- `PrimeNumberTheorem/ExceptionalZeroDyadicCapacityReindex.lean` owns exact
  packet/block identities, local occupancy, low-zero absorption, and the
  blockwise linear Carlson-capacity inequality.
- `PrimeNumberTheorem/ExceptionalZeroDyadicCarlsonSummation.lean` owns the
  whole-range bucket set, global Schur aggregation, Carlson majorant, and
  uniform high-tail theorem.
- Matching files under `Test/` lock exact public types and audit axioms.
- Existing E0, E1, D1, #265, and #268 modules are consumed without changing
  their mathematical statements.

## Verification

For each module, run in order with one Lean process in this worktree:

1. implementation target;
2. exact-type contract;
3. axiom audit;
4. forbidden-declaration and accidental-axiom scans.

Contracts must cover:

- packet/block equality at the exact height endpoint;
- the failure of that equality to be claimed without its height hypothesis;
- low zeros absorbed by `rightHigherExclusionSet` when `4 ≤ Told`;
- constants independent of `S.card`;
- a two-block range, ensuring aggregation uses a single whole-Gram energy;
- finite-range domination by the summable majorant;
- uniform high-tail smallness.

## Claim boundary

Passing these contracts completes only the centered-frozen direct-`L²`
capacity upper bound.  It supplies the upper-tail object required by a later
smoothing/two-height transfer, but it does not prove that Sharp's energy is
the same object, does not provide a uniform cofinal lower bound, and excludes
no zero.
