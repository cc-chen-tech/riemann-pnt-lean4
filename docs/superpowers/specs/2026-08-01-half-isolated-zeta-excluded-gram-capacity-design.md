# Excluded dyadic zeta Gram to Carlson capacity design

## Goal

Extend the full positive-and-negative dyadic mass bridge from PR #274 to the
actual drifting Gaussian Gram energy after deleting an arbitrary finite zero
set `S`.  The milestone provides both a conditional occupancy estimate and a
detect-or-count alternative on the same excluded zeta block.

This is an upper-bound integration milestone.  It does not provide the Sharp
repeatable residual-energy lower bound, a two-height tail transfer, a
multi-window accumulation theorem, a Carlson contradiction, or an RH result.

## Why a new excluded Gram is necessary

The existing theorem
`zetaRightDyadicGaussianGram_le_occupancy_mul_sum_sq` acts on the complete
`zetaRightDyadicBucketPairs beta k`, whereas PR #274's mass acts on
`zetaRightDyadicPairsExcluding beta k S`.

The Gaussian Gram contains oscillatory cross terms.  Removing indices is not a
monotone operation for the whole quadratic form, so the excluded energy cannot
be bounded by comparing it directly with the unexcluded Gram.  The abstract
Schur theorem must instead be instantiated on the excluded finite set itself.

## Actual excluded objects

Define the excluded drifting Gram by using the existing concrete zeta data:

```lean
noncomputable def zetaRightDyadicGaussianGramExcluding
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) (t m : ℝ) : ℝ :=
  MathlibAux.dyadicDriftingGaussianGram
    (zetaRightDyadicPairsExcluding beta k S)
    (zetaDyadicBaseMass x beta)
    (zetaDyadicBackwardDrift beta)
    (fun p => p.2.im) t m
```

Define one excluded unit-ordinate cluster by filtering on the retained bucket
label and then projecting to genuine zeta zeros:

```lean
noncomputable def zetaRightDyadicUnitClusterExcluding
    (beta : ℝ) (k : ℕ) (S : Finset ℂ) (n : ℕ) : Finset ℂ :=
  ((zetaRightDyadicPairsExcluding beta k S).filter fun p => p.1 = n).image
    Prod.snd
```

The existing injectivity of `Prod.snd` on `zetaDyadicBucketPairs k` restricts
to the excluded subset.  Therefore the cluster cardinality counts distinct
zeros rather than duplicated bucket labels.

## Occupancy theorem

Instantiate
`MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq` directly on
`zetaRightDyadicPairsExcluding beta k S`.

The public theorem has the form:

```lean
theorem zetaRightDyadicGaussianGramExcluding_le_occupancy_mul_fullMass
    {x beta t m : ℝ} (k occupancy : ℕ) (S : Finset ℂ)
    (hx : 0 < x) (ht : 0 ≤ t) (hm : 1 ≤ m)
    (hoccupancy : ∀ n ∈
      (zetaRightDyadicPairsExcluding beta k S).image Prod.fst,
      ((zetaRightDyadicPairsExcluding beta k S).filter
        fun p => p.1 = n).card ≤ occupancy + 1) :
    zetaRightDyadicGaussianGramExcluding x beta k S t m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ((occupancy + 1 : ℕ) : ℝ) *
          zetaRightDyadicFullMassSquareExcluding x beta k S
```

No new analytic assumption is introduced.  Nonnegative mass, nonpositive
drift, and the bucket-frequency gap are inherited from the actual-zeta adapter
by restricting its membership hypotheses to the excluded subset.

## Four-capacity theorem

Compose the occupancy theorem with PR #274's
`zetaRightDyadicFullMassSquareExcluding_le_fourCarlsonCapacities`.

The result retains exactly:

- `MathlibAux.gaussianBucketSchurConstant`;
- the factor `occupancy + 1`;
- the normalization `(x ^ (1 - beta)) ^ 2`;
- the `k - 1` and `k` Carlson capacities excluding `S`;
- the `k - 1` and `k` Carlson capacities excluding `conjugateFinset S`.

Its numerical assumptions are the union of the two existing interfaces:
`1 ≤ x`, `0 ≤ t`, `1 ≤ m`, `1 ≤ k`, and `sigma < beta`.  The proof may derive
`0 < x` from `1 ≤ x`; it must not alter the four capacity terms or assume that
`S` is conjugation-invariant.

## Detect-or-count theorem

Instantiate
`MathlibAux.dyadicDriftingGaussianGram_le_or_quantitativeCluster` on the same
excluded finite set.  Export the concrete alternative:

```lean
zetaRightDyadicGaussianGramExcluding x beta k S t m ≤
    MathlibAux.gaussianBucketSchurConstant *
      ((occupancy + 1 : ℕ) : ℝ) *
        zetaRightDyadicFullMassSquareExcluding x beta k S
  ∨
∃ n ∈ (zetaRightDyadicPairsExcluding beta k S).image Prod.fst,
  occupancy + 1 <
    (zetaRightDyadicUnitClusterExcluding beta k S n).card
```

Also export one thin composition in which the first branch is replaced by the
four-Carlson-capacity upper bound.  The second branch remains a quantitative
cluster of distinct genuine zeta zeros outside `S`.

This dichotomy does not prove that either branch contradicts known estimates.
In particular, no unconditional occupancy bound or local analytic
multiplicity bound is asserted.

## Files and branch isolation

Add only:

- `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge.lean`;
- `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/Contract.lean`;
- `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/AxiomAudit.lean`.

Work on branch
`codex/half-isolated-zeta-excluded-gram-capacity-bridge`, stacked on PR #274.
Do not modify PR #274, Sharp, Pintz-Carlson, or their worktrees.

## Verification

Run only focused targets, with at most four Lean threads and no concurrent
builds that write the same target:

1. source build;
2. contract build;
3. axiom-audit build;
4. `#print axioms`, allowing only standard logical axioms;
5. scoped `sorry`, `admit`, and added `axiom` scan;
6. `git diff --check` and clean worktree status;
7. one small stacked Draft PR over PR #274.

## Claim boundary

The completed milestone states only an excluded actual-zeta Gram/Schur upper
bound, its four-capacity composition, and a quantitative excluded
cluster alternative.  It does not supply repeatable positive energy, choose a
new witness, prove strict Finset growth, perform multi-window counting, exceed
Carlson capacity, exclude off-critical-line zeros, or prove RH.
