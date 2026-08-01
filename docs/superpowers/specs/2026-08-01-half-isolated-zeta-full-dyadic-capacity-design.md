# Full dyadic zeta mass to Carlson capacity design

## Scope

Extend the positive-ordinate bridge from PR #271 in two strictly ordered steps:

1. transfer the negative-ordinate excluded mass through complex conjugation;
2. split the complete dyadic excluded mass into positive and negative parts and combine both bounds.

This milestone does not add an Occupancy estimate, a Sharp lower bound, a multi-window iteration, a Carlson contradiction, or an RH conclusion.

## Exclusion-set convention

Define

```lean
conjugateFinset (S : Finset ℂ) := S.image conj
```

No conjugation-invariance assumption is permitted.  The transfer must prove the exact equivalence

```lean
rho ∉ S ↔ conj rho ∉ conjugateFinset S
```

using involutivity and injectivity of complex conjugation.

## Negative-ordinate transfer

Define the negative subset of the existing actual right dyadic bucket pairs by filtering on

```lean
p.2.im < 0 ∧ p.2 ∉ S
```

Map a pair `(n, rho)` to `(n, conj rho)`.  The proof must retain:

- the bucket label `n`, because `|Im (conj rho)| = |Im rho|`;
- the right-strip condition, because `Re (conj rho) = Re rho`;
- the reciprocal norm, because `‖conj rho‖ = ‖rho‖`;
- analytic multiplicity, using the existing zeta conjugation theorem;
- deletion of `S`, transformed exactly into deletion of `conjugateFinset S`.

The resulting theorem should have the form

```lean
zetaRightDyadicNegativeMassSquareExcluding x beta k S ≤
  (x ^ (1 - beta)) ^ 2 *
    (actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
        sigma 1 (k - 1) (conjugateFinset S) +
     actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
        sigma 1 k (conjugateFinset S))
```

under the same numerical assumptions as the positive theorem: `1 ≤ x`, `1 ≤ k`, and `sigma < beta`.

## Complete-mass split

Define the full excluded mass by filtering the existing right dyadic bucket pairs only by `p.2 ∉ S`.

For every member, the existing dyadic specification gives

```lean
(2 : ℝ) ^ k ≤ |p.2.im|
```

and `(2 : ℝ) ^ k > 0`.  Therefore `p.2.im ≠ 0`, so each term lies in exactly one of the positive or negative filters.  Use this fact to prove an exact finite-sum decomposition, not merely an inequality.

Combining the positive theorem from PR #271 and the new negative theorem gives

```lean
zetaRightDyadicFullMassSquareExcluding x beta k S ≤
  (x ^ (1 - beta)) ^ 2 *
    (cap (k - 1) S + cap k S +
     cap (k - 1) (conjugateFinset S) +
     cap k (conjugateFinset S))
```

with the actual PR #258 capacity object substituted for `cap`.

## Files and verification

Add only:

- `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge.lean`
- `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/Contract.lean`
- `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/AxiomAudit.lean`

Verification order:

1. focused source build;
2. focused contract build;
3. focused axiom-audit build;
4. `#print axioms`, allowing only standard logical axioms;
5. static `sorry`, `admit`, and added `axiom` scan;
6. clean stacked Draft PR over PR #271.

## Claim boundary

The completed theorem is an upper-bound adapter.  It does not supply positive residual energy, Occupancy, local multiplicity bounds, two-height tail transfer, multi-window growth, or a contradiction with Carlson.
