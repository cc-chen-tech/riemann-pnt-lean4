# Sharp energy to one strict zeta-zero update

## Closed composition

This stacked integration module proves the exact one-window chain

```text
positive full complementary moving Gaussian energy
  -> rho ∈ nontrivialZerosFinset T with rho ∉ S
  -> S' = insert rho S
  -> S ⊆ S'
  -> S.card < S'.card
  -> S' ⊆ nontrivialZerosFinset T
```

It also exposes the stronger directly usable input:

```text
selected-cluster remainder energy
  > 3 * (approximation budget + closed-term budget)
  -> one strict recorded-zero-set update
```

The analytic witness extraction is imported unchanged from
`VKEdgeDistinctComplementWitness`.  The finite-set update is imported
unchanged from `ExceptionalZeroDetectOrCount`.

## Why half-isolated classification is not used here

The adjacent Sharp theorem already returns a concrete genuine zero outside
the entire recorded set `S`.  That output is stronger than the disjunction
needed by the generic detect-or-count adapter, so no additional local
half-isolated classification is required for this one step.

## Exact remaining blocker

The theorem assumes the surplus inequality for the current `S`.  It does not
prove the same inequality after replacing `S` by the larger `S'`.

Therefore this closes exactly one strict growth step.  It does not prove
iteration, a quantitative growth rate, a Carlson contradiction, zero
exclusion, or the Riemann hypothesis.
