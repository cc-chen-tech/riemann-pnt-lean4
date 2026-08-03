# Cluster lower bounds versus zero-density upper bounds

## Scope

This note specifies an abstract comparison layer only.  Its owned Lean prefix
is `PrimeNumberTheorem/ZeroDensityClusterComparison*.lean`.

It does not modify or duplicate:

- `ZeroForcedOscillationComplementaryBound.lean`;
- any contract or audit owned by that module;
- any Vinogradov--Korobov edge module.

The interface may later accept a Carlson or Guth--Maynard zero-density theorem,
but this step does not claim that a Guth--Maynard estimate has been formalized.
No statement below implies RH.

## Quantities

For a finite zero cluster `C`, define

```text
localClusterLowerBound(C, sigma, T, H)
```

to be the number of members of `C` with real part at least `sigma` and
ordinate in `[T, T + H]`.

For an ambient zero-counting function, write

```text
N(sigma, T)
```

for the number of zeros with real part at least `sigma` and ordinate at most
`T`.  An abstract zero-density interface supplies an eventual upper majorant

```text
N(sigma, T) <= U(sigma, T).
```

The local cluster lower bound can only challenge this estimate after an
analytic argument proves

```text
L(sigma, T, H) <= N(sigma, T + H)
```

for an unbounded family of scales `T`.

## Auditable theorem chain

1. `localClusterLowerBound_le_card`
   A fixed finite cluster contributes at most its cardinality.

2. `finite_localClusterLowerBound_eventually_le_diverging_upper`
   If an upper majorant tends to infinity, every fixed finite cluster lower
   bound is eventually below that majorant.

3. `eventually_upper_lt_lower_of_gap_tendsto_atTop`
   If `L(T) - U(T) -> +infinity`, then eventually `U(T) < L(T)`.

4. `false_of_eventually_lower_count_upper_separated`
   Eventual inequalities `L <= N`, `N <= U`, and `U < L` are inconsistent.

5. `cluster_density_contradiction_of_gap_tendsto_atTop`
   Combining the preceding two statements yields the abstract contradiction
   criterion.

## Why one zero or a finite cluster is insufficient

If `C` is fixed and finite, then

```text
localClusterLowerBound(C, sigma, T, H) <= card(C)
```

uniformly in `T` and `H`.  A Carlson-type or Guth--Maynard-type density upper
bound usually grows with `T`; in particular, if `U(T) -> +infinity`, then

```text
localClusterLowerBound(C, sigma, T, H) <= U(T)
```

eventually.  Thus a single zero, or any fixed finite rightmost cluster, is
compatible with such an upper bound.  Anti-cancellation can force oscillation
of an explicit formula without forcing many distinct zeros.

A contradiction requires an unbounded family of distinct local clusters, or
another mechanism producing a lower count whose growth eventually exceeds the
density majorant.  Merely revisiting the same finite cluster at many `x`-scales
does not increase `N(sigma, T)`.

## Required growth separation

The minimal logical condition is eventual strict separation:

```text
U(sigma, T + H) < L(sigma, T, H).
```

A convenient sufficient condition formalized here is

```text
L(sigma, T, H) - U(sigma, T + H) -> +infinity.
```

For concrete power or exponential estimates this must be discharged by
comparing exponents and, in equal-exponent cases, leading constants.  Big-O
notation alone does not create a contradiction unless it yields the strict
eventual inequality.

## Remaining analytic bridge

Future work must supply, for a genuinely growing family of distinct zeros:

- a certified map from cluster members to zeros counted by `N`;
- control of overlap between windows;
- a quantitative lower growth law for `L(sigma, T, H)`;
- a concrete Carlson or Guth--Maynard majorant `U`;
- strict asymptotic separation of `L` and `U`.

Until these are present, the comparison layer is a transfer criterion, not a
new zero-density contradiction.
