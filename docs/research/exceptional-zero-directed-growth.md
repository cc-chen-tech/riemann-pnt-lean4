# Directed exceptional-zero growth

## Verified adapter

For a recorded finite set `S`, an old height `Told`, a right-strip threshold
`sigma`, and a truncation height `T`, define the enlarged exclusion set by
adding every truncated zero satisfying either

```text
Im rho <= Told
```

or

```text
Re rho <= sigma.
```

If the full complementary energy, or the explicit remainder surplus that
implies it, is positive after this enlarged exclusion, then Lean extracts a
zero satisfying all of

```text
rho notin S
Told < Im rho <= T
sigma < Re rho
rho is a nontrivial zeta zero.
```

If `S` is already contained in the corresponding Carlson counting finset, the
adapter also constructs `S' = insert rho S` and proves

```text
S subset S'
card S < card S'
S' subset zeroDensityZerosFinset sigma T.
```

## Remaining analytic input

This adapter does not prove that the required complementary energy remains
positive after low and non-right zeros are excluded. In particular, it does
not derive the directed surplus from the currently available empty-set Sharp
lower bound.

The next upstream theorem must prove a positive lower bound for the remainder
relative to `rightHigherExclusionSet S Told sigma T`, uniformly enough to
repeat after replacing `S` by the larger recorded set.

## Scope

The result closes the finite-set and localization implication

```text
directed residual surplus
  -> a new higher right-strip zero
  -> strict growth inside the Carlson counting finset.
```

It does not prove persistence, a multi-window lower bound, a Carlson
contradiction, or the Riemann hypothesis.
