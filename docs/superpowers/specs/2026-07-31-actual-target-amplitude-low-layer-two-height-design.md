# Actual target-amplitude low-layer two-height design

## Scope

This stack closes the low-real-part counterpart of the two-height Carlson
strip estimate.  It does not modify the complementary-zero module, any
VK-edge module, or the oscillation-cluster implementation.

The object is the positive-ordinate, outside-cluster zero bucket whose real
parts are at most `tau`.  The bucket is formed at the outer height
`T = x ^ alpha` and is split at the intermediate height `x ^ gamma`.

## Why the old one-height estimate is insufficient

The existing global-zero-count majorant gives, up to logarithms,

```text
x ^ alpha * x ^ (tau - 1).
```

After division by the target-zero amplitude `x ^ (beta - 1)`, decay requires

```text
alpha + tau - beta < 0.
```

The explicit-formula contour requires `alpha > 1 - beta`.  Near the canonical
Carlson threshold these inequalities are incompatible.  Thus the old
single-height low layer cannot be used to close the target-normalized tail.

## Two-height split

Split the low-real-part bucket into:

```text
low ordinate:  0 < Im rho <= x ^ gamma
high annulus:  x ^ gamma < Im rho <= x ^ alpha.
```

The low-ordinate piece uses the global zero count at `x ^ gamma` and the
fixed denominator guard `kappa`.  Its target-normalized polynomial exponent
is

```text
gamma + tau - beta.
```

The high annulus uses the global zero count at `x ^ alpha`, while
`|rho| >= Im rho > x ^ gamma` supplies the missing denominator.  Its
target-normalized exponent is

```text
alpha + tau - beta - gamma.
```

Balancing at `gamma = alpha / 2` gives the common exponent

```text
alpha / 2 + tau - beta.
```

Therefore a contour-compatible `alpha > 1 - beta` exists precisely when

```text
tau < (3 * beta - 1) / 2.
```

There is a usable `tau > 1 / 2` exactly for `beta > 2 / 3`.

## Lean architecture

The implementation will add:

- filtered low-ordinate and high-annulus finsets;
- a disjoint-union identity recovering the original bucket layer;
- multiplicity-mass bounds by global zero multiplicity at the inner and
  outer heights;
- pointwise kernel aggregation bounds for both pieces;
- endpoint-shift identities reducing both asymptotic limits to the existing
  actual hybrid low-layer decay theorem;
- a balanced existence theorem with `alpha > 1 - beta`.

The high-annulus endpoint shift is

```text
x ^ (tau - 1) / x ^ gamma = x ^ ((tau - gamma) - 1),
```

so the existing one-height asymptotic theorem can be reused with endpoint
`tau - gamma`, outer exponent `alpha`, and denominator constant `1`.

## Claim boundary

This stack proves decay of an actual finite low-real-part bucket after
division by the target amplitude.  It does not yet prove decay of the full
complementary zero tail, an unconditional Omega theorem, zero replication,
or the Riemann hypothesis.
