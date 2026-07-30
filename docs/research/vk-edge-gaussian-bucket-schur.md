# Gaussian bucket Schur bound

## Proved in this branch

For a finite frequency package, put each frequency into a natural unit
bucket. Assume only that two terms in buckets `n` and `k` have frequency gap
at least

```text
Nat.dist n k - 1.
```

No separation is required inside one bucket. The branch proves that, for
Gaussian scale `m >= 1`,

```text
sum_i sum_j mass_i mass_j exp(-m (freq_i - freq_j)^2)
  <= C_Schur * sum_n bucketMass(n)^2,
```

where

```text
C_Schur = 2 * (1 + (1 - exp(-1))^(-1)) > 0.
```

The proof first dominates the Gaussian by a summable kernel depending only on
the distance between buckets. Each distance fiber contains at most two
natural-number buckets, so every kernel row has a uniform finite bound. A
finite Schur argument then reduces all cross terms to squared bucket masses.

This is collision-safe: repeated frequencies, repeated zeros, and arbitrarily
close frequencies remain in the same bucket and are charged through their
combined mass.

## Zeta specialization

The branch also applies the abstract Schur estimate to the actual
multiplicity-weighted zeta-zero coefficients

```text
analyticOrderNatAt riemannZeta rho / ‖rho‖.
```

For unit absolute-ordinate buckets `H <= n <= N`, define the complete
Gaussian interaction energy by summing over every ordered pair of zeros in
every ordered pair of buckets. The proved endpoint is

```text
zeroOrdinateBucketGaussianEnergy H N m
  <= C_Schur
       * sum_{n=H}^N zeroOrdinateUnitBucketCoefficientMass(n)^2
```

for every `m >= 1`. Combining this with the previously proved square
summability gives the uniform tail statement

```text
for every eta > 0,
for all sufficiently large H,
for every N >= H and every m >= 1,
zeroOrdinateBucketGaussianEnergy H N m < eta.
```

Thus the full high-zero Gaussian cross energy, not only its diagonal part,
vanishes uniformly. The proof uses the reverse triangle inequality between
the signed ordinates and their absolute values; it does not assume distinct
zeros, simple zeros, or zero spacing.

## Role in the dynamic-packet route

Together with the normalized explicit-formula remainder, this is now the
data layer for controlling the high-frequency part of a moving zeta zero
packet. It is not another finite-height approximation theorem.

The next mathematical endpoint is to identify the Gaussian quadratic form
above with the weighted local `L2` norm of the high-zero contribution in the
normalized explicit formula, including the moving cutoff and the real-part
drift. After that, the dynamic packet split is:

```text
large complementary L2 energy
  -> extract a nonempty frequency packet
  -> merge it into the current dominant packet
  -> preserve analytic multiplicity and an overlap certificate.
```

The opposite branch, where complementary energy is small, may use the
existing cluster budget and explicit-formula remainder to force oscillation.
The local-`L2` identification and neither branch are completed here. This
module does not prove an unconditional oscillation theorem, a Carlson
contradiction, or RH.
