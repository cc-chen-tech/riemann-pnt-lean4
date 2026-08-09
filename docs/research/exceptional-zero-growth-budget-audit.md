# Exceptional-zero growth budget audit

## Audited chain

The current stacked chain now proves one strict update:

```text
positive S-relative complementary energy
  -> rho ∈ nontrivialZerosFinset T with rho ∉ S
  -> S' = insert rho S
  -> S.card < S'.card
```

The relevant endpoints are:

- `exists_nontrivialZero_not_mem_of_fullMovingGaussianSecondMoment_pos`;
- `exists_nontrivialZero_not_mem_of_remainder_energy_gt_three_errors`;
- `exists_strictly_larger_recordedZeroSet_of_fullMovingGaussianSecondMoment_pos`;
- `exists_strictly_larger_recordedZeroSet_of_remainder_energy_gt_three_errors`.

This is a genuine one-step result on actual zeta-zero finsets.  It is not yet
an asymptotic lower bound.

## Blocker 1: no persistence after the update

The unconditional Sharp lower bound
`exists_eventually_emptyClusterFullMovingGaussianSecondMoment_gt` is stated
for `S = ∅`.

The arbitrary-`S` witness theorem is conditional on positive complementary
energy, or on the explicit surplus inequality

```text
remainder energy
  > 3 * (approximation budget + closed-term budget).
```

No current theorem proves this inequality again after replacing `S` by the
larger set `S'`.  Consequently the verified lower bound on the number of
strict updates is currently exactly one, not a function tending to infinity.

## Blocker 2: the witness is not localized in the Carlson strip

The Sharp witness has type

```text
rho ∈ nontrivialZerosFinset T
rho ∉ S
```

Carlson's count `zeroDensityCount sigma T` only includes zeros satisfying

```text
0 < rho.im
sigma < rho.re.
```

The current witness theorem supplies neither inequality.  Thus even a
repeated sequence of distinct witnesses would not yet give a lower bound for
the zero-density count to which Carlson applies.

The minimum missing localization output is

```text
∃ rho,
  rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
  rho ∉ S.
```

## Blocker 3: one zero per logarithmic window is asymptotically too slow

For fixed `1/2 < sigma < 1`, the formal Carlson majorant has the shape

```text
C * ‖T ^ (4 * sigma * (1 - sigma)) * (Real.log T) ^ 4‖.
```

Its power exponent

```text
alpha = 4 * sigma * (1 - sigma)
```

is strictly positive.

The Sharp proportional window is

```text
[a, (1 + epsilon) * a]
```

in the logarithmic variable, with selected zero height

```text
T ≈ exp (a / 2).
```

Two optimistic schedules are still insufficient:

1. One new right-strip zero per additive unit of `a` gives only
   `O(log T)` zeros up to height `T`.
2. Requiring disjoint proportional `a`-windows gives only
   `O(log log T)` windows up to height `T`.

For every fixed positive `alpha`, Mathlib's theorem
`Real.isLittleO_log_rpow_atTop` certifies

```text
log T = o(T ^ alpha).
```

Therefore either polylogarithmic schedule is already negligible compared
with the power part of Carlson's allowed upper bound, before the additional
`(log T)^4` factor is included.

## Minimum quantitative target that could matter

A Carlson contradiction needs all three of the following:

1. an `S`-relative surplus theorem that can be reapplied after every update;
2. a witness in a fixed right strip `sigma < Re rho`, not merely an arbitrary
   nontrivial zero;
3. a lower count that eventually exceeds
   `T ^ alpha * (log T)^4`, where `alpha = 4 * sigma * (1 - sigma)`.

Linear growth in an iteration depth can only help if the accessible height
grows sufficiently slowly with that depth.  With logarithmic-window spacing,
linear growth is not enough.  The earlier exponential-layer strategy remains
relevant only if it can produce genuinely distinct right-strip zeros while
controlling the height cost of each generation.

## Claim boundary

The one-step detect-or-count theorem is closed.  Persistent right-strip
growth and a Carlson-beating rate are not closed.  No zero-density
contradiction, zero exclusion, or Riemann-hypothesis result follows from the
current chain.
