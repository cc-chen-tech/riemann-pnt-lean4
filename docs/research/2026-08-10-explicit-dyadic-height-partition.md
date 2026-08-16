# Explicit dyadic height partition

## Purpose

The actual explicit formula has a finite outer height, while the convenient
Carlson estimates are stated on full dyadic shells.  This note constructs the
finite shell cover exactly and explains why summing it does not add a factor
equal to the number of shells.

The key rule is:

> Intersect the last full dyadic shell with the actual outer range, use
> nonnegative monotonicity to apply the full-shell estimate, and sum the
> geometrically decaying shell bounds.

## Finite shell count

Fix

```text
0 < H,
H < U.
```

Define

```text
M := ceil (log (U / H) / log 2).
```

Since `1 < 2`, `log 2 > 0`.  The ceiling property gives

```text
log (U/H) <= M * log 2,
U <= 2^M * H.
```

For `n : Fin M`, put

```text
T(n) := 2^n * H,

FullShell(n)
  := Set.Ico (T(n)) (2*T(n)).
```

The actual truncated shell is

```text
TruncatedShell(n)
  := FullShell(n) intersect Set.Ico H U.
```

Then

```text
Set.Ico H U
  = union n : Fin M, TruncatedShell(n).
```

With the half-open convention, these shells are pairwise disjoint.

For `t in [H,U)`, a witnessing index is obtained from

```text
n := floor (log (t/H) / log 2).
```

The proof must separately establish `n < M` from `t < U` and the ceiling
definition.

## Signed ordinate shells

For zeta zeros, apply the construction to the positive quantity

```text
t := sign * Im rho
```

for `sign in {+1,-1}`.  Define

```text
SignedFullShell(sign,n)
  := {rho |
       T(n) <= sign * Im rho,
       sign * Im rho < 2*T(n)}.
```

The positive and negative families are disjoint because `H>0`.  Their union
covers

```text
H <= |Im rho| < U.
```

Combining the signs costs one explicit factor two after the separate shell
estimates.

## Truncation monotonicity

The actual last shell may stop before `2*T(n)`.  For every nonnegative
analytic-multiplicity mass,

```text
mass(TruncatedShell(n)) <= mass(FullShell(n)).
```

The same holds after intersecting with a real-part strip and deleting a finite
retained set `S`:

```text
mass((TruncatedShell(n) intersect realStrip) \ S)
  <= mass(FullShell(n) intersect realStrip).
```

Thus Carlson and local multiplicity are applied only to the standard full
shell.  No density estimate is reproved for the last shell, the outer cutoff,
or `S`.

## Middle direct-L2 sum

For one real strip, suppose the signed full-shell energy bound is

```text
Energy(n)
  <= Cmiddle
       * X^supportExponent
       * T(n)^(q - 2)
       * (1 + log T(n))^5,
```

with

```text
q <= 1,
1 <= H.
```

Then

```text
T(n)^(q-2)
  <= H^(q-2) * 2^(-n),

1 + log T(n)
  <= (1 + log H) * (n+1).
```

Hence every finite initial sum satisfies

```text
sum n : Fin M, Energy(n)
  <= 2164 * Cmiddle
       * X^supportExponent
       * H^(q-2)
       * (1 + log H)^5,
```

using

```text
sum n >= 0, 2^(-n) * (n+1)^5 = 2164.
```

The constant is independent of `M` and `U`.

If

```text
H = X^gammaLow,
```

the polynomial exponent is

```text
supportExponent + gammaLow * (q-2).
```

The upper middle height `U = X^gammaHigh` does not enter the exponent.

## Cubic high-L1 sum

For one real strip, suppose the signed full-shell amplitude bound is

```text
Amplitude(n)
  <= Chigh
       * X^supportExponent
       * X^(2*d)
       * T(n)^(q-3)
       * (1 + log T(n))^4,
```

with `q<=1`.  Since `q-3<=-2`, one may use the weaker but convenient bound

```text
T(n)^(q-3)
  <= H^(q-3) * 2^(-n).
```

The exact fourth moment

```text
sum n >= 0, 2^(-n) * (n+1)^4 = 300
```

gives

```text
sum n : Fin M, Amplitude(n)
  <= 300 * Chigh
       * X^supportExponent
       * X^(2*d)
       * H^(q-3)
       * (1 + log H)^4.
```

For

```text
H = X^gammaHigh,
U = X^alpha,
```

the high-tail exponent is

```text
supportExponent + 2*d + gammaHigh*(q-3).
```

Again, the outer height affects the finite shell count but not the geometric
tail exponent.

## Why the shell count is not a log loss

For polynomial heights,

```text
M = O(log X).
```

A crude estimate

```text
sum n : Fin M, bound(n)
  <= M * max_n bound(n)
```

would therefore introduce a false additional logarithm.  This is forbidden
because `bound(n)` decays geometrically in `n`.

The production theorem must use the finite-to-infinite comparison

```text
sum n : Fin M, nonnegativeTerm(n)
  <= sum' n : Nat, nonnegativeMajorant(n)
```

followed by the explicit moment identity.  The resulting losses remain:

```text
middle direct-L2 energy: (log X)^5,
cubic high-L1 amplitude: (log X)^4.
```

## Two-height actual partition

With

```text
Hlow  := X^gammaLow,
Hhigh := X^gammaHigh,
Houter := X^alpha,

gammaLow < gammaHigh < alpha,
```

construct two finite partitions:

```text
middle:
  [Hlow,Hhigh),

high:
  [Hhigh,Houter).
```

Their union is exactly

```text
[Hlow,Houter),
```

and they are disjoint by the shared half-open endpoint convention.  The low
retained cluster uses

```text
|Im rho| < Hlow.
```

Therefore the retained cluster, middle complement, and high complement form a
single exact partition of the zero range below the outer contour.

The same finite set `S` is deleted from both complement partitions.

## Proposed theorem chain

```text
dyadicShellCount
dyadicShellCount_pos
upper_le_two_pow_shellCount_mul
dyadicFullShell
dyadicTruncatedShell
dyadicTruncatedShell_subset_full
dyadicTruncatedShells_pairwiseDisjoint
dyadicTruncatedShells_iUnion_eq
signedDyadicShells_iUnion_eq_absRange
signedDyadicShells_disjoint
dyadicShellMass_truncated_le_full
dyadicShellMass_delete_le_full
finiteDyadicFifthMomentSum_le
finiteDyadicFourthMomentSum_le
middleDyadicEnergySum_le
cubicHighDyadicAmplitudeSum_le
twoHeightDyadicPartition
twoHeightDyadicPartition_delete
```

Names are provisional.

## Audit rules

- Require `0 < H < U`.
- Prove exact coverage and pairwise disjointness.
- Estimate the truncated last shell by full-shell monotonicity.
- Treat positive and negative ordinates separately.
- Use analytic multiplicity as a weight.
- Delete `S` by nonnegative monotonicity.
- Never multiply the first-shell estimate by `M`.
- Preserve log losses five and four exactly.
- Keep `gammaLow`, `gammaHigh`, and `alpha` distinct.
- Do not import Sharp or half-isolated lower-bound modules.
