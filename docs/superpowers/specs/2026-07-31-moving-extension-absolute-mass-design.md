# Moving Extension Absolute-Mass Design

## Goal

Discharge the moving-extension budget left explicit in stacks81-82 under a
genuine outside-seed real-part gap, without making an invalid comparison
between a sub-sum norm and a complete signed-tail norm.

For signed seed witnesses at coefficient `c > 0`, the final automatic theorem
must produce actual positive and negative PNT witnesses at coefficient
`c / 4`.

## Why the signed tail norm is insufficient

The moving extension is a subset of the complete zero tail outside the fixed
seed. It is not valid to conclude

```text
norm(sub-sum) <= norm(complete sum).
```

The complete sum may be small because of cancellation between terms that are
not present in the sub-sum. Therefore
`dynamicFullOutsideClusterPNTZeroTailNorm` cannot dominate the moving
extension.

The correct majorant is the sum of the norms of all outside-seed terms. This
absolute mass is monotone under finite-set inclusion and is immune to phase
cancellation.

## New absolute-mass objects

For a dynamic height `H` and fixed finite seed `S0`, define:

```text
dynamicPositiveOutsideClusterPNTAbsoluteMass H S0 x
dynamicRealOrdinateOutsideClusterPNTAbsoluteMass H S0 x
dynamicFullOutsideClusterPNTAbsoluteMass H S0 x.
```

Each is the finite sum of

```text
norm(pntRelativeZeroContribution x rho)
```

over the corresponding positive, real-ordinate, or complete outside-seed
zero set.

## Theorem chain

### 1. Positive absolute-mass Carlson majorant

Use the canonical two-strip bucket decomposition of the positive outside-seed
zero set.

The low layer absolute mass is bounded by the polynomial-envelope two-height
low and high-annulus masses. The high layer absolute mass is bounded by the
actual Carlson strip mass. Both bounds are already multiplicity-aware.

This gives a pointwise selected-height estimate:

```text
positive absolute mass
  <= low two-height mass + high Carlson strip mass.
```

Under the existing exponent margins, conclude

```text
TargetAmplitudeNegligible A_beta
  (dynamicPositiveOutsideClusterPNTAbsoluteMass H S0).
```

### 2. Real-ordinate absolute-mass decay

Once `H(x) >= 0`, the real-ordinate outside-seed set is the fixed finite set at
height zero. If every member has real part strictly below `beta`, finite
summation of

```text
norm(contribution rho) / A_beta -> 0
```

proves target-amplitude negligibility of the real absolute mass.

### 3. Negative absolute mass by conjugation

If `S0` is conjugation invariant and `x > 0`, conjugation bijects the negative
and positive outside-seed sets and preserves contribution norms. Hence

```text
full absolute mass =
  positive absolute mass + positive absolute mass + real absolute mass.
```

The positive and real decay theorems then imply full absolute-mass decay.

### 4. Moving-extension domination

For every finite set `E`, prove pointwise:

```text
abs(dynamicVisibleClusterPNTMain H (E \ S0) x)
  <= dynamicFullOutsideClusterPNTAbsoluteMass H S0 x.
```

The proof uses:

1. `abs(re z) <= norm z`;
2. the triangle inequality for the finite sum;
3. pointwise domination of the extension indicator by the outside-seed
   indicator;
4. monotonicity of a nonnegative absolute sum.

Specialize `E` to `movingRightEdgeExceptionalCluster H tau x`. Full absolute
mass decay then gives target-amplitude negligibility of the exact moving
extension used by stacks81-82.

### 5. Automatic genuine-gap signed transfer

Assume:

```text
2 / 3 < beta < 1,
theta < (3 * beta - 1) / 2,
c > 0,
S0 is a finite target-line nontrivial-zero seed,
S0 is conjugation invariant,
all positive nontrivial zeros outside S0 satisfy Re rho <= theta,
all real-ordinate nontrivial zeros outside S0 satisfy Re rho < beta.
```

Select `sigma`, `tau`, and `alpha` with `theta < tau < beta`. The outside cap
supplies the high-strip endpoint bound. Absolute-mass decay supplies the
moving-extension budget for every positive loss.

Choose

```text
loss = c / 2.
```

Then stack82 retains

```text
(c - c / 2) / 2 = c / 4
```

for both signs of the actual relative Chebyshev error, while also returning
the existing fixed-rate PNT convergence.

## Files

Create:

```text
PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass.lean
PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMassContract.lean
Test/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMassAxiomAudit.lean
docs/superpowers/plans/2026-07-31-moving-extension-absolute-mass.md
```

Do not modify:

```text
PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean
```

Do not modify sharp, localized pi-over-two, VK-edge, or zero-reproduction
modules.

## Claim boundary

This stack removes the moving-extension budget as an external hypothesis only
under a genuine outside-seed real-part gap. It does not prove that such a gap
exists.

It also does not prove:

- the signed fixed-seed witnesses;
- an unconditional Omega-plus-minus theorem;
- RH;
- a rightmost zero exists;
- exceptional-zero reproduction.

The theorem is nevertheless a closed and nonvacuous transfer machine: a
finite rightmost signed seed plus an actual gap now automatically yields an
actual PNT signed oscillation certificate with explicit coefficient `c / 4`.

## Verification

Compile the implementation and contract directly with one Lean process at a
time. Run the focused axiom audit and require only:

```text
propext
Classical.choice
Quot.sound
```

Publish as a stacked draft PR based on stack82, with design, plan, and Lean
code in separate commits.
