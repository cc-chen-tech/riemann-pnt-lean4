# Moving Right-Edge Seed Stability Design

## Goal

Transfer a fixed finite target-line zero-cluster witness through the moving
right-edge cluster introduced in stack78-80, while preserving the exact
coefficient loss caused by the newly visible cluster members.

The final actual-PNT amplitude must be

```text
((c - loss) * targetZeroPowerAmplitude beta x) / 2.
```

The theorem must not assume a global zero-free region or an outside-cluster
real-part cap.

## Existing boundary

Stack79 proves that the complete actual zero complement outside

```text
movingRightEdgeExceptionalCluster H tau x
```

is negligible at the target amplitude. Stack80 transfers a witness for the
whole moving visible cluster to the actual relative Chebyshev error.

The missing interface is inside the moving main term. Existing finite-seed
stability only treats one fixed extension `S0 subset S`; it cannot be applied
directly when the extension is `S m`.

## Considered approaches

### Modify stack80 to accept an arbitrary seed

This would mix moving-complement Carlson estimates with finite-sum
anti-cancellation bookkeeping. It would also enlarge an already published
stack boundary.

### Add a fully abstract moving-cluster facade

This would be reusable but would add another broad interface without
discharging an actual zeta condition.

### Add generic moving finite-sum stability and specialize immediately

This keeps the algebra reusable while the public theorem speaks directly
about actual zeta zeros, the selected good height, and the real PNT error.
This is the selected approach.

## Definitions

Introduce a predicate for a finite target-line seed:

```lean
def IsTargetRealPartNontrivialZeroSeed
    (beta : R) (S0 : Finset C) : Prop :=
  forall rho in S0,
    RiemannHypothesis.IsNontrivialZero rho /\ rho.re = beta
```

No conjugation hypothesis is needed for the unsigned transfer. The moving
right-edge cluster itself remains conjugation invariant and captures the
complete real-ordinate slice.

## Theorem chain

### 1. Moving finite-sum decomposition

For an eventually increasing family `S : N -> Finset C`, prove pointwise:

```text
dynamicVisibleClusterPNTMain T (S m) m
  = dynamicVisibleClusterPNTMain T S0 m
    + dynamicVisibleClusterPNTMain T (S m \ S0) m.
```

The proof reuses
`dynamicVisibleClusterPNTMain_eq_seed_add_extension` at each natural point.

### 2. Moving seed-witness stability

Assume:

```text
S0 subset S(m) eventually,
seed main has far witnesses at c * A(m),
abs(extension main) < loss * A(m) eventually.
```

Then the moving main has far witnesses at

```text
(c - loss) * A(m).
```

This is an exact coefficient statement. It neither constructs the seed
witness nor proves the extension budget.

### 3. Automatic eventual visibility of an actual target-line seed

If `S0` is a target-line nontrivial-zero seed, `tau < beta`, and
`Tendsto H atTop atTop`, then eventually

```text
S0 subset movingRightEdgeExceptionalCluster H tau x.
```

Finiteness of `S0` combines the individual eventual height bounds. Membership
uses `mem_rightEdgeNontrivialZerosFinset`; the real-ordinate adjoin remains
available but is not required for this argument.

### 4. Coefficient-preserving fixed-parameter actual transfer

At the selected good height, combine:

```text
fixed seed witness at c * x^(beta-1),
moving extension budget at loss * x^(beta-1),
closed-axis target negligibility,
selected contour target negligibility,
moving Carlson complement target negligibility.
```

The retained moving-main coefficient is `c - loss`. Require
`0 < c - loss`, rescale all three negligible remainders by this positive
constant, and apply the existing three-remainder natural-point assembler.

The conclusion is an actual far witness at

```text
((c - loss) * x^(beta-1)) / 2.
```

### 5. Unified and automatic-parameter outputs

Package the lower transfer with the existing fixed-rate PNT convergence.
Then use the joint two-height parameter selector at anchor `1 / 2`.

For `2 / 3 < beta < 1`, return `sigma`, `tau`, and `alpha` such that every
uniform good-height selection supports the seed-stability implication.

## Files

Create:

```text
PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer.lean
PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransferContract.lean
Test/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransferAxiomAudit.lean
docs/superpowers/plans/2026-07-31-moving-right-edge-seed-stability.md
```

Do not modify:

```text
PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean
```

Do not modify VK-edge or sharp/localized oscillation modules.

## Mathematical claim boundary

This stack closes the transfer from a fixed seed witness to the moving-cluster
input required by stack80, conditional on a quantitative bound for the newly
visible members.

It does not prove:

- the fixed seed oscillation witness;
- the moving extension budget;
- an unconditional Omega or Omega-plus-minus theorem;
- RH;
- a zero-reproduction tree.

The remaining mathematical interface is deliberately explicit:

```text
abs(moving newly visible contribution)
  < loss * target amplitude eventually.
```

That interface can be discharged either by a local mean-square/sharp theorem
or by a density estimate with a genuine real-part gap.

## Verification

Compile only the new implementation and contract with direct `lake env lean`
commands and dedicated output paths. Run the focused axiom audit and require
the same allowlist as the preceding stack:

```text
propext
Classical.choice
Quot.sound
```

Publish as a stacked draft PR based on stack80, with documentation and Lean
code in separate commits.
