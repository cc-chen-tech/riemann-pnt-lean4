# Moving Right-Edge Signed Seed Stability Design

## Goal

Upgrade the stack81 fixed-seed moving-cluster transfer from an unsigned
absolute-value witness to a common positive and negative witness pair.

Given target-line seed witnesses at coefficient `c` and a shared moving
extension budget `loss`, the actual relative Chebyshev error must have both
signs at amplitude

```text
((c - loss) * targetZeroPowerAmplitude beta x) / 2.
```

## Scope

This stack belongs only to the density/transfer layer. It consumes signed
natural-point seed witnesses and does not construct them. In particular, it
does not modify or duplicate localized pi-over-two or other sharp oscillation
proofs.

## Existing interfaces

Stack81 supplies:

- `IsTargetRealPartNontrivialZeroSeed`;
- automatic eventual visibility of a fixed target-line seed;
- unsigned moving-family seed stability;
- coefficient-preserving actual moving-cluster transfer.

The repository also supplies:

- positive and negative natural-point witness predicates;
- `transfer_eventually_sub_lt` for both signs;
- natural-point to real-variable signed witness embedding;
- a common half-amplitude bound for three negligible natural-point
  remainders.

No signed natural-point three-remainder assembler currently packages these
pieces for the moving cluster.

## Theorem chain

### 1. Positive moving-seed stability

For `S : N -> Finset C`, eventual inclusion `S0 subset S(m)`, a positive seed
witness at `c * A(m)`, and

```text
abs(dynamicVisibleClusterPNTMain T (S(m) \ S0) m)
  < loss * A(m)
```

eventually, prove a positive moving-cluster witness at

```text
(c - loss) * A(m).
```

### 2. Negative moving-seed stability

Prove the identical coefficient statement for negative seed witnesses. Both
signs use the same moving-extension budget.

### 3. Signed actual moving-seed transfer

At the selected good height:

1. prove the fixed seed is eventually contained in the moving right-edge
   cluster;
2. stabilize both seed signs to the whole moving main;
3. rescale closed-axis, contour, and moving-complement negligibility by the
   positive coefficient `c - loss`;
4. obtain one eventual bound

```text
abs(realAxis + contour + complement)
  < ((c - loss) * A) / 2;
```

5. rewrite the exact moving explicit formula to turn this into

```text
abs(actualError - movingMain)
  < ((c - loss) * A) / 2;
```

6. apply positive and negative `transfer_eventually_sub_lt`;
7. normalize the resulting algebraic amplitude to
   `((c - loss) * A) / 2`;
8. embed both natural-point witnesses into
   `HasFarSignedTargetAmplitudeWitnesses`.

### 4. Unified and automatic parameters

Pair the signed lower transfer with fixed-rate PNT convergence. For
`2 / 3 < beta < 1`, use the same joint two-height selector as stacks80-81 and
return the signed implication for every selected uniform good height.

The automatic theorem consumes only:

- a finite actual target-line seed;
- positive and negative seed witnesses at the same coefficient `c`;
- one shared moving-extension budget at coefficient `loss`;
- positivity of `c - loss`.

## Files

Create:

```text
PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer.lean
PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransferContract.lean
Test/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransferAxiomAudit.lean
docs/superpowers/plans/2026-07-31-moving-right-edge-signed-seed-stability.md
```

Do not modify:

```text
PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean
```

Do not modify VK-edge, sharp, or localized pi-over-two modules.

## Claim boundary

This stack proves that signed fixed-seed oscillation survives the moving
right-edge Carlson/explicit-formula transfer with an exact auditable
coefficient.

It does not prove:

- either signed seed witness;
- the moving-extension budget;
- unconditional Omega-plus-minus;
- RH;
- any exceptional-zero reproduction or proliferation result.

The remaining lower-bound boundary is therefore unchanged mathematically but
is sharper logically: a sharp/local theorem may provide the signed seed
witnesses, while a density or gap theorem may provide the moving-extension
budget, and this stack performs the exact actual-PNT assembly.

## Verification

Use one direct Lean process at a time:

```text
implementation compile
contract compile
focused axiom audit
```

The audit allowlist remains:

```text
propext
Classical.choice
Quot.sound
```

Publish a stacked draft PR based on stack81, with design, plan, and Lean code
in separate commits.
