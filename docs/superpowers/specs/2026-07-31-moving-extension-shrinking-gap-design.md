# Moving Extension Shrinking-Gap Design

## Status and scope

This stack replaces the fixed outside-seed real-part cap used by stack83 with a
scale-dependent cap that may approach the target real part.  It stays entirely
inside the density/transfer ownership boundary:

- create only `ZeroDensityLayerBudget*ShrinkingGap*` Lean modules;
- create their focused contract and axiom audit;
- do not modify `ZeroForcedOscillationComplementaryBound.lean`;
- do not modify Sharp, localized pi/2, VK-edge, or zero-reproduction modules.

The stack is based on
`research/pintz-carlson-stack-83-moving-extension-absolute-mass` and reuses its
cancellation-free positive, negative, real-ordinate, and full absolute masses.

## Mathematical objective

Let `beta` be the real part of a fixed seed cluster, let `x n` be the PNT
evaluation scale, and let `tau n < beta` be an outside-cluster real-part cap at
the selected height.  Suppose the Carlson layer argument gives a nonnegative
mass coefficient `M n` and the full outside absolute mass satisfies

```text
fullMass n <= M n * (x n)^(tau n - 1).
```

The target-zero amplitude is `(x n)^(beta - 1)`.  Therefore the normalized
outside mass is bounded by

```text
M n * (x n)^(tau n - beta).
```

The new quantitative hypothesis is exactly

```text
M n * (x n)^(tau n - beta) -> 0.
```

It permits `tau n -> beta`.  A fixed positive gap is only one sufficient
special case.  The logarithmic sufficient condition is

```text
log (M n) - (beta - tau n) * log (x n) -> -infinity.
```

The implementation will use the multiplicative limit as the primary interface.
The logarithmic condition will be a separate arithmetic constructor, not a
hidden assumption inside the zeta theorem.

## Rejected approaches

### Keep a fixed epsilon gap

This would merely rename stack83.  It cannot express caps approaching `beta`
and does not advance dynamic zero layering.

### Put the complete Carlson proof in one final theorem

This makes the crucial rate condition hard to audit and couples elementary
real analysis to zeta-specific finite sums.  It also prevents reuse with a
future improved zero-density estimate.

### Control a signed sub-sum by the signed full sum

This is mathematically invalid because cancellation can make the full signed
sum smaller than a sub-sum.  Every extension bound in this stack passes through
the termwise absolute mass introduced in stack83.

## Architecture

### Layer 1: shrinking-gap rate interface

Define a small predicate recording the normalized rate:

```text
HasShrinkingGapMassRate beta x tau M :=
  Tendsto (fun n => M n * (x n)^(tau n - beta)) atTop (nhds 0).
```

The final Lean spelling may expose `Real.rpow` explicitly if elaboration needs
it.  The predicate records only the rate; geometric cap and Carlson hypotheses
remain separate.

Prove an abstract transfer lemma:

```text
mass n <= M n * (x n)^(tau n - 1)
HasShrinkingGapMassRate beta x tau M
------------------------------------------------
mass n / targetZeroPowerAmplitude beta (x n) -> 0.
```

Required side conditions are explicit: eventual positivity of `x n`,
nonnegativity of `mass n` and `M n`, and nonvanishing of the target amplitude.

### Layer 2: logarithmic constructor

Provide a sufficient-condition theorem converting exponential margin into the
multiplicative rate.  Its robust input is an explicit diverging margin `L n`:

```text
0 <= M n
M n <= exp (logMajorant n)
logMajorant n - (beta - tau n) * log (x n) <= -L n
L n -> +infinity
---------------------------------------------------
HasShrinkingGapMassRate beta x tau M.
```

This avoids taking `log 0`, and it lets callers use any convenient upper bound
for the Carlson coefficient.

### Layer 3: actual absolute-mass specialization

Reuse stack83's absolute masses and decomposition.  Introduce a moving-cap
interface asserting that every selected-height positive zero outside the seed
cluster has real part at most `tau n`.  Combine it with the existing low-layer
and Carlson-strip bounds to prove

```text
dynamicFullOutsideClusterPNTAbsoluteMass ... /
  targetZeroPowerAmplitude beta (x n) -> 0.
```

The proof order is:

1. bound the selected positive outside mass by the two-height coefficient;
2. apply the shrinking-gap rate transfer;
3. obtain negative mass from conjugation;
4. add the real-ordinate mass, with its own normalized decay hypothesis;
5. use the stack83 equality `full = 2 * positive + real`;
6. dominate the moving-cluster extension by the full absolute mass.

No signed finite sum is used as a majorant.

### Layer 4: signed PNT transfer

Feed the resulting negligible moving extension into stack82's fixed-seed signed
transfer.  For a seed coefficient `c > 0`, choose the eventual extension loss
`c / 2`; stack82 then yields positive and negative actual PNT witnesses at

```text
(c / 4) * targetZeroPowerAmplitude beta.
```

The theorem accepts the fixed-seed positive and negative witness hypotheses.
It does not manufacture them and does not enter the localized pi/2 proof owned
by the Sharp task.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap.lean`
  contains the rate predicate, arithmetic bridge, actual mass specialization,
  extension decay, and signed PNT composition.
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapContract.lean`
  checks the public theorem signatures without duplicating proofs.
- `Test/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapAxiomAudit.lean`
  prints axioms for the rate bridge, full-mass decay, extension decay, and final
  signed transfer.

Existing Lean files are imported but not edited.

## Public theorem chain

The implementation should expose declarations with these stable roles:

1. `HasShrinkingGapMassRate` records the normalized multiplicative rate.
2. `targetAmplitudeNegligible_of_shrinkingGapMassRate` is the abstract
   majorant-to-normalized-decay lemma.
3. `shrinkingGapMassRate_of_exponentialMargin` constructs the rate from a
   diverging logarithmic margin.
4. `selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap`
   specializes the result to the actual outside-zero absolute mass.
5. `selectedMovingRightEdgeExtension_targetAmplitudeNegligible_of_shrinkingGap`
   transfers full-mass decay to the signed moving extension.
6. `exists_shrinkingGap_positiveOutsideClusterMovingSeedSignedNaturalTargetTransfer`
   composes the result with the actual signed PNT transfer and returns the
   coefficient `c / 4`.

Names may receive a narrowly necessary qualifier to avoid an existing global
name collision, but their mathematical roles and hypotheses must not weaken.

## Verification

Validation is intentionally focused:

1. compile the main module directly with `lake env lean`, writing its `.olean`
   and `.ilean` to the normal build tree;
2. compile the contract directly;
3. run the focused axiom-audit module;
4. require that audited public declarations use only the repository allowlist;
5. do not run a full repository build.

The design, implementation plan, and Lean implementation are separate commits.
The branch is published as a Draft PR stacked on PR #137.

## Claim boundary

This stack proves a conditional shrinking-gap transfer theorem.  It does not
prove that actual zeta zeros admit the moving cap, does not prove the required
Carlson coefficient has the stated rate for every desired schedule, and does
not prove the fixed-seed signed witnesses.  Consequently it does not establish
an unconditional `Omega_+`, `Omega_-`, `Omega_+-`, or RH result.

Its new content is the cancellation-free quantitative threshold showing
exactly when an approaching outside-zero layer is still negligible relative to
the target zero amplitude.
