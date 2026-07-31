# Fixed Carlson Geometry Shrinking-Gap Obstruction Design

## Purpose

Stack84 accepts an exact dynamic Carlson budget tending to zero while the
outside cap approaches the target line.  This stack determines when the usual
fixed-geometry Carlson power envelope can establish that hypothesis.

The result is deliberately about the proof envelope, not a lower bound for the
actual zero mass.  Failure of an upper-bound envelope to tend to zero does not
imply that the quantity it bounds is large.

## Core arithmetic

For a fixed density penalty `p`, target real part `beta`, and moving cap
`capTau x`, define

```text
E(x) = x^(p + capTau(x) - beta).
```

There are two complementary theorems.

### Sufficient logarithmic margin

If

```text
((beta - capTau(x)) - p) * log(x) -> +infinity,
```

then `E(x) -> 0`.  This is the exact growth-rate condition hidden by a fixed
negative exponent argument.

### Fixed positive penalty obstruction

If `p > 0` and `capTau(x) -> beta`, then `E(x)` does not tend to zero.  Indeed,
the exponent tends to `p`, so it is eventually positive, and `E(x) >= 1` for
`x >= 1`.

This theorem does not assert that `E(x) -> +infinity`, because non-decay is the
minimal statement needed to rule out this majorant route and is substantially
simpler to audit.

## Carlson specialization

The low two-height Carlson target exponent is

```text
carlsonTwoHeightDensityExponent(sigma) * gamma + capTau(x) - beta.
```

For `1/2 < sigma < 1` and `gamma > 0`, the fixed penalty

```text
pLow = 4 * sigma * (1 - sigma) * gamma
```

is strictly positive.  Therefore a fixed `sigma` and fixed positive inner
height exponent `gamma` cannot certify a cap satisfying `capTau(x) -> beta`
through the standard Carlson low-budget power envelope.

The conclusion is methodological and precise: a genuine shrinking-gap proof
must make at least one part of the geometry dynamic, for example
`sigma(x) -> 1`, `gamma(x) -> 0`, or a finer layer decomposition with a
vanishing effective density penalty.

## Theorem chain

The new module exposes:

1. `shrinkingGapPowerEnvelope`.
2. `tendsto_shrinkingGapPowerEnvelope_zero_of_logMargin`.
3. `not_tendsto_shrinkingGapPowerEnvelope_zero_of_fixedPositivePenalty`.
4. `fixedCarlsonLowPenalty_pos`.
5. `not_tendsto_fixedCarlsonLowPowerEnvelope_zero_of_cap_tendsto_target`.

The final theorem is only a specialization of the general obstruction; it does
not introduce a new zero-density axiom.

## Files and ownership

- `PrimeNumberTheorem/ZeroDensityLayerBudgetShrinkingGapFixedGeometryObstruction.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetShrinkingGapFixedGeometryObstructionContract.lean`
- `Test/ZeroDensityLayerBudgetShrinkingGapFixedGeometryObstructionAxiomAudit.lean`

No existing Lean file is modified.  In particular, the frozen complementary
bound, Sharp/localized pi/2, VK-edge, and zero-reproduction modules remain
untouched.

## Verification

Compile the new main module and contract directly and run the focused axiom
audit.  Publish the design, plan, and implementation as separate commits in a
Draft PR stacked on PR #138.

## Claim boundary

This stack does not prove that the actual Carlson budget fails to decay, does
not prove any zero lower bound, and does not prove or disprove a shrinking cap
for zeta zeros.  It proves that the standard fixed-parameter power-envelope
argument is quantitatively insufficient when the cap converges to the target
line, and records the exact logarithmic margin a successful replacement must
supply.
