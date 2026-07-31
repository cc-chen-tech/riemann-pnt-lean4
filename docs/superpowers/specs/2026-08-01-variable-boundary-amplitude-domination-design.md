# Variable-Boundary Amplitude Domination Design

## Goal

Reuse remainder estimates proved at a fixed exponent `beta0` when the active
explicit-formula boundary has a moving exponent `beta m` satisfying
`beta0 <= beta m` eventually.

## Mathematical interface

For natural points `m >= 1`, monotonicity of real powers gives

```text
m ^ (beta0 - 1) <= m ^ (beta m - 1).
```

Consequently, if `a m` and `b m` are eventually positive, `a m <= b m`
eventually, and

```text
|r m| / a m -> 0,
```

then `|r m| / b m -> 0`. The generic statement belongs to the existing
`NaturalPointTargetAmplitudeNegligible` interface; the fixed-to-moving power
statement is its zeta-transfer specialization.

## Files and ownership

- `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryAmplitudeDomination.lean`
  contains the generic denominator-domination lemma and the fixed-to-moving
  target-amplitude specialization.
- `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryAmplitudeDominationContract.lean`
  checks only the new public declarations.
- `Test/ZeroDensityLayerBudgetVariableBoundaryAmplitudeDominationAxiomAudit.lean`
  prints their axiom dependencies.

No protected complementary-bound, localized oscillation, or VK-edge module is
modified.

## Claim boundary

This layer transports already available remainder negligibility to a larger
moving target amplitude. It does not construct a moving right-edge schedule,
prove an anti-cancellation witness for the moving package, establish both
oscillation signs, or imply RH.

## Verification

Compile the implementation, contract, and axiom-audit targets with one Lean
process and the established overlay. The accepted audit dependency set is
`propext`, `Classical.choice`, and `Quot.sound`.
