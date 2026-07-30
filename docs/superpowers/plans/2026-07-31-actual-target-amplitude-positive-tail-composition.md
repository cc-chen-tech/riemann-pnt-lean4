# Actual target-amplitude positive-tail composition plan

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudePositiveTailComposition.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudePositiveTailCompositionContract.lean`
- `Test/ZeroDensityLayerBudgetActualTargetAmplitudePositiveTailCompositionAxiomAudit.lean`

## Theorem chain

1. Define the target-normalized positive outside-cluster tail.
2. Prove canonical layer `1` is a subset of the actual Carlson strip under
   the explicit outside-cluster real-part cap.
3. Bound canonical layer `1` norm by the actual strip mass.
4. Bound canonical layer `0` norm by the exact stack37 low-plus-high
   ordinate mass.
5. Combine the canonical two-layer cover with these two estimates.
6. Divide by the positive target amplitude.
7. Apply stack37 low-layer decay and stack36 actual-strip decay.
8. Export a contract and audit the composed theorem's axioms.

## Validation

Use direct focused Lean checks to avoid rebuilding unrelated global targets.
Run the repository allowlist checker only if sufficient disk remains after
the focused build.  Record environmental failures separately from theorem
failures.

## PR boundary

The PR contains only positive-tail composition.  Conjugation and the
real-ordinate residual belong in stack39.
