# Actual target-amplitude full-tail conjugation plan

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeFullTailConjugation.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeFullTailConjugationContract.lean`
- `Test/ZeroDensityLayerBudgetActualTargetAmplitudeFullTailConjugationAxiomAudit.lean`

## Theorem chain

1. Define the complete outside-cluster tail normalized by
   `targetZeroPowerAmplitude beta`.
2. Convert stack38 positive-tail convergence into
   `TargetAmplitudeNegligible`.
3. obtain real-ordinate negligibility from the existing strict real-part
   bound theorem.
4. Apply the existing conjugation-invariant full-tail transfer.
5. Simplify the norm absolute value and export a direct `Tendsto` theorem.
6. Add a contract and direct axiom audit.

## Validation

Compile the implementation directly to `.olean/.ilean`, then compile the
contract and run the audit directly.  Avoid a repository-wide build while
parallel tasks are consuming disk.

## PR boundary

The PR contains only full finite-zero-tail composition.  Explicit-formula
contour and real-axis formula remainders belong in stack40.
