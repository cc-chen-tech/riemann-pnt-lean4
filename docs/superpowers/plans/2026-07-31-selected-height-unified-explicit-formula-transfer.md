# Selected-height unified explicit-formula transfer plan

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualSelectedHeightUnifiedTargetTransfer.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualSelectedHeightUnifiedTargetTransferContract.lean`
- `Test/ZeroDensityLayerBudgetActualSelectedHeightUnifiedTargetTransferAxiomAudit.lean`

## Theorem chain

1. Transfer stack41 full-tail decay to the signed selected complement.
2. Combine closed real-axis, selected remainder, and selected complement.
3. Instantiate the exact explicit-formula decomposition at `H`.
4. Apply the unified PNT upper/lower transfer.
5. Add contract and axiom audit.

## Validation

Use direct Lean compilation and minimal `.olean` generation.

## PR boundary

This PR contains selected-height unified transfer only.  Automatic
construction of a concrete good-height certificate is separate.
