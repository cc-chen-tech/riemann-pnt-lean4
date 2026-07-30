# Selected-height two-height full-tail implementation plan

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualSelectedHeightTwoHeightFullTail.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualSelectedHeightTwoHeightFullTailContract.lean`
- `Test/ZeroDensityLayerBudgetActualSelectedHeightTwoHeightFullTailAxiomAudit.lean`

## Theorem chain

1. Bound selected high-annulus multiplicity by global multiplicity at the
   polynomial outer height.
2. Derive selected low-plus-high ordinate target-amplitude decay with the
   unchanged stack37 margins.
3. Embed canonical selected layer `1` into the polynomial-height actual
   Carlson strip.
4. Compose the selected positive tail from both canonical layers.
5. Apply conjugation and arbitrary-height real-ordinate residual transfer.
6. Export direct normalized limits and abstract negligibility forms.
7. Add contract and axiom audit.

## Validation

Use direct Lean compilation and minimal `.olean` generation only.

## PR boundary

This PR contains selected-height zero-tail control only.  The selected
explicit-formula unified transfer remains a separate stack.
