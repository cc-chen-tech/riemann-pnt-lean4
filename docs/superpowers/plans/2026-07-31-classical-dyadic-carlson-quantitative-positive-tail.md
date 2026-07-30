# Classical dyadic Carlson quantitative positive-tail implementation plan

> Execute this bounded stack after the quantitative moving-middle stack.

## Scope

Expose the selected-height critical-half pointwise majorant and combine it with
the quantified moving-middle and right-strip terms into one positive-zero-tail
majorant.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativePositiveTail.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativePositiveTailContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativePositiveTailAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-classical-dyadic-carlson-quantitative-positive-tail-design.md`
- `docs/superpowers/plans/2026-07-31-classical-dyadic-carlson-quantitative-positive-tail.md`

## Steps

1. Extract the generic eventual pointwise selected-height hybrid majorant.
2. Specialize it to the critical-half layer with exponent `-31/64`.
3. Prove the critical-half majorant tends to zero.
4. Combine it with the moving-middle majorant and the moving-strip Carlson
   majorant.
5. Transfer the sum to `dynamicPositivePNTTailNorm` for every selector.
6. Add a public contract and axiom audit.
7. Run only the focused module build and audit.
8. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Do not modify complementary-zero or VK-edge files.
- Preserve selector-dependent norm-separation constants.
- Do not call the positive-zero-tail bound a complete explicit-formula error.
- Stage only the five files listed above.
