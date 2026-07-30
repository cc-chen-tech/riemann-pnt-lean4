# Classical dyadic Carlson quantitative middle-mass implementation plan

> Execute this bounded stack only after the quantitative Carlson-mass stack.

## Scope

Expose a pointwise low-strip majorant and add it to the explicit Carlson
right-layer majorant.  Preserve selector-dependent low-strip constants.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeMiddleMass.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeMiddleMassContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeMiddleMassAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-classical-dyadic-carlson-quantitative-middle-design.md`
- `docs/superpowers/plans/2026-07-31-classical-dyadic-carlson-quantitative-middle.md`

## Steps

1. Extract the pointwise low-strip inequality hidden in the earlier qualitative
   squeeze proof.
2. Fix `alpha=1/64` and expose the `m^(-7/64) * (log m)^4` identity.
3. Prove the low-strip majorant tends to zero.
4. Add it to the stack-21 Carlson square-root-log majorant.
5. Transfer the sum to the complete moving-middle mass for each selector.
6. Add a public contract and axiom audit.
7. Run only the focused module build and audit.
8. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Do not modify complementary-zero or VK-edge files.
- Do not move selector-dependent low-strip constants outside their proven
  quantifier scope.
- Do not describe this middle-mass estimate as a full quantitative PNT error.
- Stage only the five files listed above.
