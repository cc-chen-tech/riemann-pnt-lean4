# Classical dyadic Carlson quantitative full-PNT implementation plan

> Execute this bounded stack after the quantitative full-zero-tail stack.

## Scope

Combine the complete finite-zero majorant with the exact closed real-axis term
and the certified classical explicit-formula remainder upper bound.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullPNT.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullPNTContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullPNTAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-classical-dyadic-carlson-quantitative-full-pnt-design.md`
- `docs/superpowers/plans/2026-07-31-classical-dyadic-carlson-quantitative-full-pnt.md`

## Steps

1. Define the complete natural relative-PNT error majorant.
2. Expose natural-point decay of the absolute closed real-axis term.
3. Combine zero-tail, closed-axis, and certified remainder limits.
4. Prove the pointwise explicit-formula triangle inequality assembler.
5. Instantiate it with the classical Pintz-Carlson selected height.
6. Add a public contract and axiom audit.
7. Run only the focused module build and audit.
8. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Retain `cofinalPNTFormulaRemainderBound` as the actual certified contour bound.
- Do not claim an optimized closed-form PNT rate.
- Do not modify complementary-zero or VK-edge files.
- Stage only the five files listed above.
