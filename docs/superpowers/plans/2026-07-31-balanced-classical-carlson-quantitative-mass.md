# Balanced classical Carlson quantitative-mass implementation plan

> Execute this bounded stack after the balanced truncation-rate stack.

## Scope

Build a parameterized selected-height Carlson mass constructor and instantiate
it with the exact balanced gap rate.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedQuantitativeMass.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedQuantitativeMassContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedQuantitativeMassAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-balanced-classical-carlson-quantitative-mass-design.md`
- `docs/superpowers/plans/2026-07-31-balanced-classical-carlson-quantitative-mass.md`

## Steps

1. Obtain the fixed-anchor quantitative majorant at an arbitrary positive gap
   rate.
2. Dominate every classical selected height by `m^(1/64)`.
3. Transfer the fixed-anchor bound to middle and moving-strip masses.
4. Preserve the input selected zero-free certificate.
5. Instantiate with the exact balanced gap-rate endpoint.
6. Add a public contract and axiom audit.
7. Run only the focused module build and audit.
8. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Preserve the exact gap rate throughout the theorem statement.
- Do not alter the existing Carlson count or coarse majorant.
- Do not modify complementary-zero or VK-edge files.
- Stage only the five files listed above.
