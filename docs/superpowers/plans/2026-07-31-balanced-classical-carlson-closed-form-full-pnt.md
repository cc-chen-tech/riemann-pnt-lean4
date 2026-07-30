# Balanced classical Carlson closed-form full-PNT implementation plan

> Execute this bounded stack after the balanced quantitative Carlson mass
> stack.

## Scope

Reassemble every quantitative upper-transfer layer while retaining the exact
balanced gap-rate relation in the final full-PNT endpoint.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedClosedFormFullPNT.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedClosedFormFullPNTContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedClosedFormFullPNTAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-balanced-classical-carlson-closed-form-full-pnt-design.md`
- `docs/superpowers/plans/2026-07-31-balanced-classical-carlson-closed-form-full-pnt.md`

## Steps

1. Consume the balanced quantitative middle/strip mass endpoint.
2. Add selector-dependent critical-half and low-strip pointwise majorants.
3. Assemble the positive and complete finite zero-tail bounds.
4. Add the closed-form explicit-formula remainder and closed-axis terms.
5. Prove the final majorant tends to zero and bounds the actual PNT error.
6. Retain both exact rate equalities in the final theorem statement.
7. Add a public contract and axiom audit.
8. Run only the focused module build and audit.
9. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Do not reselect or existentially hide the balanced gap rate.
- Preserve selector-dependent norm constants inside each selector.
- Do not modify complementary-zero or VK-edge files.
- Do not claim the coarse `alpha*/8` rate is analytically optimal.
- Stage only the five files listed above.
