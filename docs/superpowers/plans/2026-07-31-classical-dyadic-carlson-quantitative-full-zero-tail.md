# Classical dyadic Carlson quantitative full-zero-tail implementation plan

> Execute this bounded stack after the quantitative positive-zero-tail stack.

## Scope

Add an explicit fixed real-ordinate majorant and combine it with conjugation to
control the complete finite nontrivial-zero sum.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullZeroTail.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullZeroTailContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullZeroTailAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-classical-dyadic-carlson-quantitative-full-zero-tail-design.md`
- `docs/superpowers/plans/2026-07-31-classical-dyadic-carlson-quantitative-full-zero-tail.md`

## Steps

1. Define the finite height-zero real-ordinate kernel majorant.
2. Prove every summand and the finite sum tend to zero at natural points.
3. Bound the dynamic real-ordinate norm by the fixed majorant.
4. Add twice the positive-zero-tail majorant using conjugation.
5. Transfer the sum to `dynamicFullPNTZeroTailNorm` for every selector.
6. Add a public contract and axiom audit.
7. Run only the focused module build and audit.
8. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Preserve each real-ordinate zero's actual exponent.
- Do not assume a numerical real-part gap not already proved.
- Do not modify complementary-zero or VK-edge files.
- Do not call the finite zero-tail bound a complete explicit-formula remainder.
- Stage only the five files listed above.
