# Classical dyadic Carlson closed-form full-PNT implementation plan

> Execute this bounded stack after the quantitative full-PNT stack.

## Scope

Replace the final certificate remainder term by the proved explicit
square-root-log contour majorant and exact closed-log term.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonClosedFormFullPNT.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonClosedFormFullPNTContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonClosedFormFullPNTAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-classical-dyadic-carlson-closed-form-full-pnt-design.md`
- `docs/superpowers/plans/2026-07-31-classical-dyadic-carlson-closed-form-full-pnt.md`

## Steps

1. Define and prove decay of the exact closed-log relative term.
2. Bound the selected classical natural remainder by the two-scale contour
   majorant plus the closed-log term.
3. Substitute that bound into the stack-25 full-PNT majorant.
4. Prove the closed-form majorant tends to zero and controls the actual error.
5. Document the contour/Carlson truncation-rate comparison.
6. Add a public contract and axiom audit.
7. Run only the focused module build and audit.
8. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Use the proved contour majorant without weakening its pointwise statement.
- Preserve selector and zero-separation quantifier boundaries.
- Do not modify complementary-zero or VK-edge files.
- Do not claim the current Carlson coarse exponent is optimal.
- Stage only the five files listed above.
