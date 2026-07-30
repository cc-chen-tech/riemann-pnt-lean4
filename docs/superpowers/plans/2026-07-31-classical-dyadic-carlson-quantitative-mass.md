# Classical dyadic Carlson quantitative-mass implementation plan

> Execute this bounded stack only in the explicit-formula unified worktree.

## Scope

Add an explicit square-root-log majorant for the actual classical dyadic
Carlson density contribution.  Do not modify complementary-zero or VK-edge
modules.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeMass.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeMassContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeMassAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-classical-dyadic-carlson-quantitative-mass-design.md`
- `docs/superpowers/plans/2026-07-31-classical-dyadic-carlson-quantitative-mass.md`

## Steps

1. Expose the eventual actual-mass-to-layered-coarse bound.
2. Define the explicit classical square-root-log majorant.
3. Prove the coarse ratio is eventually bounded by the majorant.
4. Prove its polynomial-times-exponential identity and convergence to zero.
5. Transfer the quantitative bound to selected classical admissible heights.
6. Add a public contract and axiom audit.
7. Run only the focused module build and audit.
8. Commit documentation and code separately, push, and open a stacked draft PR.

## Global constraints

- Preserve the existing Pintz/Carlson/explicit-formula interfaces.
- Keep the low strip explicit rather than hiding it in the density majorant.
- Make no claim of a new density estimate, optimal PNT rate, Omega theorem, or
  RH.
- Stage only the five files listed above.
