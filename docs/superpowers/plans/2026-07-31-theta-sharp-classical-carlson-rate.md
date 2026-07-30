# Theta-sharp classical Carlson rate implementation plan

> Execute this bounded stack after the balanced closed-form full-PNT stack.

## Scope

Generalize the coarse classical Carlson exponent from `rate/4` to every
`theta * rate` with `0 < theta < 1/2`, and transfer it to the actual
fixed-anchor zero mass.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpRate.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpRateContract.lean`
- `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpRateAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-theta-sharp-classical-carlson-rate-design.md`
- `docs/superpowers/plans/2026-07-31-theta-sharp-classical-carlson-rate.md`

## Steps

1. Define the theta-family square-root-log majorant.
2. Prove the exact eventual negative-exponent inequality for `theta < 1/2`.
3. Bound the layered coarse ratio by the theta majorant.
4. Prove its polynomial-times-exponential identity and convergence.
5. Transfer it to the actual fixed-anchor zeta mass.
6. Prove strict improvement over the old quarter-rate and the strict upper
   limit at one quarter of the balanced height rate.
7. Add a public contract and axiom audit.
8. Run only the focused module build and audit.
9. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Keep the endpoint strict at `theta < 1/2`.
- Do not weaken the genuine fixed-anchor mass statement.
- Do not modify complementary-zero or VK-edge files.
- Do not claim the unattained endpoint `theta = 1/2`.
- Stage only the five files listed above.
