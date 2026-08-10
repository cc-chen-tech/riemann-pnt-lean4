# Classical balanced truncation-rate implementation plan

> Execute this bounded stack after the closed-form full-PNT stack.

## Scope

Retain and formalize the exact relation between the optimized classical height
rate, zero-free gap constant, and current verified Carlson bottleneck.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetClassicalBalancedTruncationRate.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetClassicalBalancedTruncationRateContract.lean`
- `Test/ZeroDensityLayerBudgetClassicalBalancedTruncationRateAxiomAudit.lean`
- `docs/superpowers/specs/2026-07-31-classical-balanced-truncation-rate-design.md`
- `docs/superpowers/plans/2026-07-31-classical-balanced-truncation-rate.md`

## Steps

1. Define the verified `alpha/8` full-transfer decay rate.
2. Prove its exact relation to the gap and contour rates.
3. Transfer the existing admissible optimizer to the verified rate.
4. Reconstruct the selected zero-free-gap endpoint with the exact rate
   equality retained.
5. Package the optimizer, positivity, gap, and selected zero-free data.
6. Add a public contract and axiom audit.
7. Run only the focused module build and audit.
8. Commit docs and code separately, push, and open a stacked draft PR.

## Constraints

- Do not claim the coarse factor eight is analytically optimal.
- Preserve the original zero-free theorem and selected-height quantifiers.
- Do not modify complementary-zero or VK-edge files.
- Stage only the five files listed above.
