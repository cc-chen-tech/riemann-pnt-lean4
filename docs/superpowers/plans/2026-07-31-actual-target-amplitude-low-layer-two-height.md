# Actual target-amplitude low-layer two-height implementation plan

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeLowLayerTwoHeight.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeLowLayerTwoHeightContract.lean`
- `Test/ZeroDensityLayerBudgetActualTargetAmplitudeLowLayerTwoHeightAxiomAudit.lean`

## Theorem chain

1. Define the low-ordinate and high-annulus filters of an actual
   outside-cluster bucket layer.
2. Prove that the two filters are disjoint and their union is the original
   positive-ordinate layer.
3. Bound the low filter's multiplicity by global zero multiplicity at
   `x ^ gamma`.
4. Bound the high filter's multiplicity by global zero multiplicity at
   `x ^ alpha`.
5. Aggregate the fixed-denominator endpoint kernel bound over the low filter.
6. Aggregate the rectangle kernel bound, including the `x ^ gamma`
   denominator, over the high filter.
7. Divide by `x ^ (beta - 1)` and identify both expressions with existing
   hybrid majorants, using endpoint `tau` for the low piece and
   `tau - gamma` for the high piece.
8. Prove both normalized pieces tend to zero under
   `gamma + tau - beta + epsilon < 0` and
   `alpha + tau - beta - gamma + epsilon < 0`.
9. Specialize to `gamma = alpha / 2` and prove existence of a
   contour-compatible `alpha > 1 - beta` whenever
   `1 / 2 < tau < (3 * beta - 1) / 2`.
10. Export the declarations through a contract and audit their axioms.

## Validation

Build only the new implementation, contract, and axiom-audit targets.  Run
the repository axiom allowlist checker for the new audit file.  Stage only
the three implementation files and the two documentation files; explicitly
exclude the frozen untracked complementary-zero file.

## PR boundary

The PR contains only the actual global low-layer two-height split and its
target-amplitude decay theorem.  The later full-tail composition belongs in
a separate stack.
