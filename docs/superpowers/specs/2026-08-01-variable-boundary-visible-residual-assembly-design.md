# Variable-Boundary Visible Residual Assembly Design

## Goal

Assemble the moving Carlson visible-tail decay and fixed-exponent analytic
remainder estimates into the exact variable-boundary explicit-formula
residual used by the PNT oscillation transfer.

## Missing bridge made explicit

The stack101 tail is a nonnegative infinite sum over visible positive Carlson
zero indices. The explicit formula uses the finite signed complement outside
the moving equal-real-part package. Their connection is isolated as
`VariableBoundaryVisibleComplementMajorized sigma H beta`:

```text
|moving package complement at m| / moving target amplitude at m
  <= visible normalized Carlson tail at m
```

eventually. This is the precise finite-sum/indexing bridge still requiring a
separate proof; it is not hidden inside an analytic certificate.

## Theorem chain

1. Stack101 gives convergence of the visible normalized tail under the
   indexed visible-right-edge and absorption-or-gap hypotheses.
2. The majorization bridge and eventual positivity squeeze the actual moving
   package complement to zero at the moving target amplitude.
3. Stack103 promotes the fixed-`beta0` closed real-axis and contour remainder
   estimates whenever `beta0 <= beta(m)` eventually.
4. Stack100's exact explicit-formula decomposition identifies the sum of
   these three remainders with the relative PNT error minus the moving package
   main term.

## Files

- `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryVisibleResidualAssembly.lean`
- `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryVisibleResidualAssemblyContract.lean`
- `Test/ZeroDensityLayerBudgetVariableBoundaryVisibleResidualAssemblyAxiomAudit.lean`

## Claim boundary

The assembly is conditional only on the explicit pointwise majorization
bridge and the already stated Carlson/contour inputs. It does not prove that
bridge automatically, construct a moving main-term witness, establish both
oscillation signs, or imply RH.

## Verification

Compile implementation, contract, and audit sequentially with one Lean
process and the established overlay. The expected axiom set is `propext`,
`Classical.choice`, and `Quot.sound`.
