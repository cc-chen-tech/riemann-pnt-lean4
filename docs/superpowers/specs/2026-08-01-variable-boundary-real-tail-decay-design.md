# Variable-Boundary Real-Tail Decay Design

## Goal

Discharge stack105's real-ordinate tail input automatically from a fixed
strict real-part gap below an eventual lower bound for the moving exponent.

## Method

The set of real-ordinate nontrivial zeros is finite. For a fixed `beta0`, each
term with `rho.re < beta0` satisfies

```text
norm(kernel rho at m) / m^(beta0 - 1) -> 0.
```

Summing gives a fixed finite majorant tending to zero. At natural points with
`beta0 <= beta(m)`, stack103's real-power monotonicity makes the moving target
amplitude at least the fixed one. Removing moving-package members can only
decrease the real-ordinate norm majorant, so the actual moving real tail is
squeezed to zero.

## Public outputs

- `variableBoundaryRealOrdinateFixedMajorant`
- `variableBoundaryRealOrdinateFixedMajorant_tendsto_zero`
- `variableBoundaryRealNormalizedSum_le_fixedMajorant`
- `variableBoundaryRealNormalizedSum_tendsto_zero_of_fixed_gap`
- a stack105 residual corollary with the real-tail input discharged

## Claim boundary

The strict fixed real gap is an explicit hypothesis. This stack does not
discharge the low positive strip, the positive Finset-to-Carlson-index bridge,
the moving main witness, both signs, or RH.
