# Local cubic zero kernel + response kernel bridge: FORMALIZED

Status: **DONE** (2026-08-16, merge-test-amplification worktree).
Round 38; 0 `sorry`, axiom audits clean.

## What happened

The per-zero content of the cubic kernel line
(`actual-cubic-two-height-l2-tail`:
`ZeroDensityLayerBudgetCubicResidueSecondDifferenceKernel`,
`ZeroDensityLayerBudgetCubicKernelFactorization`,
`ZeroDensityLayerBudgetCubicKernelNearOne`) is *locally self-contained* —
it only uses `analyticOrderNatAt`, complex `cpow`/`exp` and mathlib.  It
was therefore re-derived locally (same declaration names, same namespace
`ExplicitFormulaResidues`) so the L2/L3 response machinery can proceed in
this worktree without touching the user's active line.  The explicit
formula machinery (`thirdOrderContourRemainder`, `chebyshevPsi`, the
common-pole approximants) stays on the cubic line; when that line merges,
its files supersede the local ones.

## `PrimeNumberTheorem/ZeroDensityLayerBudgetCubicKernelLocal.lean`

| declaration | content |
|---|---|
| `cubicZeroResidueSecondDifference`, `cubicPoleOneSecondDifference` | kernel definitions (logarithmic second forward difference) |
| `cubicKernelMultiplier`, `cubicSimpleZeroKernel`, `cubicKernelDifferenceQuotient` | multiplier / simple-kernel definitions |
| `ofReal_mul_exp_cpow_eq_cpow_mul_exp` | exponential translation of cpow |
| `cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier` | exact `/h²` factorization |
| `norm_cubicSimpleZeroKernel_eq` | `‖kernel‖ = m · x^(Re rho) / ‖rho‖` |
| `norm_cubicZeroResidueSecondDifference_div_sq_eq` | same, times `‖multiplier‖` |
| `cubicPoleOneSecondDifference_div_sq_eq` | pole-at-one real factorization |
| `norm_cubicKernelDifferenceQuotient_sub_one_le`, `norm_cubicKernelMultiplier_sub_one_le_three_mul` | near-one Taylor bounds |
| `norm_multiplier_bounds_of_sub_one_le`, `norm_cubicZeroResidueSecondDifference_correctScale_bounds` | two-sided scale bounds |
| `exists_pos_forall_mem_norm_cubicKernelMultiplier_sub_one_lt` | uniform threshold over a finite pole set |
| **`norm_cubicKernelMultiplier_le_nine_div_sq`** | *new*: far range `‖M‖ ≤ 9/(h‖ρ‖)²` for `Re ρ ∈ [0,1]`, `h ≤ log 2` |
| **`norm_cubicKernelMultiplier_le_uniform`** | *new*: `‖M‖ ≤ max 4 (36/(h·T0/2)²)` on the top layer |

## `PrimeNumberTheorem/WindowedDetectorResponseKernel.lean`

| declaration | content |
|---|---|
| `zeroResponseKernel ρ x h γ` | `cubicZeroResidueSecondDifference ρ x h / h² · exp(−iγ log x)` |
| `norm_zeroResponseKernel_eq` | exact norm `m·x^(Re ρ)/‖ρ‖·‖M‖` (phase norm = 1) |
| `norm_zeroResponseKernel_correctScale_bounds` | two-sided `(1 ± 3h‖ρ‖)` scale bounds |
| `norm_zeroResponseKernel_le_uniform` | top-layer uniform bound `max 4 (36/(h·T0/2)²)·m·x^(Re ρ)/‖ρ‖` |

## Next

- L3-(A) instantiation: `topLayerResponseSum_le` with the real kernel —
  `KA·4·X^(λβ+β)/(T0)` times the L1 mass (the `x^(Re ρ) ≤ x` factor from
  `0 < Re ρ < 1`).
- The L2 full identity `windowedMellinResponse_eq_sum_add_error` still
  needs the truncated explicit formula (cubic line's
  `exists_cubicZeroKernelSum_chebyshevPsi_bounds`, whose residue-side
  content is now available locally).
- Gate `hbranch`/`hbranch_le`/`hlower`/`hdisjoint` follow from the L3
  windowed-detector conclusion; `hgap` and `hroots` are done.

Audit files: `Test/CubicKernelLocalAxiomAudit.lean`,
`Test/WindowedDetectorResponseKernelAxiomAudit.lean`.
