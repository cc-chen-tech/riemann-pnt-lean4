# L2 windowed Mellin response identity: FORMALIZED (input-parametrized)

Status: **DONE** (2026-08-16, merge-test-amplification worktree).
Round 40; 0 `sorry`, axiom audits clean (`propext`, `Classical.choice`,
`Quot.sound` only; the truncated explicit formula itself remains the
explicit input `hexplicit`).

## `PrimeNumberTheorem/WindowedMellinResponseIdentity.lean`

| declaration | statement |
|---|---|
| `centeredSecondDifferencePsi x h` | the centered second forward difference of `chebyshevPsi` at log-scale `h`, normalized by `h²` |
| `windowedResponse X lam h γ` | `∫_X^{X^lam} centeredSecondDifferencePsi x h · x^(−1−iγ) dx` |
| `zeroResponseCoeff ρ h` | the per-zero response coefficient `−m(ρ)/ρ · cubicKernelMultiplier ρ h` |
| `windowedIntegral_cubicKernel_eq_response` | `∫ kernel(ρ,x,h)/h² · x^(−1−iγ) dx = zeroResponseCoeff ρ h · integralFactor ρ X lam γ` (via the round-38 factorization + the round-35 complex FTC) |
| **`windowedMellinResponse_eq_sum_add_error`** | **L2 MAIN**: under `hexplicit` (the pointwise truncated cubic explicit formula) and `herr` (`‖Err x‖ ≤ C x^(1−1/20)`), eventually in `X`: `‖windowedResponse − Σ_ρ zeroResponseCoeff ρ h · integralFactor ρ X lam γ‖ ≤ C' X^(lam(1−1/20))` |

## Correction vs. the draft

The draft's per-zero term `zeroResponseKernel ρ X h γ · integralFactor` has
the base `X^ρ · exp(−iγ log X)` baked into the kernel while the windowed
integral already carries it; the honest coefficient form is
`zeroResponseCoeff ρ h · integralFactor` (`zeroResponseCoeff = −m/ρ · M`),
which is exactly what the windowed integral produces.

## Remaining

1. Discharge `hexplicit`/`herr`: the cubic line's
   `exists_cubicZeroKernelSum_chebyshevPsi_bounds` + the contour-remainder
   bound (the residue-side content is locally available since round 38;
   only the contour remainder stays on the cubic line).
2. L3 windowed-detector conclusion per top-layer window (`hnoZero`
   contradiction via `topAndComplementaryResponse_lt_seedScale`,
   round 39) → gate inputs `hbranch`/`hbranch_le`/`hlower`/`hdisjoint`.
3. Gate instantiation + terminal theorem
   (`no_nontrivial_zero_re_gt_two_thirds_of_gateInputs`, round 37).

Audit file: `Test/WindowedMellinResponseIdentityAxiomAudit.lean`.
