# L3 coefficient-form bounds: FORMALIZED

Status: **DONE** (2026-08-16, merge-test-amplification worktree).
Round 41; 0 `sorry`, axiom audits clean.

## `PrimeNumberTheorem/WindowedMellinL3.lean` — two new theorems

The L2 response identity (round 40) produces per-zero terms of the form
`zeroResponseCoeff ρ h · integralFactor ρ X lam γ` (coefficient form,
*without* the base `X^ρ` factor).  The round-39 kernel-form bounds carry
an `X^β` that cancels; these two theorems restate the bounds in the
coefficient form directly:

| declaration | statement |
|---|---|
| **`topLayerCoeffResponseSum_le`** | `Σ_top ‖coeff ρ h · I ρ‖ ≤ KA·4·X^(λβ)/T0·Mass` (`KA = max 4 (36/(h·T0/2)²)`, kernel multiplier bound `norm_cubicKernelMultiplier_le_uniform`, `1/‖ρ‖ ≤ 2/T0`) |
| **`complementaryCoeffResponseSum_le`** | `Σ_comp ‖coeff ρ h · I ρ‖ ≤ KA·4·X^(λ(β−gap))/T0·Mass` (exponent fold `ρ.re ≤ β−gap`) |

Also moved `zeroResponseCoeff` to `WindowedDetectorResponseKernel.lean`
(alongside `zeroResponseKernel`, no import cycle).

## Next (the L3 capstone)

`windowedDetector_contradicts_noTopLayerZero`: under `hnoZero` (no
top-layer zero in `[T0, T0+H]`), the truncated explicit formula, the two
coefficient bounds above, the windowed error budget and the seed-signal
excess (the vk-edge oscillation witness), the response inequality
contradicts itself — hence the L3 windowed-detector conclusion and the
gate's `hbranch`/`hbranch_le`/`hlower`/`hdisjoint` inputs.
