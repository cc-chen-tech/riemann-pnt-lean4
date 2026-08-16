# L3 threshold assembly + real-kernel (A) instantiation: FORMALIZED

Status: **DONE** (2026-08-16, merge-test-amplification worktree).
Round 39; 0 `sorry`, axiom audits clean.

## `PrimeNumberTheorem/WindowedMellinL3.lean` — two new theorems

| declaration | statement |
|---|---|
| **`topLayerResponseSum_le_of_kernel`** | the top-layer (outside-window) response sum with the *real* kernel `zeroResponseKernel` is `≤ max 4 (36/(h·T0/2)²) · 4 · X^(λβ+β) / T0 · Mass` — kernel norm bound (`norm_zeroResponseKernel_le_uniform`), `1/‖ρ‖ ≤ 2/T0`, `X^β ≤ X`, the L2 integral bound, and the `m ≥ 1` multiplicity step |
| **`topAndComplementaryResponse_lt_seedScale`** | L3 threshold assembly: `A + B < X^(λβ+β)/(2β(T0+H))` from the two per-layer bounds and the two strict exponent budgets `KA·4·MassA/T0 < 1/(4β(T0+H))` and `KA·4·X^((λ+1)(β−gap))/T0·MassB < X^(λβ+β)/(4β(T0+H))` |

The two budgets are exactly the conditions the gate instantiation
discharges: the B-budget via `AmplificationGateExponentBudget`
(round 36, `4σ(1−σ) < h'·depth`-type comparison) and the A-budget via
the parameter choice `γ₀h' > 2d` (window growth beats the smoothing
decay), per `windowed-detector-L3-threshold.md`.

## Remaining

1. L2 full identity `windowedMellinResponse_eq_sum_add_error` — needs the
   truncated explicit formula (`exists_cubicZeroKernelSum_chebyshevPsi_bounds`
   on the cubic line; its residue-side content is locally available since
   round 38).
2. L3 windowed-detector conclusion per top-layer window (the
   `hbranch`/`hbranch_le`/`hlower`/`hdisjoint` gate inputs): instantiate
   `topAndComplementaryResponse_lt_seedScale` inside each window and turn
   the response domination into the existence of a top-layer zero
   (`hnoZero` contradiction).
3. Gate instantiation and the terminal theorem
   (`no_nontrivial_zero_re_gt_two_thirds_of_gateInputs`, round 37) then
   close with AxiomAudit at zero.
