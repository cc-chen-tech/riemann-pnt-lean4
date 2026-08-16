# L3-(A) top-layer sums + gate instantiation skeleton: FORMALIZED

Status: **DONE** (2026-08-16, merge-test-amplification worktree).
Round 37 additions; both modules 0 `sorry`, axiom audits clean.

## `PrimeNumberTheorem/WindowedMellinL3.lean` — two new theorems

| declaration | statement |
|---|---|
| `topLayerMass_le` | the top-layer (outside-window) frequency-weighted mass `Σ m(ρ)/|γ−Im ρ|` is `≤ (1/η)·Cg·(T0+H)·(1+log(T0+H+6))`, from the η-avoidance (`η ≤ |γ−Im ρ|`) and `globalZeroMultiplicity` |
| `topLayerResponseSum_le` | the top-layer response sum with kernel factor `C_h : ℂ → ℂ` (as an explicit parameter) under `‖C_h ρ‖ ≤ KA` is `≤ KA·2·X^(λβ)·Mass`, from L2's `complementaryResponse_le` and `m(ρ) ≥ 1` |

Together with round-35's `complementaryResponseSum_le` /
`complementaryResponseSum_lt_seedResponse`, the full L3 summation (A + B
vs seed) is formalized modulo the kernel-multiplier bound — which is
exactly what the cubic line's
`norm_cubicKernelMultiplier_sub_one_le_three_mul` supplies (`KA = 4`).

## `PrimeNumberTheorem/ExceptionalZeroAmplificationGateInstantiation.lean`

| declaration | statement |
|---|---|
| `seedRoots ρ₀` | the seed layer `roots T = {ρ₀}` |
| `seedRoots_eventually_nonempty` | gate input 1 (`hroots`) for the seed layer |
| **`no_nontrivial_zero_re_gt_two_thirds_of_gateInputs`** | **terminal interface**: if `AmplificationGateInputs β δ σ H depth` is supplied for every feasible tuple (`2/3 < β < 1`, `1/2 < σ < β`, `0 < δ, H`), then `∀ ρ, IsNontrivialZero ρ → ρ.re ≤ 2/3` — a counterfactual seed at `σ = (2/3+β)/2, δ = 1, H = 1, depth = 2` goes through `amplificationGate_of_inputs` to `False` |

## Remaining obligations (all on the cubic kernel line)

1. `ZeroDensityLayerBudgetCubicKernelFactorization` /
   `ZeroDensityLayerBudgetCubicKernelNearOne` (user worktree
   `actual-cubic-two-height-l2-tail`): the kernel `C_h` and its bounds —
   then `topLayerResponseSum_le` instantiates with `KA = 4`.
2. The L2 full identity `windowedMellinResponse_eq_sum_add_error`
   (truncated explicit formula + residue sum).
3. The L3 windowed-detector conclusion per top-layer window
   (`hbranch`, `hdisjoint`, `hbranch_le`, `hlower`).
4. `hgap` is already available: `AmplificationGateExponentBudget`
   (round 36) — the supplier instantiates it with `q T = ⌊T^h'⌋`,
   `h'·depth > 4σ(1−σ)`.

When 1–3 land, the terminal theorem's hypothesis is discharged and the
full `Re ρ > 2/3` exclusion closes with the audit at zero.
