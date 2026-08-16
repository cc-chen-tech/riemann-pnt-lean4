# L2 analytic core + L3 complementary layer: FORMALIZED (kernel-free part)

Status: **DONE** (2026-08-16, merge-test-amplification worktree).

Two new modules, self-contained (import `Mathlib` and, for L3,
`ZeroFreeRegion.MeromorphicAux` only), 0 `sorry`, axiom audit clean
(`propext`, `Classical.choice`, `Quot.sound` only):

## `PrimeNumberTheorem/WindowedMellinL2.lean`

| declaration | statement |
|---|---|
| `integralFactor ρ X lam γ` | closed form `((X^lam)^(ρ-iγ) − X^(ρ-iγ)) / (ρ − iγ)` |
| `norm_cpow_ofReal_pos` | `‖x^z‖ = x^(Re z)` for `0 < x` |
| `integral_cpow_eq_integralFactor` | `∫_X^{X^lam} x^(ρ-1-iγ) dx = integralFactor ρ X lam γ` (complex-power FTC via `hasDerivAt_ofReal_cpow_const`) |
| `integral_rpow_sub_one_eq` | `∫_X^{X^lam} x^(β-1) dx = ((X^lam)^β − X^β) / β` |
| `seedResponse_aligned_lowerBound` | **L2 target**: eventually `X^(λβ)/(2β) ≤ ∫ x^(β−1)` |
| `complementaryResponse_le` | **L2 target**: `‖∫ x^(ρ−1−iγ)‖ ≤ 2 (X^lam)^(Re ρ)/|γ−Im ρ|` (hypotheses: `1 < X`, `1 < lam`, `0 ≤ Re ρ`, `ρ − iγ ≠ 0`, `γ ≠ Im ρ`) |

## `PrimeNumberTheorem/WindowedMellinL3.lean`

| declaration | statement |
|---|---|
| `complementaryResponseSum_le` | **L3-B**: `Σ_ρ ‖response(ρ)‖ ≤ 2 X^(λ(β−gap)) · Mass`, where `Mass = Σ m(ρ)/|γ−Im ρ| ≤ C (1+log(T0+H+6))² (T0+H)/H` is an explicit hypothesis (exactly the conclusion of L1's `dyadic_distance_sum_le`); uses `m(ρ) ≥ 1` from `ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero` |
| `complementaryResponseSum_lt_seedResponse` | **L3-B strict**: if `C (1+log(T0+H+6))² (T0+H)/H < X^(λ·gap)/(4β)`, then complementary response < seed response `∫ x^(β−1)` |

## Interfaces with the remaining line

- `complementaryResponse_le`'s hypotheses `ρ − iγ ≠ 0`, `γ ≠ Im ρ` are
  discharged in the L3 final assembly by the L1 avoidance property
  `η ≤ |γ − Im ρ|` (`hγavoid`) and `Re ρ > 0`.
- The per-zero kernel multiplier `C_h` (`ZeroDensityLayerBudgetCubicKernelNearOne`,
  on the `actual-cubic-two-height-l2-tail` line) multiplies `integralFactor`
  in the real detector; the theorems above are stated for the bare
  `cubicZeroResidueSecondDifference`-free integral, so the kernel line
  composes with them by a factor `K (1 + o(1))` without changing any
  exponent comparison.
- Remaining for L3: the (A) top-layer-outside sum, the full
  `windowedMellinResponse_eq_sum_add_error` identity (needs the truncated
  explicit formula from the cubic line), and the gate instantiation.

Audit files: `Test/WindowedMellinL2AxiomAudit.lean`,
`Test/WindowedMellinL3AxiomAudit.lean`.
