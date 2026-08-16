# Gate `hgap` exponent budget: FORMALIZED

Status: **DONE** (2026-08-16, merge-test-amplification worktree).

`PrimeNumberTheorem/AmplificationGateExponentBudget.lean` — 0 `sorry`,
axiom audit clean (`propext`, `Classical.choice`, `Quot.sound` only;
`Test/AmplificationGateExponentBudgetAxiomAudit.lean`).

| declaration | statement |
|---|---|
| `ExceptionalZeroAmplificationGate.tendsto_powerGrowth_sub_carlsonMajorant_atTop` | for `0 < σ < 1`, `0 ≤ C`, `0 ≤ H`, `4σ(1−σ) < qexp`: `T^qexp − C·‖(T+H)^(4σ(1−σ))·(log(T+H))^4‖ → ∞` |
| `ExceptionalZeroAmplificationGate.tendsto_qPower_sub_carlsonMajorant_atTop` | gate-shaped: `q : ℝ → ℕ` with eventual `T^h' ≤ q T` and `4σ(1−σ) < h'·depth` gives `cl·(q T)^depth − C·‖(T+H)^(4σ(1−σ))·(log(T+H))^4‖ → ∞` for any `cl > 0` |

Mechanism: the subpolynomial bound
`isLittleO_log_rpow_rpow_atTop` (`(log x)^4 = o(x^(4ε))`, uniform constant 1
via `IsLittleO.bound`) absorbs the `log⁴`; the remaining comparison is
pure rpow arithmetic with `ε = (qexp − 4σ(1−σ))/8`.

## Where this plugs into the gate

`ExceptionalZeroAmplificationGateContract.amplificationGate` takes
`hgap : Tendsto (fun T => localContribution·(q T)^depth − C·‖(T+H)^(4σ(1−σ))·(log(T+H))^4‖) atTop atTop`.
The second theorem supplies `hgap` for any `q T` with power growth
`T^h' ≤ q T` (e.g. `q T = ⌊T^h'⌋` from the window count `H/(2δ)`) and
`h'·depth > 4σ(1−σ)` (feasible: `σ ∈ (1/2,1)` has `4σ(1−σ) < 1`, take
`h' = 0.6`, `depth = 2` per `gate-windowed-detector-instantiation.md`).

Remaining gate inputs: `hroots`, `hbranch`, `hdisjoint`, `hbranch_le`,
`hlower` — these need the L3 windowed-detector conclusion (L2 full
identity + L3-(A) with the cubic kernel multiplier on the
`actual-cubic-two-height-l2-tail` line).
