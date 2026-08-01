# VK-Edge Sharp Low-Height Energy Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove a cofinal genuine-zeta Gaussian energy lower bound at an independently parameterized low detector height for one fixed off-line zero with real part greater than `2 / 3`.

**Architecture:** Generalize the existing normalized proportional-window remainder estimate from the hard-coded height exponent `1 / 2` to `gammaLow`. Then reuse the existing true empty-cluster residual lower bound and full-complement transfer, while proving separately that the selected low height lies below the outer height `exp (alpha * a)`.

**Tech Stack:** Lean 4, Mathlib filters and asymptotics, the repository's real-height explicit formula, Gaussian energy, contract, and axiom-audit infrastructure.

## Global Constraints

- Work only on the Sharp lower-bound side.
- Do not modify Carlson, finite-set growth, witness extraction, or final integration.
- The finite sum must be the repository's actual zeta-zero complement contribution.
- Keep `alpha` and `gammaLow` as distinct parameters.
- Run at most one Lean process globally and set `LEAN_NUM_THREADS=1`.

---

### Task 1: Generalized low-height normalized remainder

**Files:**
- Create: `PrimeNumberTheorem/ExplicitFormulaNormalizedPowerHeightWindowRemainder.lean`
- Create: `Test/ExplicitFormulaNormalizedPowerHeightWindowRemainderContract.lean`

**Interfaces:**
- Consumes: `exists_uniform_goodHeight_Icc_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le`.
- Produces: `eventually_exists_uniform_goodHeight_normalized_powerHeight_proportional_window_remainder_lt`.

- [x] Write the exact `#check` contract before the source module exists.
- [x] Run the contract and confirm it fails because the new module is absent.
- [x] Implement the power-height envelope, pointwise estimate, decay theorem, and selector.
- [x] Run the source and contract with `LEAN_NUM_THREADS=1`.
- [x] Commit the independently reviewable analytic selector.

### Task 2: Empty-cluster cofinal low-height energy

**Files:**
- Create: `PrimeNumberTheorem/VKEdgeSharpLowHeightEnergy.lean`
- Create: `Test/VKEdgeSharpLowHeightEnergyContract.lean`

**Interfaces:**
- Consumes: the Task 1 selector, `exists_eventually_emptyClusterResidualForwardGaussianSecondMoment_gt`, and `dynamicComplementFullMovingGaussianSecondMoment_ge_of_normalizedRemainder`.
- Produces: `exists_eventually_emptyClusterLowHeightFullMovingGaussianSecondMoment_gt` and the literal genuine-zeta integral endpoint `exists_eventually_emptyClusterLowHeightNormalizedComplementSecondMoment_gt`.

- [x] Write the exact endpoint contract before the source module exists.
- [x] Run the contract and confirm it fails because the new module is absent.
- [x] Prove eventual containment of the selected low-height interval below `exp (alpha * a)`.
- [x] Transfer the true residual lower bound to actual finite-zero complement energy.
- [x] Rewrite the internal full-bucket energy as the literal Gaussian integral of the genuine finite zeta-zero complement.
- [x] Run the source and contract with `LEAN_NUM_THREADS=1`.
- [x] Commit the genuine-zeta `S = empty` endpoint.

### Task 3: Audit and finite-S boundary

**Files:**
- Create: `Test/ExplicitFormulaNormalizedPowerHeightWindowRemainderAxiomAudit.lean`
- Create: `Test/VKEdgeSharpLowHeightEnergyAxiomAudit.lean`
- Modify: the central axiom allowlist and import audit files required by repository convention.
- Create: `docs/research/vk-edge-sharp-low-height-energy-boundary.md`

**Interfaces:**
- Consumes: the two public endpoints.
- Produces: checked axiom declarations and a precise statement of the missing arbitrary-`S` analytic input.

- [x] Add dedicated `#print axioms` audit files and exact central allowlist entries.
- [x] Run focused source, exact contracts, and dedicated audits serially.
- [x] Re-run the central audit with the literal integral endpoint.
- [ ] Complete the full multi-module allowlist parse when a shared build slot is available; the new declarations already pass both dedicated and central audits.
- [x] Record that deleting the anchor pair blocks an arbitrary-`S` transfer and state the minimal genuine-zeta replacement input.
- [x] Run the bounded target-inventory, chain-gap, placeholder, Python syntax, and diff checks without starting a no-target full build.
- [ ] Commit, push, and open a bounded Draft PR.
