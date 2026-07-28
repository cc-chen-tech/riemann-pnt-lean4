# VK-edge Zero-Cluster Local L2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove an explicit local second-moment lower bound for a finite zeta-zero cluster in which near-frequency interactions are measured by the Carneiro--Littmann local-separation energy.

**Architecture:** First add a generic Hilbert lower bound for drifting exponential polynomials. Then specialize it to the merged zeta-zero coefficients and insert the equal-ordinate phase-coercivity estimate. Keep all unresolved spectral interaction visible in one local-separation energy term.

**Tech Stack:** Lean 4, Mathlib complex analysis, finite sums, interval integrals, Carneiro--Littmann Hilbert inequality.

## Global Constraints

- Work only on `research/vk-edge-cluster-local-l2`, based on commit `5d71807`.
- Do not modify `main` or unrelated worktrees.
- Do not claim a real explicit-formula cluster theorem, a zero-density contradiction, or RH.
- Every new public theorem must have an exact contract and central axiom registration.
- New source must contain no `sorry`, `admit`, or project-defined `axiom`.

---

### Task 1: Generic drifting Hilbert lower bound

**Files:**
- Create: `MathlibAux/DriftingExponentialPolynomialHilbert.lean`
- Create: `Test/DriftingExponentialPolynomialHilbertContract.lean`
- Create: `Test/DriftingExponentialPolynomialHilbertAxiomAudit.lean`

**Interfaces:**
- Consumes: `MathlibAux.driftingExponentialPolynomial`, `MathlibAux.mergedFrequencySupport`, `MathlibAux.mergedFrequencyCoefficient`, and `PrimeNumberTheorem.DirichletPolynomial.hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann`.
- Produces: a frozen mean-square error theorem and a merged drifting lower bound with the exact `4 * Real.pi` local-separation penalty.

- [x] **Step 1: Write exact failing contracts for the frozen and drifting Hilbert bounds.**
- [x] **Step 2: Run the focused contract build and confirm the identifiers are missing.**
- [x] **Step 3: Implement the frozen mean-square estimate from the exact Hilbert identity.**
- [x] **Step 4: Implement the drift transfer and merged-frequency specialization.**
- [x] **Step 5: Run the focused build and axiom audit.**

### Task 2: Zeta zero-cluster local L2 endpoint

**Files:**
- Create: `PrimeNumberTheorem/VKEdgeZeroClusterLocalL2.lean`
- Create: `Test/VKEdgeZeroClusterLocalL2Contract.lean`
- Create: `Test/VKEdgeZeroClusterLocalL2AxiomAudit.lean`

**Interfaces:**
- Consumes: Task 1 and `totalCoefficientMass_sq_le_four_card_mul_mergedFrequencyEnergy`.
- Produces: a quantitative finite-zero-cluster local `L2` lower bound and a strict positivity theorem with every drift and local-separation loss displayed.

- [x] **Step 1: Write exact failing contracts for the quantitative and positive endpoints.**
- [x] **Step 2: Run the focused contract build and confirm the identifiers are missing.**
- [x] **Step 3: Insert the phase-coercivity energy lower bound into Task 1.**
- [x] **Step 4: Derive the strict positivity endpoint.**
- [x] **Step 5: Run the focused build and axiom audit.**

### Task 3: Repository integration and verification

**Files:**
- Modify: `lakefile.lean`
- Modify: `Test/MultiplicityAxiomAudit.lean`
- Modify: `scripts/check_axiom_allowlist.py`

**Interfaces:**
- Consumes: all public theorems from Tasks 1 and 2.
- Produces: repository-wide build roots and auditable theorem registration.

- [x] **Step 1: Register modules and every public theorem.**
- [x] **Step 2: Run focused builds and `python3 scripts/check_axiom_allowlist.py`.**
- [x] **Step 3: Run placeholder and whitespace scans.**
- [x] **Step 4: Run `./scripts/verify-baseline.sh` and the full `lake build`.**
- [x] **Step 5: Commit, push, and create a stacked Draft PR against `research/vk-edge-cluster-phase-coercivity`.**
