# Finite Zero Cluster Explicit-Formula L2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Connect PR #30's finite zero-cluster local `L2` coercivity theorem to the actual multiplicity-aware explicit formula for the standard Chebyshev error.

**Architecture:** A new focused module defines the actual complement and normalized remainder, proves the exact pointwise decomposition, establishes interval integrability, and transfers the cluster energy lower bound to the standard `psi` second moment. Contracts and axiom audits lock the public boundary.

**Tech Stack:** Lean 4, Mathlib interval integrals, the repository explicit-formula API, PR #30 zero-cluster coercivity.

## Global Constraints

- Do not add `sorry`, `admit`, or project-defined `axiom`.
- Do not replace the explicit-formula remainder by an abstract assumption.
- Do not claim an unconditional positive `psi` second moment without proving the remainder budget.
- Do not claim a zero-density contradiction or RH.

---

### Task 1: Lock The Actual Explicit-Formula Contract

**Files:**
- Create: `Test/VKEdgeZeroClusterExplicitFormulaL2Contract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `normalizedFiniteZeroClusterContribution`, `nontrivialZerosFinset`, and the multiplicity-aware explicit formula.
- Produces: exact public signatures for the normalized standard error, actual remainder, their second moments, and the local `L2` transfer.

- [x] **Step 1: Write the failing contract.**
- [x] **Step 2: Run the focused contract build and confirm the new module is missing.**

### Task 2: Prove The Exact Standard-Psi Decomposition

**Files:**
- Create: `PrimeNumberTheorem/VKEdgeZeroClusterExplicitFormulaL2.lean`

**Interfaces:**
- Consumes: the finite zero sum and `zeroPackageClosedTerms`.
- Produces: `normalizedChebyshevPsiErrorAtExponent_eq_neg_cluster_sub_remainder`.

- [x] **Step 1: Define the actual complement and standard-`psi` remainder.**
- [x] **Step 2: Prove the full finite zero sum splits over `S` and its complement.**
- [x] **Step 3: Prove the normalized pointwise identity.**
- [x] **Step 4: Run the focused contract build.**

### Task 3: Transfer Cluster Energy To The Standard Psi Moment

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeZeroClusterExplicitFormulaL2.lean`
- Create: `Test/VKEdgeZeroClusterExplicitFormulaL2AxiomAudit.lean`

**Interfaces:**
- Consumes: PR #30's local-separation and phase-coercive lower bounds.
- Produces: `normalizedChebyshevPsiErrorSecondMoment_ge_cluster_sub_remainder` and its strict positivity endpoint.

- [x] **Step 1: Prove interval integrability of the actual normalized functions.**
- [x] **Step 2: Prove the interval `L2` reverse-triangle transfer.**
- [x] **Step 3: Install the local-separation cluster lower bound.**
- [x] **Step 4: Derive the strict remainder-dominance endpoint.**
- [x] **Step 5: Run focused build, contract, and axiom audit.**

### Task 4: Repository Verification And Publication

**Files:**
- Modify: `Test/MultiplicityAxiomAudit.lean`
- Modify: `scripts/check_axiom_allowlist.py`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: every new public theorem.
- Produces: auditable repository integration and a stacked Draft PR.

- [x] **Step 1: Register public theorems in the central allowlist and audit.**
- [x] **Step 2: Scan for forbidden placeholders and run `git diff --check`.**
- [x] **Step 3: Run `./scripts/verify-baseline.sh`.**
- [x] **Step 4: Commit, push, and create a Draft PR stacked on PR #30.**
