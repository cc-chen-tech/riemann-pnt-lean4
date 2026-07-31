# Zero-Free Envelope for the Running Boundary Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Dominate the canonical running boundary by a monotone zero-free envelope and derive actual PNT decay from the effective gap.

**Architecture:** Pointwise Finset maximum domination feeds a recursive running-maximum induction. An order comparison transfers effective-gap divergence to the Stack 117 log-gap.

**Tech Stack:** Lean 4, Finset maxima, order filters, Stack 117.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*`, matching contract/audit files, and task documents.
- Use the effective gap `min(1-beta0,gap)`.
- Keep signed witnesses explicit.
- Do not touch protected complementary-bound or Sharp/VK-edge files.
- Do not claim unconditional Omega or RH.

---

### Task 1: Envelope domination

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryZeroFreeEnvelopeTransfer.lean`

**Interfaces:**
- Produces: visible zero-free envelope predicate, effective gap, pointwise bottleneck domination, and recursive running-boundary domination.

- [ ] Define the envelope and effective gap.
- [ ] Bound the inserted-zero Finset maximum by `max beta0 (1-gap(m))`.
- [ ] Prove recursive running-boundary domination using antitonicity.

### Task 2: Log-gap and actual transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryZeroFreeEnvelopeTransfer.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryZeroFreeEnvelopeTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryZeroFreeEnvelopeTransferAxiomAudit.lean`

**Interfaces:**
- Produces: effective-gap-to-zero-free-decay theorem and sigma-only actual PNT decay/signed-Omega facade.

- [ ] Compare the effective gap with `1-runningBoundary(m)`.
- [ ] Transfer divergence by eventual order domination.
- [ ] Apply Stack 117 to the sigma-only canonical boundary.
- [ ] Add contract and axiom audit targets.
- [ ] Compile, commit, push, and open a draft PR based on Stack 117.
