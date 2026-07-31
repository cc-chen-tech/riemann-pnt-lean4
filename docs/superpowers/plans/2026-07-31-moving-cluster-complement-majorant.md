# Moving-Cluster Complement Majorant Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove target-amplitude negligibility of the actual signed complement outside the moving right-edge exceptional cluster.

**Architecture:** Dominate every moving low layer by the empty-cluster polynomial-envelope two-height mass, dominate every moving high layer by one actual Carlson strip, and then use pointwise conjugation plus real-ordinate capture to control the full signed complement.

**Tech Stack:** Lean 4, actual Carlson two-height mass bounds, moving exceptional clusters, multiplicity-aware explicit formula.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualMovingClusterComplementMajorant*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the moving visible-cluster witness outside this module.

---

### Task 1: Uniform moving positive-tail majorant

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingClusterComplementMajorant.lean`

**Interfaces:**
- Produces: moving-layer subset, low-layer majorant, high-strip subset, pointwise positive-tail bound, and moving positive-tail negligibility.

- [x] **Step 1: embed every moving selected layer in the empty-cluster polynomial layer**

- [x] **Step 2: derive the empty-cluster low two-height mass bound**

- [x] **Step 3: embed the moving high layer in the actual Carlson strip**

- [x] **Step 4: combine the fixed empty-cluster and strip limits**

### Task 2: Full signed moving complement

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingClusterComplementMajorant.lean`

**Interfaces:**
- Produces: zero real-ordinate moving tail, moving full-tail negligibility, and moving signed-complement negligibility.

- [x] **Step 1: prove the adjoined real-ordinate tail is zero**

- [x] **Step 2: apply pointwise conjugation to bound the full tail**

- [x] **Step 3: dominate the signed complement by the full norm**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingClusterComplementMajorantContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualMovingClusterComplementMajorantAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [x] **Step 3: commit documentation and code separately**

- [x] **Step 4: push and create a draft PR based on stack78**
