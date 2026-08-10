# Classical Dyadic Carlson Gap Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct one explicit moving width that simultaneously satisfies
the automatic dyadic Carlson margin and the proved classical zero-free region
at the repository's subpolynomial selected good height.

**Architecture:** A focused production module first proves the asymptotic
dyadic margin for `rate / (1 + sqrt(log m))`. A second theorem adapts the
classical truncation right edge to the same width and selected height. A final
existence theorem chooses the admissibly balanced constants.

**Tech Stack:** Lean 4, Mathlib filters and real logarithms, existing
`ZeroDensityLayerBudgetActualDyadicCarlsonSelectedHeightPNT`,
`ZeroDensityLayerBudgetClassicalAdmissibleGoodHeight`, and
`ZeroDensityLayerBudgetClassicalAdmissibleFiniteZeroDecay`.

## Global Constraints

- Only create `ZeroDensityLayerBudgetActualClassicalDyadicCarlsonGap*`.
- Never modify `ZeroForcedOscillationComplementaryBound.lean`.
- Never modify VK-edge modules.
- Preserve the selected-good-height boundary.
- Accepted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

---

### Task 1: Exact dynamic width and Carlson margin

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonGap.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonGapContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonGapAxiomAudit.lean`

**Interfaces:**
- Consumes: `pntSqrtLog`
- Consumes: `IsCarlsonMovingDyadicLogPowerGap`
- Produces: `classicalAdmissibleDyadicCarlsonGapWidth`
- Produces: `isCarlsonMovingDyadicLogPowerGap_classicalAdmissible`

- [ ] Define `delta(m) = rate / (1 + pntSqrtLog m)`.
- [ ] Prove global positivity for `rate > 0`.
- [ ] Prove eventual `delta(m) <= 1 / 8`.
- [ ] Bound the positive exponent term below by a fixed positive multiple of
      `pntSqrtLog m`.
- [ ] Bound all reciprocal-gap and `log log` costs by
      `O(log(pntSqrtLog m))`.
- [ ] Use `Real.isLittleO_log_id_atTop` to prove the exact gap expression
      tends to positive infinity.

### Task 2: Classical selected-height zero-free adapter

**Interfaces:**
- Consumes: `dynamicHeight_classicalZeroFreeWidth_ge`
- Consumes: `eventually_selectedClassicalAdmissibleGoodHeight_mem`
- Produces:
  `isSelectedHeightDynamicZeroFree_selectedClassicalAdmissible`

- [ ] Transfer the selected height upper bound to
      `T <= exp(alpha * pntSqrtLog m)`.
- [ ] Apply the strict margin `rate * alpha < b`.
- [ ] Insert each visible nontrivial zero into `nontrivialZerosFinset T`.
- [ ] Compare `delta(m)` with the classical width `b / log(T + 6)`.

### Task 3: Canonical existence theorem and audits

**Interfaces:**
- Consumes: `exists_classicalTruncationRightEdge_nontrivialZerosFinset`
- Consumes: `classicalAdmissibleBalancedRate_le_zeroFreeRate`
- Produces:
  `exists_selectedClassicalAdmissibleDyadicCarlsonZeroFreeGap`

- [ ] Choose `alpha = classicalAdmissibleBalancedRate b`.
- [ ] Choose `rate = alpha / 2`.
- [ ] Prove `rate * alpha < b`.
- [ ] Assemble the Carlson-gap and selected-height zero-free conclusions.
- [ ] Register every public declaration in the exact contract.
- [ ] Print axioms for the two endpoint theorems.
