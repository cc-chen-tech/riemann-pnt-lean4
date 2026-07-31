# Weighted Optimal Polynomial-Height Window Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove and audit the minimax polynomial-height allocation for every nonnegative density slope `q`.

**Architecture:** A focused Lean module first proves the weighted four-constraint arithmetic optimizer, then specializes it at `q = 1`, and finally feeds its strict window into the existing selected-height and explicit-formula remainder interfaces. Separate contract and axiom-audit modules lock the public surface and logical boundary.

**Tech Stack:** Lean 4, Mathlib real arithmetic, the existing PrimeNumberTheorem selected-height and remainder-certificate modules.

## Global Constraints

- Modify only `ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindow*.lean` and this stack's spec/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`, Sharp/localized-pi-over-two modules, or VK-edge modules.
- Keep `q >= 0` explicit and require a strictly positive weighted feasibility gap.
- Do not claim a formalized external density estimate, RH, or an unconditional Omega theorem.
- Compile serially with `nice -n 10` and the existing overlay.

---

### Task 1: Lock the weighted minimax arithmetic interface

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindow.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindowContract.lean`

**Interfaces:**
- Consumes: `optimalPolynomialHeightSafetyMargin`, `optimalPolynomialHeightInnerExponent`, `optimalPolynomialHeightOuterExponent`, and `optimalPolynomialHeightEpsilon`.
- Produces: `weightedPolynomialHeightCommonSafetyMargin_le_optimal`, `weightedOptimalPolynomialHeightWindow_equalMargins`, and `weightedOptimalPolynomialHeight_q_one`.

- [ ] **Step 1: State the public contract checks for the weighted definitions and theorem chain.**

- [ ] **Step 2: Compile the contract before the implementation target and confirm that the missing declarations reject the contract.**

Run:

```bash
nice -n 10 lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindowContract.lean
```

Expected: failure because the new public module or declarations are absent.

- [ ] **Step 3: Implement the feasibility gap, optimizer definitions, upper bound, attainment theorem, and `q = 1` recovery.**

- [ ] **Step 4: Compile the implementation and contract serially.**

Run:

```bash
nice -n 10 lake env lean -o "$OVERLAY/PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindow.olean" PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindow.lean
nice -n 10 lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindowContract.lean
```

Expected: both commands exit zero.

### Task 2: Connect the optimizer to actual selected heights

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindow.lean`

**Interfaces:**
- Consumes: `eventually_selectedUniformGoodHeight_le_polynomialHeight`, `selectedUniformGoodHeight_tendsto_atTop`, and `selectedUniformGoodHeight_actualNaturalRemainderCertificate`.
- Produces: `weightedOptimalPolynomialHeightWindow_spec` and `weightedOptimalPolynomialSelectedHeight_spec`.

- [ ] **Step 1: State strict positivity, exponent ordering, density slack, inner-exponent cap, and exact-budget conclusions.**

- [ ] **Step 2: Prove the arithmetic specification from `q >= 0`, `0 < beta < 1`, `0 < sigma`, and `0 < W`.**

- [ ] **Step 3: Instantiate the existing selected-height growth and actual natural-point remainder certificate.**

- [ ] **Step 4: Recompile the implementation and contract serially.**

Expected: both commands exit zero with no warnings.

### Task 3: Audit and publish Stack147

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindowAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-08-01-weighted-optimal-polynomial-height-window-design.md`
- Create: `docs/superpowers/plans/2026-08-01-weighted-optimal-polynomial-height-window.md`

**Interfaces:**
- Consumes: all public Stack147 theorems.
- Produces: a direct axiom report and a bounded stacked PR based on Stack146.

- [ ] **Step 1: Compile the axiom-audit target against the implementation overlay.**

Run:

```bash
nice -n 10 lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetWeightedOptimalPolynomialHeightWindowAxiomAudit.lean
```

Expected: exit zero; each theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 2: Commit the design documents separately from the Lean implementation.**

- [ ] **Step 3: Stage only the three Stack147 Lean files, commit, push, and open a draft PR based on Stack146.**
