# VK-Edge Prime-Side Detector Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the exact `s = 1` obstruction for nonnegative finite Dirichlet detectors and quantify the signed cancellation required to remove the main pole.

**Architecture:** A standalone real-algebra module defines the detector value and its positive/negative weighted masses. A contract locks all public signatures, an axiom audit locks dependencies, and a boundary note records why this does not yet produce a new zeta zero.

**Tech Stack:** Lean 4, Mathlib finite sums and real order algebra, repository contract and axiom-audit conventions.

## Global Constraints

- Work only in `research/vk-edge-prime-side-detector`.
- Do not modify Gate B, Pintz-Carlson, or existing Sharp modules.
- Add no axiom, `sorry`, `admit`, or unproved `Prop` interface.
- Do not claim a zeta-zero growth theorem or RH progress.
- Run at most one Lean process globally; use `LEAN_NUM_THREADS=1` for Lake.

---

### Task 1: Main-Pole Algebra

**Files:**
- Create: `PrimeNumberTheorem/PrimeSideDetectorMainPole.lean`
- Test: `Test/PrimeSideDetectorMainPoleContract.lean`

**Interfaces:**
- Consumes: `Finset`, real division, `max`, and ordered-ring lemmas from Mathlib.
- Produces: the three detector definitions and five exact public theorems listed in the design.

- [x] **Step 1: Write the exact contract**

Declare `example` type equalities for all definitions and theorem signatures,
including positivity of every support index and nontriviality of the
coefficient family on the support.

- [x] **Step 2: Run the contract and verify it fails**

Run:

```bash
lake env lean Test/PrimeSideDetectorMainPoleContract.lean
```

Expected: failure because `PrimeNumberTheorem.PrimeSideDetectorMainPole` and
its declarations do not exist.

- [x] **Step 3: Implement the minimal algebra**

Define

```lean
finiteDirichletDetectorAtOne S a := ∑ n ∈ S, a n / (n : ℝ)
positiveDirichletDetectorMassAtOne S a :=
  ∑ n ∈ S, max (a n) 0 / (n : ℝ)
negativeDirichletDetectorMassAtOne S a :=
  ∑ n ∈ S, max (-a n) 0 / (n : ℝ)
```

Prove the positive-minus-negative decomposition termwise, then derive
positivity, nonvanishing, mass balance, and existence of both coefficient
signs.

- [x] **Step 4: Run source and contract**

Run each command separately:

```bash
lake env lean PrimeNumberTheorem/PrimeSideDetectorMainPole.lean
lake env lean Test/PrimeSideDetectorMainPoleContract.lean
```

Expected: both pass.

- [x] **Step 5: Commit the algebra milestone**

```bash
git add PrimeNumberTheorem/PrimeSideDetectorMainPole.lean Test/PrimeSideDetectorMainPoleContract.lean
git commit -m "feat: formalize prime-side main-pole obstruction"
```

### Task 2: Audit and Boundary

**Files:**
- Create: `Test/PrimeSideDetectorMainPoleAxiomAudit.lean`
- Create: `docs/research/vk-edge-prime-side-detector-main-pole.md`
- Modify: `Test/MultiplicityAxiomAudit.lean`
- Modify: `lakefile.lean`
- Modify: `scripts/check_axiom_allowlist.py`

**Interfaces:**
- Consumes: all public declarations from Task 1.
- Produces: focused and central audit coverage plus an explicit mathematical claim boundary.

- [x] **Step 1: Add focused axiom checks and central registration**

Add `#print axioms` for all five public theorems, exact imports to the central
audit, a Lake target for the contract/audit pair, and allowlist entries using
the fully-qualified theorem names.

- [x] **Step 2: Write the boundary note**

Record the proved obstruction, the exact equality of positive and negative
weighted mass, and the remaining signed prime-response inequality. State
explicitly that no prescribed-zero annihilator, new zero, Carlson
contradiction, or RH theorem is proved.

- [x] **Step 3: Run focused verification serially**

After confirming no external Lean process is active, run source, contract,
and dedicated axiom audit one at a time. Expected axiom output may contain
only the repository's standard logical allowlist.

- [ ] **Step 4: Run central checks serially**

Run the central multiplicity audit with `LEAN_NUM_THREADS=1`, the Python
allowlist checker, placeholder scan, target consistency, chain-gap scan, and
`git diff --check`.

Checkpoint: the placeholder scan, target consistency, chain-gap check,
worktree target scan, and `git diff --check` pass. The central multiplicity
audit and complete allowlist command remain pending because unrelated Lean
jobs repeatedly occupied the global single-process resource window.

- [ ] **Step 5: Commit and publish a Draft PR**

```bash
git add PrimeNumberTheorem/PrimeSideDetectorMainPole.lean \
  Test/PrimeSideDetectorMainPoleContract.lean \
  Test/PrimeSideDetectorMainPoleAxiomAudit.lean \
  Test/MultiplicityAxiomAudit.lean lakefile.lean \
  scripts/check_axiom_allowlist.py \
  docs/research/vk-edge-prime-side-detector-main-pole.md \
  docs/superpowers/specs/2026-07-31-vk-edge-prime-side-detector-design.md \
  docs/superpowers/plans/2026-07-31-vk-edge-prime-side-detector.md
git commit -m "docs: audit prime-side detector boundary"
git push -u origin research/vk-edge-prime-side-detector
```

Create a stacked Draft PR with base
`research/vk-edge-right-higher-sharp-blocker`. The PR description must call
this an algebraic obstruction, not a repeatable Sharp lower bound.
