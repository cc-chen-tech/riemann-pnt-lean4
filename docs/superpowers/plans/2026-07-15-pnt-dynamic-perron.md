# PNT Dynamic Perron Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove `PNTForm3` unconditionally through the existing first-order finite-zero-sum explicit formula at a moving right endpoint.

**Architecture:** Quantify the near-one von Mangoldt series, sharpen the Tannery majorant at `c(m) = 1 + 1 / log m`, propagate the moving endpoint through the horizontal contour, and combine the resulting subpolynomial-height formula with the proved zero-free region and zero count.

**Tech Stack:** Lean 4, mathlib real and complex analysis, Dirichlet series, contour integration, repository contract tests.

## Global Constraints

- Only theorem-level analytic estimates that remove a named PNT-chain gap count as progress.
- Do not add conditional endpoint propositions or API-only wrappers.
- Keep every asymptotic constant uniform in variables quantified after it.
- Do not claim PNT until `PNTForm3` itself is proved and all verification gates pass.

---

### Task 1: Near-one von Mangoldt series bound

**Files:**
- Create: `PrimeNumberTheorem/VonMangoldtLSeriesNorm.lean`
- Modify: `PrimeNumberTheorem/RightHorizontalEdge.lean`
- Create: `Test/VonMangoldtLSeriesNormContract.lean`

- [x] Add and verify a failing contract for an explicit `O(epsilon ^ (-2))` bound.
- [x] Bound the p-series by `1 + 1 / delta` and compare `Lambda(n)` with a small power.
- [x] Prove the public near-one series theorem and pass the focused contract.
- [x] Extract the theorem into a dependency-neutral module and add the contract to `lakefile.lean`.
- [x] Run focused downstream builds.

### Task 2: Dynamic-line Perron error

**Files:**
- Modify: `PrimeNumberTheorem/FirstOrderLSeriesPerron.lean`
- Create: `Test/DynamicNaturalPerronContract.lean`

- [x] Add a failing contract with the constant quantified before `m` and `T`.
- [x] Prove moving-abscissa positivity and `m ^ c(m) = exp 1 * m`.
- [x] Split the Tannery sum below, at, and above the jump.
- [x] Retain reciprocal integer distance and sum it with harmonic bounds.
- [x] Use Task 1 for the tail and prove the uniform `m log^2(m) / T` Perron theorem.
- [x] Build focused modules.

### Task 3: Dynamic complete horizontal contour

**Files:**
- Modify: `PrimeNumberTheorem/CentralHorizontalEdge.lean`
- Modify: `PrimeNumberTheorem/CofinalExplicitFormula.lean`
- Create: `Test/DynamicHorizontalContourContract.lean`

- [x] Add a failing contract whose horizontal factor is `m * polylog(m,T)`, not `m ^ 2`.
- [x] Generalize the right endpoint from `2` to `c(m)` while retaining `x ^ sigma <= x ^ c(m)`.
- [x] Apply Task 1 on the short right-of-one segment.
- [x] Reassemble central and far-left horizontal pieces at a selected good height.
- [x] Prove the dynamic truncated explicit formula and commit.

### Task 4: Zero-free-region finite zero sum

**Files:**
- Create: `PrimeNumberTheorem/PNTFiniteZeroSum.lean`
- Create: `Test/PNTFiniteZeroSumContract.lean`

- [ ] Add a failing contract for the unconditional finite zero-sum bound.
- [ ] Combine the high-height classical zero-free region with a compact low-height width.
- [ ] Apply the reciprocal multiplicity bound from `GlobalZeroCount`.
- [ ] Choose height `exp (sqrt (b * log m))` and prove every explicit-formula error is `o(m)`.
- [ ] Commit the zero-sum and natural-sample asymptotic.

### Task 5: Unconditional PNT

**Files:**
- Create: `PrimeNumberTheorem/PNTFromDynamicPerron.lean`
- Modify: `PrimeNumberTheorem.lean`
- Create: `Test/PNTFromDynamicPerronContract.lean`

- [ ] Add a failing contract for unconditional `PNTForm3`.
- [ ] Transfer the natural-sample estimate to real inputs using the floor identities.
- [ ] Prove `PNTForm3`, then invoke existing bridges for `PNTForm1` and `PNTForm2`.
- [ ] Update inventory, proof-chain documents, and the axiom audit.
- [ ] Run full build and all repository verification gates before integration.
