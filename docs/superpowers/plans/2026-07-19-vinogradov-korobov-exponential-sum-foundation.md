# Vinogradov-Korobov Exponential-Sum Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Establish the discrete exponential-sum feasibility gate for the full Vinogradov-Korobov proof route, ending in a nontrivial bound for a dyadic block of `sum n^(-it)`.

**Architecture:** Adapt and audit the existing CC0 van der Corput fundamental inequality, then layer first- and second-derivative tests over it.  Specialize the resulting bound to the logarithmic phase before beginning zeta growth and zero-repulsion work.

**Tech Stack:** Lean 4.29.1, the repository's vendored Mathlib snapshot, Lake contract targets, `#print axioms`, Git worktrees.

## Global Constraints

- Preserve attribution to `rwst/lean-code` commit `d9d838819277fc2d8bd2b0ee09c773f1402a7aa6` and its CC0 dedication.
- Add no remote Lake dependency for the upstream file.
- Add no `sorry`, `admit`, project-level `axiom`, or `def ... : Prop` substitute for a required theorem.
- Keep `vinogradov_korobov_zero_free_region` classified as open until its body is proved.
- Every public milestone must compile and have a contract; final surfaces must pass the existing axiom allowlist.

---

### Task 1: Adapt And Audit The Fundamental Inequality

**Files:**
- Create: `ZeroFreeRegion/VinogradovKorobov/VanDerCorput.lean`
- Create: `Test/VinogradovKorobovVanDerCorputContract.lean`
- Create: `Test/VinogradovKorobovAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `Finset.Icc`, complex conjugation, `sq_sum_le_card_mul_sum_sq`.
- Produces: `ZeroFreeRegion.VinogradovKorobov.vanDerCorputFundamentalInequality` with the upstream explicit autocorrelation statement.

- [x] **Step 1: Add a failing contract importing the missing project module and checking the exact theorem signature.**
- [x] **Step 2: Run `lake -Kjobs=1 build Test.VinogradovKorobovVanDerCorputContract` and verify failure is `unknown module` or `unknown constant`.**
- [x] **Step 3: Adapt the attributed upstream proof into the project namespace, changing only the incompatible Mathlib import and namespace/theorem name.**
- [x] **Step 4: Add the contract and axiom-audit roots to `lakefile.lean`.**
- [x] **Step 5: Run the contract and audit targets; require only `propext`, `Classical.choice`, and `Quot.sound`.**
- [x] **Step 6: Commit as `feat(vk): add audited van der Corput inequality`.**

### Task 2: Linear Phase And Correlation Specialization

**Files:**
- Create: `ZeroFreeRegion/VinogradovKorobov/ExponentialSum.lean`
- Create: `Test/VinogradovKorobovExponentialSumContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Task 1's fundamental inequality and Mathlib complex-exponential identities.
- Produces: an interval exponential sum, a phase-difference correlation identity, the trivial length bound, and the geometric linear-phase cancellation bound.

- [x] **Step 1: Write failing contract examples for the phase-difference identity and geometric bound.**
- [x] **Step 2: Verify the contract fails before the new module exists.**
- [x] **Step 3: Implement the definitions and exact identities using `Complex.norm_exp_ofReal_mul_I`, `Complex.exp_add`, and geometric-sum lemmas.**
- [x] **Step 4: Prove the minimum of the trivial and geometric bounds.**
- [x] **Step 5: Build the contract and rerun the placeholder scan.**
- [x] **Step 6: Commit as `feat(vk): add finite phase-sum identities`.**

### Task 3: Discrete Kusmin-Landau Estimate

**Files:**
- Create: `ZeroFreeRegion/VinogradovKorobov/FirstDerivative.lean`
- Create: `Test/VinogradovKorobovFirstDerivativeContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Task 2's geometric block bound and real mean-value/monotonicity APIs.
- Produces: a quantitative first-derivative estimate for a monotone real phase separated from integral frequencies.

- [ ] **Step 1: State a failing contract with explicit derivative-separation hypotheses and an explicit result constant.**
- [ ] **Step 2: Verify the missing theorem failure.**
- [ ] **Step 3: Prove the increment bounds by the mean value theorem.**
- [ ] **Step 4: Convert increment separation to a geometric cancellation estimate and sum the controlled variation terms.**
- [ ] **Step 5: Build the contract and audit the theorem.**
- [ ] **Step 6: Commit as `feat(vk): prove discrete first derivative estimate`.**

### Task 4: Van Der Corput Second Derivative Test

**Files:**
- Create: `ZeroFreeRegion/VinogradovKorobov/SecondDerivative.lean`
- Create: `Test/VinogradovKorobovSecondDerivativeContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Task 1's autocorrelation inequality and Task 3's first-derivative estimate.
- Produces: an explicit second-derivative bound for finite complex phase sums.

- [ ] **Step 1: Write a failing contract for the two-sided second-derivative theorem.**
- [ ] **Step 2: Verify the contract fails for the missing theorem.**
- [ ] **Step 3: Apply the first-derivative theorem to each shifted phase difference in the autocorrelation sum.**
- [ ] **Step 4: Bound the weighted shift sum and optimize a concrete legal differencing length.**
- [ ] **Step 5: Build the contract, run the axiom audit, and check constants are positive.**
- [ ] **Step 6: Commit as `feat(vk): prove second derivative exponential-sum bound`.**

### Task 5: Apply The Bound To The Logarithmic Phase

**Files:**
- Create: `ZeroFreeRegion/VinogradovKorobov/LogPhase.lean`
- Create: `Test/VinogradovKorobovLogPhaseContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Task 4's second-derivative theorem and real logarithm derivative identities.
- Produces: a proved dyadic estimate for `sum exp (-I * t * log n)` and a theorem showing strict improvement over the trivial bound on an explicit parameter regime.

- [ ] **Step 1: Write failing contracts for the dyadic estimate and strict-saving corollary.**
- [ ] **Step 2: Verify both contracts fail before implementation.**
- [ ] **Step 3: Prove the first and second derivatives of `-t * log x` and their dyadic interval bounds.**
- [ ] **Step 4: Apply the second-derivative theorem and normalize the result to the repository's `n^(-it)` representation.**
- [ ] **Step 5: Prove the explicit parameter regime makes the new bound strictly less than the interval length.**
- [ ] **Step 6: Run all VK contracts, the axiom audit, consistency scripts, and the placeholder scan.**
- [ ] **Step 7: Commit as `feat(vk): bound logarithmic phase sums`.**

### Task 6: Record The Gate And Plan The Remaining VK Chain

**Files:**
- Modify: `docs/missing-chains-index.md`
- Modify: `docs/zero-free-region-chain.md`
- Modify: `docs/formal-theorem-inventory.md`

**Interfaces:**
- Consumes: Task 5's strict-saving theorem.
- Produces: an evidence-backed transition plan for exponent pairs, zeta growth, zero repulsion, and the `3/5` PNT error.

- [ ] **Step 1: Record exact proved theorem names and parameter regimes without claiming the VK region.**
- [ ] **Step 2: Identify the next exponent-pair or repeated-differencing theorem required for the zeta growth estimate.**
- [ ] **Step 3: Run `./scripts/verify-baseline.sh` when machine pressure permits and record the full validation bundle.**
- [ ] **Step 4: Commit as `docs(vk): record exponential-sum feasibility gate`.**
