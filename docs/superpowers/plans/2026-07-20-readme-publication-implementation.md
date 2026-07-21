# Publication-Oriented README Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the internal-log-style README with a Chinese-first, English-assisted publication entry point that remains precise about proved theorems, research branches, and open targets.

**Architecture:** Replace the current long README, add focused human-readable chain pages for the three newest result families, and make the new README a short navigation and claims surface. Do not retain a complete archive of the old README. Validate every headline theorem against Lean source and every repository-relative link against the filesystem.

**Tech Stack:** Markdown, Mermaid, Lean 4 source declarations, Git, shell-based static checks.

## Global Constraints

- Chinese is the primary narrative language; the English summary must independently describe the project.
- The new README must be approximately 350--500 lines.
- `main`, research-branch results, and open `def ... : Prop` targets must be separate.
- Do not claim RH, Vinogradov--Korobov, Selberg positive proportion, Conrey's percentage theorem, or Pintz maximal order.
- Every headline result must link to an exact Lean source file and a human-readable explanation.
- Do not modify Lean source files or project dependencies.
- Move still-current unique technical content into focused documents; do not preserve the old README as a complete archive.

---

### Task 1: Classify Existing Technical Material

**Files:**
- Inspect: `README.md`
- Reuse: `docs/formal-theorem-inventory.md`, `docs/target-statements-and-chains.md`, `docs/missing-chains-index.md`

**Interfaces:**
- Consumes: the complete current `README.md`.
- Produces: a list of still-current material to retain through focused documentation.

- [x] **Step 1: Identify unique current material**

Retain theorem declarations, proof-chain explanations, claim boundaries, and reproducibility commands.

- [x] **Step 2: Identify material to remove**

Remove obsolete progress logs, repeated inventories, stale next-step sections, and internal route narration.

- [x] **Step 3: Confirm no complete README archive remains**

The replacement README and focused documents are the only retained public documentation from this rewrite.

### Task 2: Add Human-Readable Detail Pages for New Results

**Files:**
- Create: `docs/riemann-von-mangoldt-chain.md`
- Create: `docs/carlson-zero-density-chain.md`
- Create: `docs/local-separation-hilbert-chain.md`

**Interfaces:**
- Consumes: theorem declarations in `PrimeNumberTheorem/RiemannVonMangoldt/AllHeightAsymptotic.lean`, `PrimeNumberTheorem/CarlsonAsymptotic.lean`, and `PrimeNumberTheorem/CarneiroLittmannProfile.lean`.
- Produces: stable explanation targets for the README theorem table and proof graph.

- [ ] **Step 1: Write the Riemann--von Mangoldt page**

Include these exact elements:

```text
Mathematical statement: N(T) = T/(2*pi) log(T/(2*pi)) - T/(2*pi) + O(log T).
Lean theorem: exists_abs_riemannZeroCount_sub_mainTerm_le_log.
Main file: PrimeNumberTheorem/RiemannVonMangoldt/AllHeightAsymptotic.lean.
Explanation: contour count, Gamma main term, good-height theorem, all-height extension.
Boundary: no RH and no numerical explicit final constant.
```

- [ ] **Step 2: Write the Carlson page**

Include these exact elements:

```text
Mathematical statement: N(sigma,T) = O(T^(4*sigma*(1-sigma)) (log T)^4), 1/2 < sigma < 1.
Lean theorem: carlson_zeroDensity_isBigO.
Main file: PrimeNumberTheorem/CarlsonAsymptotic.lean.
Explanation: multiplicity count, mollifier/detector, mean square, Littlewood rectangle count.
Boundary: fixed sigma, non-explicit constants, not RH or a density hypothesis.
```

- [ ] **Step 3: Write the local-separation page**

Include these exact elements:

```text
Lean theorems: hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann and finiteExponentialSum_meanSquare_le_localSeparation.
Main file: PrimeNumberTheorem/CarneiroLittmannProfile.lean.
Explanation: concrete extremal profile, Fourier certificate, reciprocal local gaps.
Boundary: reusable analytic infrastructure; it does not by itself strengthen Carlson.
```

- [ ] **Step 4: Check theorem identifiers in source**

```bash
rg -n 'theorem exists_abs_riemannZeroCount_sub_mainTerm_le_log|theorem carlson_zeroDensity_isBigO|theorem hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann|theorem finiteExponentialSum_meanSquare_le_localSeparation' PrimeNumberTheorem
```

Expected: all four declarations are found.

### Task 3: Rewrite the README as the Publication Entry Point

**Files:**
- Modify: `README.md`

**Interfaces:**
- Consumes: the design specification, Task 1 classification, Task 2 detail pages, current theorem declarations, and current PR/branch status.
- Produces: the repository's public publication-oriented landing page.

- [ ] **Step 1: Replace the title and opening sections**

Use the Chinese title and English subtitle from the design. Add a Chinese plain-language overview explaining primes, zeta zeros, RH, Lean verification, and the project's non-RH boundary. Follow it with a 150--250-word English summary.

- [ ] **Step 2: Add the verified theorem table**

List only results merged into `main`:

```text
classical_zero_free_region_proved
PNTForm3_proved and the classical psi/pi error theorems
hardy_theorem_target_proved
exists_abs_riemannZeroCount_sub_mainTerm_le_log
carlson_zeroDensity_isBigO
hilbertForm_norm_le_two_pi_localSeparation_carneiroLittmann
finiteExponentialSum_meanSquare_le_localSeparation
```

Each row links to source and an explanation page.

- [ ] **Step 3: Add a separate research status table**

State exact branch boundaries:

```text
research/hardy-littlewood: theorem contracts exist; integration/full audit pending.
research/pintz-envelope-upper: envelope foundation; no prime-error oscillation bridge.
feat/vinogradov-korobov-exponential-sums: exponential-sum infrastructure; final VK target open.
agent/research-oscillation-smoothing-weil: draft partial routes with uncontrolled/infinite-dimensional gaps.
```

- [ ] **Step 4: Add the Mermaid proof map and publication packages**

The map must visually distinguish `main proved`, `branch proved`, and `open target`. Publication packages must rank Riemann--von Mangoldt + Carlson as immediately packageable, Hardy + Hardy--Littlewood as integration-dependent, and Selberg/VK/Pintz as future work.

- [ ] **Step 5: Add reproducibility, related work, deep-reading, and citation sections**

Include focused contracts, baseline/full-build commands, axiom policy, links to focused proof-chain and inventory documents, primary related-work links, and a software BibTeX entry without paper placeholders.

### Task 4: Validate Claims, Links, and Repository State

**Files:**
- Test: `README.md`
- Test: `docs/riemann-von-mangoldt-chain.md`
- Test: `docs/carlson-zero-density-chain.md`
- Test: `docs/local-separation-hilbert-chain.md`

**Interfaces:**
- Consumes: all documentation changes.
- Produces: a reviewable, committed, and pushed main branch.

- [ ] **Step 1: Check length and formatting**

```bash
wc -l README.md
git diff --check
```

Expected: README is between 350 and 500 lines; no whitespace errors.

- [ ] **Step 2: Check prohibited overclaims**

```bash
rg -n 'RH.*proved|proved.*RH|Vinogradov.Korobov.*proved|Selberg.*proved|Pintz.*maximal.*proved|first formalization' README.md
```

Expected: no positive theorem claim matching these patterns; explicit non-claim text may be reviewed manually.

- [ ] **Step 3: Check repository-relative Markdown links**

Run a shell script that extracts non-HTTP Markdown link targets from the four changed public documents, strips anchors, and fails when a target does not exist relative to its source file.

Expected: every repository-relative target exists.

- [ ] **Step 4: Run documentation-adjacent project checks**

```bash
./scripts/verify-baseline.sh
python3 scripts/list-target-statements.py
python3 scripts/check-chain-gaps.py
```

Expected: all commands exit 0. Do not start another full Lean build if one is already running; cite the latest successful merged-PR full builds instead.

- [ ] **Step 5: Review the final diff and commit**

```bash
git diff --stat
git diff -- README.md docs/riemann-von-mangoldt-chain.md docs/carlson-zero-density-chain.md docs/local-separation-hilbert-chain.md
git add README.md PUBLISHING.md docs/riemann-von-mangoldt-chain.md docs/carlson-zero-density-chain.md docs/local-separation-hilbert-chain.md docs/superpowers/specs/2026-07-20-readme-publication-design.md docs/superpowers/plans/2026-07-20-readme-publication-implementation.md
git commit -m "docs: publish bilingual research overview"
```

- [ ] **Step 6: Push the reviewed commits**

```bash
git push origin main
```

Expected: `main` and `origin/main` point to the same final commit; `.DS_Store` remains untracked and untouched.
