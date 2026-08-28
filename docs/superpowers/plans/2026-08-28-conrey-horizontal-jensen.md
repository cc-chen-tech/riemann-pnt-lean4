# Conrey Horizontal Jensen Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the actual-product Jensen divisor-mass and admissible-horizontal-height checkpoint needed for Conrey's equation (37).

**Architecture:** A geometry module fixes the moving disk without crossing `Re s=0` or `s=1`. A growth module proves concrete bounds for the explicit mollifier and degree-one `V1`; a Jensen module combines those bounds with the existing analytic Jensen library and selects a zero-free horizontal height. The weighted horizontal integral remains a later plan.

**Tech Stack:** Lean 4, Mathlib complex analysis, existing `AnalyticJensen`, `HorizontalArgument`, Conrey right-edge modules, Lake contract tests.

**Spec:** `docs/superpowers/specs/2026-08-28-conrey-horizontal-jensen-design.md`

## Global Constraints

- Use the constants and admissible window from the spec verbatim.
- Prove actual-product growth; no conditional growth interface may be advertised as closure.
- Write each contract before production code and record the expected missing declaration.
- Run `#print axioms` for every public endpoint; allow only `propext`, `Classical.choice`, and `Quot.sound`.
- Do not claim the weighted horizontal term, equations (38)--(41), the long mollified mean square, or strict `> 2/5`.

---

### Task 1: Moving Jensen geometry and actual-product analyticity

**Files:**
- Create: `HardyTheorem/ConreyHorizontalJensenGeometry.lean`
- Create: `Test/ConreyHorizontalJensenGeometryContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one` and `analyticOnNhd_conreyMollifier`.
- Produces: `conreyHorizontalRightEdge`, `conreyHorizontalLeftEdge`, `conreyHorizontalJensenCenter`, `conreyHorizontalJensenInnerRadius`, `conreyHorizontalJensenOuterRadius`, rectangle containment, `innerRadius < outerRadius`, and actual-product analyticity on the outer closed ball.

- [x] **Step 1: Write the failing contract**

Check all seven definitions/endpoints above with `#check`, then run:

```bash
lake env lean Test/ConreyHorizontalJensenGeometryContract.lean
```

Expected: failure because `HardyTheorem.ConreyHorizontalJensenGeometry` does not exist.

- [x] **Step 2: Implement the five exact geometry definitions**

Use exactly:

```lean
def conreyHorizontalRightEdge (L : ℝ) : ℝ := 2 * Real.log L
def conreyHorizontalLeftEdge (R L : ℝ) : ℝ := 1 / 2 - R / L
def conreyHorizontalJensenCenter (L U : ℝ) : ℂ :=
  conreyHorizontalRightEdge L + I * (U + 1 / 2)
def conreyHorizontalJensenInnerRadius (R L : ℝ) : ℝ :=
  Real.sqrt ((conreyHorizontalRightEdge L -
    conreyHorizontalLeftEdge R L) ^ 2 + 1 / 4)
def conreyHorizontalJensenOuterRadius (L : ℝ) : ℝ :=
  conreyHorizontalRightEdge L - 1 / 4
```

- [x] **Step 3: Prove the geometry inequalities**

Under `40000 <= L`, `0 <= R`, `R <= 6/5`, prove rectangle containment,
`0 < innerRadius`, `innerRadius < outerRadius`, and `1/4 <= z.re` on the
outer disk. Under `rightEdge L + 1 <= U`, prove every point of the outer disk
is different from `1`.

- [x] **Step 4: Prove actual-product analyticity**

For the explicit parameters and `conreyExplicitP`, combine the preceding
real-part and pole-avoidance statements with the existing `V1` and mollifier
analyticity theorems.

- [x] **Step 5: Verify and commit**

```bash
lake env lean Test/ConreyHorizontalJensenGeometryContract.lean
lake build HardyTheorem.ConreyHorizontalJensenGeometry Test.ConreyHorizontalJensenGeometryContract
git diff --check
git add HardyTheorem/ConreyHorizontalJensenGeometry.lean Test/ConreyHorizontalJensenGeometryContract.lean lakefile.lean
git commit -m "feat(conrey): establish horizontal Jensen geometry"
```

### Task 2: Uniform center lower bound

**Files:**
- Create: `HardyTheorem/ConreyHorizontalJensenCenter.lean`
- Create: `Test/ConreyHorizontalJensenCenterContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: the low/high right-edge norm estimates already in `ConreyExplicitRightVertical` and `ConreyExplicitRightVerticalLow`.
- Produces:

```lean
theorem one_sixth_le_norm_conreyExplicitRightVerticalProduct
    {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : 40000 ≤ L) (ht : 1 ≤ t) (htop : t ≤ Real.exp L) :
    (1 / 6 : ℝ) ≤ ‖conreyExplicitRightVerticalProduct Y sigma0 L t‖
```

- [x] **Step 1: Write and run the failing contract**

Expected: unknown declaration.

- [x] **Step 2: Split at `t = 2 * log L`**

Use the existing low theorem for the first interval. On the high interval,
combine `one_third_le_conreyExplicitDegreeOneHeightMain_re` with the proved
product error bound and discharge the explicit `<= 1/6` error arithmetic at
`L >= 40000`.

- [x] **Step 3: Verify axiom boundary and commit**

```bash
lake env lean Test/ConreyHorizontalJensenCenterContract.lean
lake build HardyTheorem.ConreyHorizontalJensenCenter Test.ConreyHorizontalJensenCenterContract
git diff --check
git add HardyTheorem/ConreyHorizontalJensenCenter.lean Test/ConreyHorizontalJensenCenterContract.lean lakefile.lean
git commit -m "feat(conrey): bound horizontal Jensen centers away from zero"
```

### Task 3: Actual-product outer-circle growth

**Files:**
- Create: `HardyTheorem/ConreyHorizontalJensenGrowth.lean`
- Create: `Test/ConreyHorizontalJensenGrowthContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Task 1 geometry, `exists_norm_riemannZeta_le_polynomial_on_zero_four`, Cauchy derivative estimates, digamma recurrence, and `abs_conreyExplicitP_le_one`.
- Produces fixed constants `C >= 1` and the actual bound

```text
norm F(z) <= C * Y * (U + rightEdge L + 10)^6 * (L + 2)^2
```

on the outer closed ball, under the exact spec hypotheses.

- [x] **Step 1: Write and run the failing contract**

Check separate mollifier, zeta/derivative, `H'/H`, `V1`, and product growth endpoints. Expected: unknown declarations.

- [x] **Step 2: Prove `norm B <= Y` on `Re s >= 1/4`**

Expose or locally reprove the private coefficient bound from
`ConreyMollifierRightEdge`; bound every Dirichlet term by one and the number of
terms by `Y`.  Do not reuse the moving-right-line `B = 1 + O(1/L)` theorem.

- [x] **Step 3: Prove zeta and zeta-derivative polynomial bounds**

Use a radius-`1/16` Cauchy circle and split its center at `Re s = 63/16`.
On the left the circle lies in `0 <= Re w <= 4` and has `|Im w| > 1`; on
the right it lies in `Re w > 2`.  Feed the corresponding zeta bounds into
the proved Cauchy derivative bridge.

- [x] **Step 4: Prove the `H'/H` logarithmic bound**

First generalize `logDeriv_conreyH_eq` to `0 < Re s` and `s != 1`.
For `z=s/2`, use `|Im z| >= 7/8` to control `z⁻¹`, then one digamma
recurrence to `Re (z+1) >= 1`.  Use the disk's `Im s >= 7/4` for the rational
factors.

- [x] **Step 5: Assemble actual-product growth, verify, and commit**

```bash
lake env lean Test/ConreyHorizontalJensenGrowthContract.lean
lake build HardyTheorem.ConreyHorizontalJensenGrowth Test.ConreyHorizontalJensenGrowthContract
git diff --check
git add HardyTheorem/ConreyHorizontalJensenGrowth.lean Test/ConreyHorizontalJensenGrowthContract.lean lakefile.lean
git commit -m "feat(conrey): prove horizontal Jensen circle growth"
```

### Task 4: Jensen divisor mass and admissible height

**Files:**
- Create: `HardyTheorem/ConreyHorizontalJensenCount.lean`
- Create: `Test/ConreyHorizontalJensenCountContract.lean`
- Modify: `lakefile.lean`
- Modify: `docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md`

**Interfaces:**
- Consumes: Tasks 1--3 and `PrimeNumberTheorem.AnalyticJensen`.
- Produces the exact `HJ-mass` inequality and a height `t in Icc U (U+1)` on which `F(x+it) != 0` for every `x in Icc sigma0 A`.

- [x] **Step 1: Write and run the failing contract**

Check the divisor definition, finite support, exact mass bound, and admissible-height theorem. Expected: unknown declarations.

- [x] **Step 2: Apply Jensen with center norm `1/6`**

Keep `Real.log (outerRadius / innerRadius)` visible. Do not replace it by a Big-O predicate.

- [x] **Step 3: Select a zero-free height**

Map the finite divisor support in the inner disk to imaginary parts and use the existing finite-set separation lemma to obtain a height in the unit window. Convert any hypothetical horizontal zero back to inner-disk divisor support using Task 1 containment.

- [x] **Step 4: Verify, document, and commit**

```bash
lake env lean Test/ConreyHorizontalJensenCountContract.lean
lake build HardyTheorem.ConreyHorizontalJensenCount Test.ConreyHorizontalJensenCountContract
git diff --check
git add HardyTheorem/ConreyHorizontalJensenCount.lean Test/ConreyHorizontalJensenCountContract.lean lakefile.lean docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md
git commit -m "feat(conrey): select Jensen-controlled horizontal heights"
```

### Task 5: Whole-checkpoint verification and publication

**Files:**
- Modify: PR body only after all local verification succeeds.

**Interfaces:**
- Consumes: Tasks 1--4.
- Produces: an honest ready-for-review stacked PR whose body lists the weighted horizontal regular-part bound as still open.

- [ ] **Step 1: Run focused verification**

```bash
lake build HardyTheorem.ConreyHorizontalJensenGeometry HardyTheorem.ConreyHorizontalJensenCenter HardyTheorem.ConreyHorizontalJensenGrowth HardyTheorem.ConreyHorizontalJensenCount Test.ConreyHorizontalJensenGeometryContract Test.ConreyHorizontalJensenCenterContract Test.ConreyHorizontalJensenGrowthContract Test.ConreyHorizontalJensenCountContract
git diff --check
```

- [ ] **Step 2: Run the default build and wait for its final exit code**

```bash
lake build
```

- [ ] **Step 3: Review proof status**

Confirm that no theorem name or documentation claims equation (37), the
weighted horizontal terms, the far-right argument variation, the long mean
square, or strict `> 2/5` complete.  In particular, do not identify the
proved right-edge `integral |log |F||` with argument variation.

- [ ] **Step 4: Push and open the stacked PR**

Base the PR on `codex/conrey-global-right-vertical-20260828`, keep it non-Draft, and include the exact remaining-gates ledger.
