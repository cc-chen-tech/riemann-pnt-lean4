# Published Off-Diagonal Coverage Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the current qualitative discussion of published estimates by an exact-rational Region A--C coverage ledger for the weakest (O(T^{1+\varepsilon})) coupled-kernel target, and emit deterministic witnesses for every residual route represented by the audit.

**Architecture:** A focused Python module will encode the admissible exponent box, the two Bettin--Chandee savings, the best elementary completion exponent, and the direct-applicability decision for Wright's fixed-denominator theorem. The research note will derive each formula from the primary theorem statement, separate the (O(T^{1+\varepsilon})) gate from the stronger (o(T)) gate, and explain why a (T^\eta)-enlarged core makes the tail harmless for the stated upper-bound goal.

**Tech Stack:** Python 3 exact `fractions.Fraction`, pytest, Markdown/LaTeX, primary-source theorem statements from arXiv:1502.00769, arXiv:1411.7764, and arXiv:2604.25177.

**Spec:** `docs/superpowers/specs/2026-08-24-mobius-weighted-offdiagonal-design.md`

## Global Constraints

- Every analytic theorem must retain its exact hypotheses and be cited to a primary source.
- The checker proves rational algebra only; it must never label an analytic gate as proved.
- The target for this slice is the original upper bound (O_{\varepsilon,W}(T^{1+\varepsilon})), not the stronger asymptotic (o(T)).
- No new Lean axiom, `sorry`, `admit`, or theorem claiming the coupled gate is allowed.
- The original coupled (h,\delta,r,s) kernel and both Möbius weights remain the Region-D interface.

---

### Task 1: Exact Region-A savings

**Files:**
- Create: `scripts/audit_mwkf_coverage.py`
- Create: `tests/test_mwkf_coverage_audit.py`

**Interfaces:**
- Consumes: `ExponentBox` and `is_admissible` from `scripts.audit_mwkf_ranges`.
- Produces: `BettinChandeeSavings(first: Fraction, second: Fraction)`, `bettin_chandee_savings(box)`, and `bettin_chandee_covers(box)`.

- [ ] **Step 1: Write the failing test**

```python
def test_bc_savings_are_the_two_hand_derived_exponents() -> None:
    balanced = boundary_witnesses()["balanced_max_a"]
    assert bettin_chandee_savings(balanced) == BettinChandeeSavings(
        first=F(-41, 10), second=F(-37, 8)
    )
    short = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(0))
    assert bettin_chandee_savings(short) == BettinChandeeSavings(
        first=F(1, 20), second=F(1, 8)
    )
```

- [ ] **Step 2: Run test to verify it fails**

Run: `pytest -q tests/test_mwkf_coverage_audit.py::test_bc_savings_are_the_two_hand_derived_exponents`

Expected: FAIL because `scripts.audit_mwkf_coverage` does not exist.

- [ ] **Step 3: Write minimal implementation**

```python
@dataclass(frozen=True)
class BettinChandeeSavings:
    first: Fraction
    second: Fraction

def bettin_chandee_savings(box: ExponentBox) -> BettinChandeeSavings:
    a = box.third_length
    largest = max(box.rho, box.sigma)
    smallest = min(box.rho, box.sigma)
    return BettinChandeeSavings(
        Fraction(3, 20) * (box.rho + box.sigma)
        - Fraction(17, 20) * a - Fraction(1, 4) * largest,
        Fraction(1, 8) * smallest - a,
    )

def bettin_chandee_covers(box: ExponentBox) -> bool:
    savings = bettin_chandee_savings(box)
    return is_admissible(box) and savings.first >= 0 and savings.second >= 0
```

- [ ] **Step 4: Run test to verify it passes**

Run: `pytest -q tests/test_mwkf_coverage_audit.py`

Expected: PASS.

### Task 2: Completion and Wright applicability

**Files:**
- Modify: `scripts/audit_mwkf_coverage.py`
- Modify: `tests/test_mwkf_coverage_audit.py`

**Interfaces:**
- Consumes: the exponent box from Task 1.
- Produces: `completion_exponents(box)`, `completion_covers(box)`, and `wright_direct_applicability(box, fixed_denominator_factor)`.

- [ ] **Step 1: Write the failing tests**

```python
def test_completion_records_boundary_and_trivial_losses() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert completion_exponents(box) == (F(5), F(3), F(3))
    assert not completion_covers(box)
    unit_a = ExponentBox(F(2), F(1), F(0), F(1), F(0), F(0), F(0))
    assert completion_covers(unit_a)

def test_wright_has_no_direct_fixed_factor_in_the_original_s_sum() -> None:
    box = boundary_witnesses()["r_long"]
    result = wright_direct_applicability(box, fixed_denominator_factor=F(0))
    assert not result.improves_bc
    assert result.reason == "R0=1 recovers BC equation (7.2), so gives no improvement"
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `pytest -q tests/test_mwkf_coverage_audit.py -k 'completion or wright'`

Expected: FAIL because the functions are missing.

- [ ] **Step 3: Implement the hand-derived completion exponents**

```python
def completion_exponents(box: ExponentBox) -> tuple[Fraction, Fraction, Fraction]:
    return (
        box.third_length,
        max(box.sigma, box.ell),
        max(box.sigma, box.h),
    )

def completion_covers(box: ExponentBox) -> bool:
    return is_admissible(box) and min(completion_exponents(box)) <= 0
```

The entries correspond respectively to the trivial (LH) bound, completion in (h), and completion in \(\delta\). For example, smooth completion in (h) gives

\[
 \sum_{\delta\asymp L}\left|\sum_{h\asymp H}F(h/H)e(-h\delta\bar r/s)\right|
 \ll T^\varepsilon (1+L/s)(H+s),
\]

whose exponent is `max(ell-sigma, 0) + max(h, sigma) = max(ell, sigma)` because the admissible polytope has `h <= sigma`.

- [ ] **Step 4: Implement Wright's direct-applicability record**

```python
@dataclass(frozen=True)
class WrightApplicability:
    improves_bc: bool
    reason: str

def wright_direct_applicability(
    box: ExponentBox, fixed_denominator_factor: Fraction
) -> WrightApplicability:
    if fixed_denominator_factor == 0:
        return WrightApplicability(
            False, "R0=1 recovers BC equation (7.2), so gives no improvement"
        )
    return WrightApplicability(
        False,
        "a positive fixed factor requires a prior factorization of s and belongs to Region D",
    )
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `pytest -q tests/test_mwkf_coverage_audit.py`

Expected: PASS.

### Task 3: Deterministic route classification

**Files:**
- Modify: `scripts/audit_mwkf_coverage.py`
- Modify: `tests/test_mwkf_coverage_audit.py`

**Interfaces:**
- Consumes: Tasks 1 and 2.
- Produces: `classify_box(box) -> CoverageResult` and CLI witness output.

- [ ] **Step 1: Write the failing test**

```python
def test_residual_witnesses_are_not_reported_as_published_coverage() -> None:
    results = {name: classify_box(box) for name, box in boundary_witnesses().items()}
    assert results["balanced_max_a"].route == "D"
    assert results["r_long"].route == "D"
    assert results["s_long"].route == "D"
    assert results["large_q_endpoint"].route == "D"
```

- [ ] **Step 2: Run test to verify it fails**

Run: `pytest -q tests/test_mwkf_coverage_audit.py::test_residual_witnesses_are_not_reported_as_published_coverage`

Expected: FAIL because `classify_box` is missing.

- [ ] **Step 3: Implement the classifier**

```python
@dataclass(frozen=True)
class CoverageResult:
    route: str
    reason: str

def classify_box(box: ExponentBox) -> CoverageResult:
    if bettin_chandee_covers(box):
        return CoverageResult("A", "both BC saving exponents are nonnegative")
    if completion_covers(box):
        return CoverageResult("B", "the h-delta support has exponent zero")
    return CoverageResult("D", "no direct Region A-C theorem covers the box")
```

- [ ] **Step 4: Run all coverage tests**

Run: `pytest -q tests/test_mwkf_coverage_audit.py`

Expected: PASS.

### Task 4: Research-note proof and upper-bound tail correction

**Files:**
- Modify: `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`

**Interfaces:**
- Consumes: exact formulas and classifications from Tasks 1--3.
- Produces: a primary-source hypothesis table, the Region A--C inequalities, and the corrected weakest (O(T^{1+\varepsilon})) gate.

- [ ] **Step 1: Add the weakest-gate distinction**

State separately:

\[
 |\mathfrak S_q[\Psi]|\ll_{\varepsilon,W}RS T^\varepsilon
 \Longrightarrow \mathcal R_{T^3,T}\ll_{\varepsilon,W}T^{1+\varepsilon},
\]

and retain `CK_{1/1000}` only as the stronger input needed for an (o(T)) asymptotic.

- [ ] **Step 2: Prove the (T^\eta)-core tail bound**

Replace the polylog-only upper-bound tail by cutoffs

\[
 |\delta|\le (MR/T)T^\eta,\qquad |h|\le(S/M)T^\eta.
\]

For the complement, perform (J) integrations by parts with (J\eta>7/2+A\). Combining the resulting (T^{-J\eta}) with the existing absolute scale (T^{9/2+\varepsilon}) gives (O(T^{1-A+\varepsilon})). Record that this argument is for the upper-bound target and does not supply a logarithmic asymptotic error.

- [ ] **Step 3: Derive the Region-A inequalities**

Starting from Bettin--Chandee Theorem 1 and the exact norms, write the two local exponents

\[
 E_1=\frac{17}{20}(a+\rho+\sigma)+\frac14\max(\rho,\sigma),\qquad
 E_2=\frac78(\rho+\sigma)+a+\frac18\max(\rho,\sigma).
\]

Coverage of the (RS T^\varepsilon) target is exactly (E_i\le\rho+\sigma\), equivalent to the two savings in Task 1.

- [ ] **Step 4: Derive Region B and audit Region C**

Prove the incomplete-completion inequality used in Task 2, list its three exponent losses, and state that it directly closes only the exponent-zero (LH=T^{o(1)}) face. Quote Wright Theorem 2.1 with its fixed denominator (nR_0), `M << N^2`, and polynomial-size (R_0) hypotheses; explain that the original sum has (R_0=1), for which Wright explicitly recovers Bettin--Chandee (7.2), while (R_0>1) requires factorizing (s=R_0n) and therefore belongs to the structured Region-D analysis.

- [ ] **Step 5: Update the status ledger without claiming closure**

Mark the (O(T^{1+\varepsilon})) tail as proved after power enlargement, Regions A--C as exactly classified, and the residual coupled Type-I/II inequality as unproved.

### Task 5: Verification and commit

**Files:**
- Verify all files above.

**Interfaces:**
- Consumes: Tasks 1--4.
- Produces: a clean, reviewable published-coverage commit.

- [ ] **Step 1: Run focused tests**

Run: `pytest -q tests/test_mwkf_coverage_audit.py tests/test_mwkf_range_audit.py`

Expected: all tests PASS.

- [ ] **Step 2: Run the deterministic checkers**

Run: `python3 scripts/audit_mwkf_ranges.py && python3 scripts/audit_mwkf_coverage.py`

Expected: every named boundary box prints a stable route and exact rational BC savings.

- [ ] **Step 3: Run repository formatting checks**

Run: `git diff --check`

Expected: exit 0.

- [ ] **Step 4: Audit proof-status language**

Run: `rg -n "proved|unproved|conditional|CK_|MWKF|TAIL|Wright|Bettin" docs/research/2026-08-24-mobius-weighted-off-diagonal.md`

Expected: the upper-bound tail is proved, the coupled Region-D gate remains explicitly unproved, and no direct Wright coverage is asserted.

- [ ] **Step 5: Commit the coverage slice**

```bash
git add docs/superpowers/plans/2026-08-25-mobius-off-diagonal-published-coverage.md \
  docs/research/2026-08-24-mobius-weighted-off-diagonal.md \
  scripts/audit_mwkf_coverage.py tests/test_mwkf_coverage_audit.py
git commit -m "docs(research): classify published off-diagonal coverage"
```
