# Möbius-Weighted Off-Diagonal Exact Audit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Audit and, where necessary, correct the exact AFE/Poisson reduction for the \(N=T^3\) Möbius mollifier, then identify the weakest local Kloosterman gate that still implies an \(O(T^{1+\varepsilon})\) remainder.

**Architecture:** Keep the mathematical derivation in the existing research note and add one dependency-free exact-rational Python ledger for the exponent polytope. Regression tests verify the finite algebra, boundary witnesses, and document status markers; they never stand in for the analytic proof. This plan stops after exact-reduction and gate validation, before applying BCR/Wright bounds or attempting a new Type I/II estimate.

**Tech Stack:** Markdown/LaTeX, Python 3.9 standard library (`dataclasses`, `fractions`), pytest supplied ephemerally by `uv`, Git.

**Spec:** `docs/superpowers/specs/2026-08-24-mobius-weighted-off-diagonal-design.md`

## Global Constraints

- Preserve the distinction among exact identities, published inputs, numerical diagnostics, and unproved analytic inequalities.
- Do not claim Farmer's all-length mollifier conjecture.
- Do not use withdrawn arXiv:2601.00292 as an analytic input.
- Do not create a Lean axiom for MWKF(3), and do not add `sorry` or `admit`.
- Do not multiply a pointwise approximate-functional-equation error by the length-\(T^3\) mollifier.
- Retain the exact logarithm and full smooth kernel; do not introduce an unaudited Taylor remainder.
- Treat the rational range checker as a regression tool, not as a proof of the analytic estimates.
- Make no Lean source change in this slice; consequently, verification is Python/document-focused and does not start a full Lean build.
- Work only in the existing isolated worktree `.worktrees/docs-mobius-weighted-offdiagonal-20260824` on branch `codex/docs-mobius-weighted-offdiagonal-20260824`.

## File map

- Create `scripts/audit_mwkf_ranges.py`: exact-rational representation of the zero-slack exponent polytope and deterministic boundary witnesses.
- Create `tests/test_mwkf_range_audit.py`: executable regression tests for the polytope, witnesses, finite implications, and research-note audit markers.
- Modify `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`: corrected analytic derivation, proof-status ledger, gate comparison, and final classification for this slice.
- Read only `docs/research/2026-08-24-selberg-mobius-lcm-main-term.md` once PR #478 is available locally or on `origin/main`: cross-check the normalization of the main quadratic form without copying its proof.

---

### Task 1: Exact exponent-polytope ledger

**Files:**
- Create: `scripts/audit_mwkf_ranges.py`
- Create: `tests/test_mwkf_range_audit.py`

**Interfaces:**
- Consumes: the zero-slack constraints in the approved spec and equations (5.3), (5.6), (5.7), (5.10), (5.11) of the research note.
- Produces:
  - `ExponentBox(rho, sigma, m, k, ell, h, kappa)` with `Fraction` fields;
  - `ExponentBox.third_length -> Fraction`, equal to `ell + h`;
  - `admissibility_violations(box) -> tuple[str, ...]`;
  - `is_admissible(box) -> bool`;
  - `boundary_witnesses() -> dict[str, ExponentBox]`.

- [ ] **Step 1: Write failing tests for admissible boundary boxes**

Create `tests/test_mwkf_range_audit.py` with:

```python
from fractions import Fraction as F

from scripts.audit_mwkf_ranges import (
    ExponentBox,
    admissibility_violations,
    boundary_witnesses,
    is_admissible,
)


def test_balanced_maximal_third_variable_box() -> None:
    box = ExponentBox(
        rho=F(3), sigma=F(3), m=F(1, 2), k=F(1, 2),
        ell=F(5, 2), h=F(5, 2), kappa=F(0),
    )
    assert box.third_length == F(5)
    assert admissibility_violations(box) == ()
    assert is_admissible(box)


def test_unbalanced_endpoint_boxes_remain_admissible() -> None:
    witnesses = boundary_witnesses()
    assert set(witnesses) == {
        "balanced_max_a", "r_long", "s_long", "large_q_endpoint"
    }
    assert all(is_admissible(box) for box in witnesses.values())
    assert witnesses["r_long"].third_length == F(4)
    assert witnesses["s_long"].third_length == F(4)
    assert witnesses["large_q_endpoint"].kappa == F(2)
```

- [ ] **Step 2: Run the focused test and verify the import failure**

Run:

```bash
uv run --with pytest pytest tests/test_mwkf_range_audit.py -v
```

Expected: FAIL during collection with `ModuleNotFoundError: No module named 'scripts.audit_mwkf_ranges'`.

- [ ] **Step 3: Implement the exact-rational data model and witnesses**

Create `scripts/audit_mwkf_ranges.py` with this public surface:

```python
#!/usr/bin/env python3
"""Exact zero-slack exponent ledger for the MWKF(3) reduction.

This module checks linear implications only.  It does not prove an
oscillatory-sum estimate or certify that an analytic truncation is valid.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class ExponentBox:
    rho: Fraction
    sigma: Fraction
    m: Fraction
    k: Fraction
    ell: Fraction
    h: Fraction
    kappa: Fraction

    @property
    def third_length(self) -> Fraction:
        return self.ell + self.h


def admissibility_violations(box: ExponentBox) -> tuple[str, ...]:
    v: list[str] = []
    values = (
        box.rho, box.sigma, box.m, box.k,
        box.ell, box.h, box.kappa,
    )
    if any(value < 0 for value in values):
        v.append("nonnegative")
    if box.kappa + box.rho > 3:
        v.append("mollifier_r")
    if box.kappa + box.sigma > 3:
        v.append("mollifier_s")
    if box.k + box.m > 1:
        v.append("km_length")
    if box.k + box.sigma != box.m + box.rho:
        v.append("ratio_balance")
    if box.ell > box.m + box.rho - 1:
        v.append("delta_length")
    if box.h > box.sigma - box.m:
        v.append("frequency_length")
    if box.third_length > box.rho + box.sigma - 1:
        v.append("third_length")
    return tuple(v)


def is_admissible(box: ExponentBox) -> bool:
    return not admissibility_violations(box)


def boundary_witnesses() -> dict[str, ExponentBox]:
    F = Fraction
    return {
        "balanced_max_a": ExponentBox(F(3), F(3), F(1, 2), F(1, 2),
                                       F(5, 2), F(5, 2), F(0)),
        "r_long": ExponentBox(F(3), F(2), F(0), F(1),
                               F(2), F(2), F(0)),
        "s_long": ExponentBox(F(2), F(3), F(1), F(0),
                               F(2), F(2), F(0)),
        "large_q_endpoint": ExponentBox(F(1), F(1), F(0), F(0),
                                         F(0), F(1), F(2)),
    }
```

- [ ] **Step 4: Run the boundary tests and verify they pass**

Run:

```bash
uv run --with pytest pytest tests/test_mwkf_range_audit.py -v
```

Expected: 2 tests PASS.

- [ ] **Step 5: Add rejection tests for every independent constraint**

Append this parameterized test:

```python
import pytest


@pytest.mark.parametrize(
    ("box", "code"),
    [
        (ExponentBox(F(-1), F(1), F(0), F(0), F(0), F(0), F(0)),
         "nonnegative"),
        (ExponentBox(F(3), F(1), F(0), F(2), F(0), F(0), F(1)),
         "mollifier_r"),
        (ExponentBox(F(1), F(3), F(2), F(0), F(0), F(0), F(1)),
         "mollifier_s"),
        (ExponentBox(F(2), F(2), F(1), F(1), F(0), F(0), F(0)),
         "km_length"),
        (ExponentBox(F(2), F(2), F(0), F(1), F(0), F(0), F(0)),
         "ratio_balance"),
        (ExponentBox(F(2), F(2), F(0), F(0), F(2), F(0), F(0)),
         "delta_length"),
        (ExponentBox(F(2), F(2), F(0), F(0), F(0), F(3), F(0)),
         "frequency_length"),
    ],
)
def test_each_constraint_has_a_stable_failure_code(
    box: ExponentBox, code: str
) -> None:
    assert code in admissibility_violations(box)
    assert not is_admissible(box)
```

- [ ] **Step 6: Run all range tests**

Run:

```bash
uv run --with pytest pytest tests/test_mwkf_range_audit.py -v
```

Expected: all tests PASS.

- [ ] **Step 7: Commit the executable range ledger**

```bash
git add scripts/audit_mwkf_ranges.py tests/test_mwkf_range_audit.py
git commit -m "test(research): encode MWKF exponent polytope"
```

---

### Task 2: Audit the exact AFE and shifted-divisor expansion

**Files:**
- Modify: `docs/research/2026-08-24-mobius-weighted-off-diagonal.md:1-311`
- Modify: `tests/test_mwkf_range_audit.py`

**Interfaces:**
- Consumes: the existing definitions of \(G_t\), \(g_t\), \(V_t\), \(\mathscr J_t\), and the dyadic shifted-divisor boxes.
- Produces: three separately reviewable derivations headed `Completion and pole cancellation`, `Absolute convergence and termwise expansion`, and `Uniform weight bounds`; a prominent proof-status table that no longer treats unaudited later sections as proved.

- [ ] **Step 1: Add a failing document-contract test**

Append:

```python
from pathlib import Path


NOTE = Path("docs/research/2026-08-24-mobius-weighted-off-diagonal.md")


def test_research_note_exposes_afe_audit_ledger() -> None:
    text = NOTE.read_text()
    for marker in (
        "> **Current proof status.**",
        "### 2.1 Completion and pole cancellation",
        "### 2.2 Absolute convergence and termwise expansion",
        "### 2.3 Uniform weight bounds",
    ):
        assert marker in text
    assert "\\Lambda(s)=\\gamma(s)\\zeta(s)" in text
```

- [ ] **Step 2: Run the document-contract test and verify failure**

Run:

```bash
uv run --with pytest pytest \
  tests/test_mwkf_range_audit.py::test_research_note_exposes_afe_audit_ledger -v
```

Expected: FAIL because the status block and subsection markers are absent.

- [ ] **Step 3: Add the proof-status block and define the completion**

Immediately below the title, add a status block with four rows:

```text
LCM main quadratic form                 proved separately
Exact AFE and shifted-divisor identity under audit in Sections 2--3
Poisson zero/nonzero-mode identity      under audit in Section 4
MWKF local estimate                     unproved
```

In Section 2 define

\[
 \Lambda(s)=\gamma(s)\zeta(s),\qquad
 \gamma(s)=\pi^{-s/2}\Gamma(s/2),
\]

and state explicitly that this \(\Lambda\) is meromorphic with simple poles
at \(0,1\) and satisfies \(\Lambda(s)=\Lambda(1-s)\).

- [ ] **Step 4: Expand the pole-cancellation derivation**

Under `### 2.1 Completion and pole cancellation`, list the poles of the two
completed factors as

\[
 -s_t,\quad 1-s_t,\quad s_t-1,\quad s_t,
\]

match them respectively with the zeros of the two quadratic factors in
\(G_t(z)\), and write the contour rectangle at height \(V\). Record the
horizontal-integral bound before taking \(V\to\infty\). After the substitution
\(z\mapsto-z\), display the sign from orientation and derive

\[
 2\mathscr J_t=\Lambda(s_t)\Lambda(1-s_t).
\]

- [ ] **Step 5: Supply absolute-convergence majorants**

Under `### 2.2 Absolute convergence and termwise expansion`, use
\(\Re(s_t+z)=\Re(1-s_t+z)=5/2\) on \(\Re z=2\) and record

\[
 \sum_{m,n\ge1}(mn)^{-5/2}<\infty.
\]

Combine this with Stirling decay from \(e^{z^2}\) on vertical lines to justify
the double-series/integral interchange. For the later sum, record the direct
majorant

\[
 \sum_{m,n\ge1}\frac1{\sqrt{mn}}
 \left(1+\frac{mn}{T}\right)^{-A}<\infty
 \qquad(A>1/2),
\]

including the divisor-sum rewrite by \(k=mn\).

- [ ] **Step 6: Prove the stated weight-derivative form or weaken it**

Under `### 2.3 Uniform weight bounds`, differentiate the Mellin integral and
record exactly which powers of \(z\), polygamma factors, and \(T^{-1}\) factors
occur. If the derivation only gives

\[
 x^jT^k|\partial_x^j\partial_t^kV_t(x)|
 \ll_{A,j,k}(1+x/T)^{-A}T^{\epsilon_{j,k}},
\]

replace (2.5) and every downstream use by that proved form. Do not retain the
stronger statement solely because it is standard.

- [ ] **Step 7: Recheck the shifted-divisor sum and dyadic partition**

In Section 3, add the finite/absolute convergence justification for opening
the mollifier sum, separating \(me=nd\), and inserting
\(\sum_jF(x/2^j)=1\). State that for each fixed positive integer variable only
finitely many dyadic factors are nonzero, so the partition has no endpoint
term.

- [ ] **Step 8: Run the document contract and the entire focused test file**

```bash
uv run --with pytest pytest tests/test_mwkf_range_audit.py -v
git diff --check
```

Expected: all tests PASS and `git diff --check` is silent.

- [ ] **Step 9: Commit the AFE audit**

```bash
git add docs/research/2026-08-24-mobius-weighted-off-diagonal.md \
  tests/test_mwkf_range_audit.py
git commit -m "docs(research): audit exact mollified AFE"
```

---

### Task 3: Audit Poisson summation and the zero-mode main term

**Files:**
- Modify: `docs/research/2026-08-24-mobius-weighted-off-diagonal.md:313-443`
- Modify: `tests/test_mwkf_range_audit.py`

**Interfaces:**
- Consumes: the audited AFE/shifted-divisor formula from Task 2 and the LCM normalization from PR #478.
- Produces: a common-Mellin-integral derivation of the diagonal plus zero mode, an exact nonzero-mode formula with all normalizing factors, and a status label that says either `proved after audit` or `conditional/corrected` rather than silently preserving the baseline claim.

- [ ] **Step 1: Add failing status and derivation-marker tests**

Append:

```python
def test_research_note_exposes_poisson_audit_ledger() -> None:
    text = NOTE.read_text()
    for marker in (
        "### 4.1 Residue class and Poisson normalization",
        "### 4.2 Zero mode from a common Mellin integral",
        "### 4.3 Residue and main-term normalization",
    ):
        assert marker in text
    assert "zero-mode audit result:" in text
```

- [ ] **Step 2: Run the new test and verify failure**

```bash
uv run --with pytest pytest \
  tests/test_mwkf_range_audit.py::test_research_note_exposes_poisson_audit_ledger -v
```

Expected: FAIL because the Section 4 audit headings do not exist.

- [ ] **Step 3: Derive the residue class and Poisson factor**

Starting from

\[
 m_1s-m_2r=\delta,
\]

derive

\[
 m_2\equiv-\bar r\delta\pmod s,
 \qquad m_1=(m_2r+\delta)/s.
\]

Apply the residue-class Poisson formula

\[
 \sum_{n\equiv b\ (s)}f(n)
 =\frac1s\sum_{h\in\mathbb Z}e(hb/s)\widehat f(h/s)
\]

with the Fourier convention displayed in the note. Multiply it by the
original mollifier factor \(2/(q\sqrt{rs})\) and verify the final coefficient
\(2/(q\sqrt{rs}\,s)\) and phase \(e(-h\delta\bar r/s)\).

- [ ] **Step 4: Put the diagonal and zero mode over a common Mellin kernel**

Under `### 4.2 Zero mode from a common Mellin integral`, perform these steps
in the displayed order:

1. Sum the dyadic \(K,M\) weights before Mellin inversion.
2. Write the \(h=0\) integral with the positivity condition
   \(xr+\delta>0\) still present.
3. Insert the definition of \(V_t\) on an initial line where the \(x\)-integral
   and \(\delta\)-sum are absolutely convergent.
4. Evaluate the \(x\)-integral and the signed \(\delta\ne0\) Dirichlet series,
   retaining all gcd restrictions inherited from \((r,s)=1\).
5. Display the completed functional equation used to move the resulting
   Dirichlet series to the \(-c\) line.
6. Compare the resulting Euler factors with the diagonal integral term by
   term.

The derivation is accepted only if it reproduces (4.6b) including its sign,
factor 2, \(d^*e^*\)-power, and zeta argument. If it produces an additional
Euler factor, pole, or boundary term, replace (4.6b), (4.6), (4.7), and (4.8)
with the corrected formulas in the same task.

- [ ] **Step 5: Recompute the residue at \(z=0\)**

Use the expansions

\[
 \zeta(1+2z)=\frac1{2z}+\gamma+O(z),\qquad
 (d^*e^*)^{-z}=1-z\log(d^*e^*)+O(z^2),
\]

\[
 g_t(z)=1+z\lambda(t)+O_t(z^2),\qquad G_t(z)=1+O_t(z^2),
\]

and verify that the coefficient of \(z^{-1}\) after the outer `1/z` is

\[
 \frac12\bigl(\lambda(t)-\log(d^*e^*)+2\gamma\bigr).
\]

Cross-check \(d^*e^*=de/(d,e)^2\) against the LCM main-term note.
Read the note without merging PR #478:

```bash
git show \
  origin/codex/docs-selberg-lcm-main-term-20260824:docs/research/2026-08-24-selberg-mobius-lcm-main-term.md \
  | rg -n 'c_T|log\(d,e\)|2\.10|main constant|主常数'
```

Expected: the displayed LCM logarithm uses
\(2\log(d,e)-\log d-\log e\), matching
\(-\log(d^*e^*)\).

- [ ] **Step 6: Record the zero-mode audit outcome explicitly**

Write a status sentence after the derivation using exactly one of these
prefixes:

```text
zero-mode audit result: proved after audit;
```

or

```text
zero-mode audit result: the baseline identity required correction;
```

Complete the selected sentence with the actual equation numbers introduced
during the edit and, for the correction case, the name of every remaining
term.

- [ ] **Step 7: Run focused and full tests**

```bash
uv run --with pytest pytest \
  tests/test_mwkf_range_audit.py::test_research_note_exposes_poisson_audit_ledger -v
uv run --with pytest pytest tests/test_mwkf_range_audit.py -v
git diff --check
```

Expected: all tests PASS; `git diff --check` is silent.

- [ ] **Step 8: Commit the Poisson audit**

```bash
git add docs/research/2026-08-24-mobius-weighted-off-diagonal.md \
  tests/test_mwkf_range_audit.py
git commit -m "docs(research): audit zero Poisson mode"
```

---

### Task 4: Verify effective ranges and choose the weakest sufficient gate

**Files:**
- Modify: `scripts/audit_mwkf_ranges.py`
- Modify: `tests/test_mwkf_range_audit.py`
- Modify: `docs/research/2026-08-24-mobius-weighted-off-diagonal.md:445-669`

**Interfaces:**
- Consumes: the corrected nonzero-mode kernel from Task 3 and `ExponentBox` from Task 1.
- Produces:
  - `derived_bounds(box) -> dict[str, Fraction]` with keys `a`, `a_cap`, `m_cap`, `k_cap`;
  - `main() -> None`, printing deterministic witness diagnostics;
  - deterministic checks of the balanced and unbalanced boundary boxes;
  - a Section 6 comparison of uniform-separated, integrated-separated, and coupled-kernel gates;
  - one accepted gate with an explicit implication to the global remainder.

- [ ] **Step 1: Add failing tests for derived range identities**

Extend the imports with `derived_bounds` and append:

```python
def test_derived_bounds_match_the_written_polytope() -> None:
    for box in boundary_witnesses().values():
        bounds = derived_bounds(box)
        assert bounds["a"] == box.ell + box.h
        assert bounds["a"] <= bounds["a_cap"]
        assert box.m <= bounds["m_cap"]
        assert box.k <= bounds["k_cap"]


def test_balanced_box_exhibits_the_long_a_gap() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert box.third_length == F(5)
    assert (box.rho + box.sigma) / 2 == F(3)
    assert box.third_length - (box.rho + box.sigma) / 2 == F(2)
```

- [ ] **Step 2: Run and verify the missing-interface failure**

```bash
uv run --with pytest pytest \
  tests/test_mwkf_range_audit.py::test_derived_bounds_match_the_written_polytope \
  tests/test_mwkf_range_audit.py::test_balanced_box_exhibits_the_long_a_gap -v
```

Expected: FAIL during import because `derived_bounds` does not exist.

- [ ] **Step 3: Implement exact derived bounds**

Add:

```python
def derived_bounds(box: ExponentBox) -> dict[str, Fraction]:
    half = Fraction(1, 2)
    return {
        "a": box.third_length,
        "a_cap": box.rho + box.sigma - 1,
        "m_cap": half * (1 + box.sigma - box.rho),
        "k_cap": half * (1 + box.rho - box.sigma),
    }
```

Document that `m_cap` and `k_cap` follow by combining
\(k+m\le1\) with \(k+\sigma=m+\rho\).

- [ ] **Step 4: Run range tests and verify pass**

```bash
uv run --with pytest pytest tests/test_mwkf_range_audit.py -v
```

Expected: all tests PASS.

- [ ] **Step 5: Re-derive every effective cutoff from the coupled kernel**

In Section 5, provide one integration-by-parts operator for the \(t\)-phase
and one for the Poisson Fourier phase. Use them to derive, with dyadic support
constants retained:

\[
 KM\ll T^{1+\eta},\quad KS\asymp MR,
\]

\[
 |\delta|\ll MRT^{-1+\eta},\quad
 |h|\ll SM^{-1}T^\eta.
\]

Then derive \(LH\ll RST^{-1+2\eta}\), the nonempty-box lower bounds, and
the exact box normalization. If the kernel derivatives introduce additional
powers beyond \(T^{O(\eta)}\), update the range ledger and tests before
continuing.

- [ ] **Step 6: Compare the three gates without taking an early absolute value**

Add `### 6.1 Gate comparison` and write all three candidate inequalities in
the normalization of the corrected box formula:

1. a supremum over separated \(x,y\);
2. an integral of separated sums weighted by the actual transform norm;
3. the original coupled-kernel sum.

For each direction used, display the inequality (Fourier inversion,
Mellin inversion, Minkowski, or Cauchy--Schwarz) and its transform norm.
Choose the weakest candidate whose bound by \(RS T^\varepsilon\) yields
\(T^{1+\varepsilon}/q\) per box and a summable \(q\)-series after dyadic
aggregation.

- [ ] **Step 7: Add deterministic boundary-box diagnostics**

Run the script directly:

```bash
python3 scripts/audit_mwkf_ranges.py
```

Implement a `main()` that prints the witness name, all seven exponents,
`a`, and `a - (rho + sigma) / 2` in sorted witness-name order. Copy the
balanced and unbalanced output into a non-proof diagnostic table in Section
6. The table must label the \(T^2\) balanced long-\(a\) gap as a failure of
the arbitrary-coefficient BCR conjectural range, not as a counterexample to
the coupled structured gate.

- [ ] **Step 8: State the accepted gate and global implication**

Replace the current unconditional wording around MWKF(3) with exactly one of
these complete status lines:

```text
Accepted local gate after exact audit: uniform-separated.
Accepted local gate after exact audit: integrated-separated.
Accepted local gate after exact audit: coupled-kernel.
```

Keep only the selected alternative and its proved implication to the global
remainder in the theorem-style box. Preserve the other two as comparison
statements, not assumptions silently used later.

- [ ] **Step 9: Run tests and commit**

```bash
uv run --with pytest pytest tests/test_mwkf_range_audit.py -v
python3 scripts/audit_mwkf_ranges.py
git diff --check
git add scripts/audit_mwkf_ranges.py tests/test_mwkf_range_audit.py \
  docs/research/2026-08-24-mobius-weighted-off-diagonal.md
git commit -m "docs(research): validate MWKF local gate"
```

Expected: tests PASS, witness output is deterministic, and the commit changes
only the three planned files.

---

### Task 5: Final proof-status and source audit

**Files:**
- Modify: `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`
- Modify: `tests/test_mwkf_range_audit.py`

**Interfaces:**
- Consumes: all audited statements from Tasks 1--4.
- Produces: a self-contained Phase-1 result classified as exact reduction,
  corrected reduction, or blocked audit; a clean branch ready for the
  published-estimate coverage plan.

- [ ] **Step 1: Add the final status-contract test**

Append:

```python
def test_research_note_has_one_honest_phase_one_classification() -> None:
    text = NOTE.read_text()
    labels = (
        "Phase-1 classification: exact reduction verified",
        "Phase-1 classification: corrected reduction verified",
        "Phase-1 classification: exact reduction remains blocked",
    )
    assert sum(label in text for label in labels) == 1
    assert "Accepted local gate after exact audit:" in text
    assert "arXiv:2601.00292" in text
    assert "withdrawn" in text.lower()
```

- [ ] **Step 2: Run and verify failure before the classification is written**

```bash
uv run --with pytest pytest \
  tests/test_mwkf_range_audit.py::test_research_note_has_one_honest_phase_one_classification -v
```

Expected: FAIL because no Phase-1 classification line exists.

- [ ] **Step 3: Reconcile the proved/not-proved ledger**

Rewrite Section 8 so each item cites the equation range containing its full
derivation. Select exactly one classification label from the test based on
the actual Task 2--4 outcome. If the zero-mode derivation remains blocked,
the accepted local gate must be described as provisional and no equation may
claim a complete exact decomposition.

- [ ] **Step 4: Update primary-source status**

Add Thomas Wright's August 2026 v2 paper as a future Region-C input, with no
claim that it already covers the polytope. Add arXiv:2601.00292 only in a
warning that it was withdrawn after a missing \(L^2\) factor was reported.
Retain BCR, Radziwiłł, and Pratt--Robles with the exact length ranges used in
the note.

- [ ] **Step 5: Run the complete focused verification**

```bash
set -e
uv run --with pytest pytest tests/test_mwkf_range_audit.py -v
python3 scripts/audit_mwkf_ranges.py
git diff --check
test -z "$(git diff --name-only HEAD | grep -vE '^(docs/research/2026-08-24-mobius-weighted-off-diagonal.md|scripts/audit_mwkf_ranges.py|tests/test_mwkf_range_audit.py)$')"
```

Expected: all tests PASS, range output is deterministic, whitespace audit is
silent, and the current task has not changed a file outside the three
implementation artifacts.

- [ ] **Step 6: Review the mathematical diff from beginning to end**

```bash
git diff HEAD -- docs/research/2026-08-24-mobius-weighted-off-diagonal.md
rg -n 'exact|under audit|unproved|conditional|classification|MWKF' \
  docs/research/2026-08-24-mobius-weighted-off-diagonal.md
```

Expected: every use of `exact` points to a derivation; the local analytic
gate is still labeled unproved unless this slice unexpectedly proves it.

- [ ] **Step 7: Commit the Phase-1 audit result**

```bash
git add docs/research/2026-08-24-mobius-weighted-off-diagonal.md \
  tests/test_mwkf_range_audit.py
git commit -m "docs(research): finalize off-diagonal exact audit"
```

- [ ] **Step 8: Record the handoff to the next research slice**

Run:

```bash
git status --short --branch
git log --oneline --decorate -6
```

Expected: clean worktree, with the five implementation commits after this
plan commit. The next plan consumes the accepted gate and builds the
published-estimate coverage table; it does not reopen the exact reduction
unless review finds a concrete defect.
