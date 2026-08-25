# Möbius Region-D Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox syntax for tracking.

**Goal:** Give an exact finite Möbius decomposition that preserves \(a=h\delta\) and the second Möbius weight, audit the resulting fixed-factor Type-I route against Wright's theorem, and isolate the precise averaged Type-II estimate still needed.

**Architecture:** A standard-library Python module will verify the finite Dirichlet-convolution identity and compute exact rational savings for the factorized Wright route. The research note will prove the identity algebraically, translate every fixed-factor theorem parameter, and retain the unsummed \(u,r,n,h,\delta\) expression as the next analytic interface.

**Tech Stack:** Python 3 fractions.Fraction, finite Dirichlet convolution, pytest, Markdown/LaTeX.

**Spec:** docs/superpowers/specs/2026-08-24-mobius-weighted-off-diagonal-design.md

## Global Constraints

- Do not replace either Möbius weight by an arbitrary bounded coefficient before the exact decomposition is displayed.
- Keep the phase \(e(-h\delta\overline r/s)\) and the coupled kernel.
- Wright's theorem may be used only with its fixed denominator \(R_0\), size hypotheses, and all five terms.
- A failed Type-I route is not the failure of CK\(_{\rm ub}(3)\); the remaining Type-II average must be stated explicitly.

---

### Task 1: Finite Möbius geometric identity

**Files:**
- Create: scripts/audit_mobius_type_ii.py
- Create: tests/test_mobius_type_ii_audit.py

**Interfaces:**
- Produces: mobius(n), short_mobius(n, cutoff), c_coefficient(n, cutoff), mobius_geometric_value(n, cutoff, depth).

- [ ] Write a failing test that checks
  \[
  \mu(n)=\sum_{j=0}^{J-1}(-1)^j(\mu_{\le U}*c_U^{*j})(n)
  \quad(n\le U^J),
  \]
  for every \(1\le n\le200\), \(U\in\{2,3,5\}\), and the least \(J\) with \(U^J\ge200\).
- [ ] Run uv run --with pytest pytest -q tests/test_mobius_type_ii_audit.py and verify failure because the module is absent.
- [ ] Implement exact finite convolution with
  \[
  c_U=\mathbf1*\mu_{\le U}-\delta_1,
  \qquad c_U(n)=0\quad(n\le U).
  \]
- [ ] Re-run the focused test and verify pass.

### Task 2: Factorized Wright savings

**Files:**
- Modify: scripts/audit_mobius_type_ii.py
- Modify: tests/test_mobius_type_ii_audit.py

**Interfaces:**
- Consumes: ExponentBox.
- Produces: wright_factor_savings(box, tau) and wright_factor_covers(box, tau).

- [ ] Write failing literal-value tests for the five savings
  \[
  \begin{aligned}
  d_1&=\sigma/8-a-3\tau/8,\\
  d_2&=\rho/4-\sigma/8-a-\tau/4,\\
  d_3&=3\sigma/20-\rho/10-19a/20-\tau/4,\\
  d_4&=\rho/5-3\sigma/20-17a/20-\tau/10,\\
  d_5&=\rho/2-3\sigma/8-a+\tau/8.
  \end{aligned}
  \]
- [ ] Verify the tests fail because the interface is absent.
- [ ] Implement the five exact fractions and enforce Wright's \(X\ll Y^2\) condition \(\rho\le2(\sigma-\tau)\).
- [ ] Test that the balanced maximal-\(a\) witness is uncovered for every rational \(0\le\tau\le3/2\), and that \(d_1\le\sigma/8-a\).
- [ ] Re-run all focused tests.

### Task 3: Written Type-I/II interface

**Files:**
- Modify: docs/research/2026-08-24-mobius-weighted-off-diagonal.md

**Interfaces:**
- Consumes: Tasks 1--2.
- Produces: exact equations for the decomposition and the residual averaged fixed-factor sum.

- [ ] Prove \(\mu*(\delta_1+c_U)=\mu_{\le U}\), iterate it \(J\) times, and use \(\operatorname{supp}(c_U)\subset(U,\infty)\) to kill the remainder on \(n\le U^J\).
- [ ] Substitute the identity into only the \(s\)-Möbius weight of (6.0), leaving \(\mu(r)\), \(h\), \(\delta\), and \(\Psi\) intact.
- [ ] For the Type-I endpoint \(s=un\), write Wright's variables \(X=R\), \(Y=S/U\), \(R_0=u\), \(A=LH\), include the \(\ell^1\) cost \(U\), and derive all five savings.
- [ ] State the residual Type-II object before absolute values:
  \[
  \sum_{u\asymp U}\lambda_u
  \sum_{r,n,h,\delta}\mu(r)\beta_{u}(n)
  \Psi(r/R,un/S,\delta/L,h/H)
  e(-h\delta\bar r/(un)).
  \]
- [ ] Record the balanced witness and the exact missing \(T^{37/8}\) saving from the decisive arbitrary-\(a\) term.

### Task 4: Verification and commit

- [ ] Run uv run --with pytest pytest -q tests/test_mobius_type_ii_audit.py tests/test_mwkf_coverage_audit.py tests/test_mwkf_range_audit.py.
- [ ] Run both audit scripts and git diff --check.
- [ ] Audit all uses of proved, unproved, Type I, Type II, Wright, and CK_ub.
- [ ] Commit with message docs(research): isolate residual Mobius Type II gate.
