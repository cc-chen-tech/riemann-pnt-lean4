# Möbius-weighted \(T^3\) off-diagonal research design

## Goal

For

\[
 M_N(s)=\sum_{n\le N}\frac{\mu(n)}{n^s}
 \left(1-\frac{\log n}{\log N}\right),
 \qquad N=T^3,
\]

study the smoothed twisted second moment

\[
 I_{N,W}(T)=\int_{\mathbb R}
 |\zeta(\tfrac12+it)|^2|M_N(\tfrac12+it)|^2W(t/T)\,dt
\]

and attempt to prove the unconditional upper bound

\[
 I_{T^3,W}(T)\ll_{\varepsilon,W}T^{1+\varepsilon}.
\]

The already completed LCM calculation proves that the proposed arithmetic
main term has size \(O_{\varepsilon,W}(T^{1+\varepsilon})\). This design is
only about the off-diagonal remainder.

The target is beyond the range of currently cited unconditional twisted
second-moment theorems. It is therefore a research target, not a promised
routine implementation. Every delivered statement must distinguish among:

1. exact finite or absolutely convergent identities proved in the note;
2. applications of named published theorems whose hypotheses are checked;
3. numerical or symbolic diagnostics that are evidence only;
4. new analytic inequalities that remain unproved.

## Existing baseline

The branch `codex/docs-mobius-weighted-offdiagonal-20260824` contains

```text
docs/research/2026-08-24-mobius-weighted-off-diagonal.md
```

which proposes the chain

\[
 I_{N,W}(T)
 \longrightarrow \text{exact AFE}
 \longrightarrow \text{shifted divisor boxes}
 \longrightarrow \text{Poisson modes}
 \longrightarrow \operatorname{MWKF}(3).
\]

The note identifies the structured local sum

\[
\begin{aligned}
 \mathfrak T_q(R,S;L,H;x,y)
 ={}&\sum_{a\ne0}\nu_{x,y}(a)
 \sum_{\substack{r\asymp R,\ s\asymp S\\
                  (r,s)=(q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\\
 &\qquad\qquad\times U_1(r/R)V_1(s/S)
 e\!\left(-\frac{a\bar r}{s}\right),
\end{aligned}
\]

where

\[
 \nu_{x,y}(a)=\sum_{h\delta=a}
 U(h/H)V(\delta/L)e(-hx+\delta y/(2\pi)).
\]

It then proposes the local bound

\[
 |\mathfrak T_q(R,S;L,H;x,y)|
 \ll_{\varepsilon,W}RS\,T^\varepsilon
 \tag{MWKF(3)}
\]

as a sufficient input. The baseline does not prove this inequality. Before
using it as the final gate, the derivation and the strength of its uniformity
must be audited.

## Non-goals

This research slice does not:

- claim Farmer's all-length mollifier conjecture;
- use a withdrawn preprint as an analytic input;
- replace an unconditional goal by RH, Lindelöf, pair correlation, or a
  ratios conjecture without changing the theorem label to conditional;
- create a Lean axiom named after MWKF(3) and then report the target closed;
- formalize gamma factors, Poisson summation, or Kuznetsov before the analytic
  statement and its parameter range are stable;
- modify the already merged LCM main-term calculation except to cross-link
  the off-diagonal status.

## Phase 1: exact-reduction audit

### Exact approximate functional equation

Re-derive the pole-cancelled contour identity for
\(|\zeta(\tfrac12+it)|^2\). The audit must explicitly record:

- the definition of the meromorphic completion used;
- all four moving poles and the zeros that cancel them;
- decay on both vertical lines;
- the orientation and factor of two after applying the functional equation;
- absolute convergence sufficient for expanding both zeta factors and for
  interchanging the integral with the double Dirichlet series;
- uniform derivative bounds for the resulting weight \(V_t(x)\).

No pointwise approximate-functional-equation error may be multiplied by the
length-\(T^3\) mollifier.

### Diagonal and zero Poisson mode

The highest-risk identity in the baseline is that the original diagonal plus
all zero Poisson modes equals the LCM quadratic main term. The revised note
must derive this identity from a common Mellin integral. In particular it
must show:

- how the \(\delta\ne0\) sum is formed after Poisson summation;
- every gcd and coprimality factor in its Dirichlet series;
- the initial half-plane of absolute convergence;
- the exact functional-equation transformation;
- every pole crossed when shifting the contour;
- the residue producing
  \(\lambda(t)-\log(de/(d,e)^2)+2\gamma\);
- why the dyadic partition sums to one without a boundary remainder.

If extra Euler factors or residues appear, the main-term identity and all
downstream normalizations must be corrected before any Kloosterman estimate
is attempted.

### Nonzero Poisson modes

For \(d=qr\), \(e=qs\), \((r,s)=1\), re-check Poisson summation in the zeta
variable. The accepted formula must retain:

- the factor \(2/(q\sqrt{rs}\,s)\);
- the residue class \(m_2\equiv-\bar r\delta\pmod s\);
- the phase \(e(-h\delta\bar r/s)\);
- the exact logarithm \(t\log(1+\delta/(m_2r))\);
- the positivity restriction on the reconstructed \(m_1\);
- the complete smooth kernel rather than a Taylor approximation.

### Effective ranges

With

\[
 R=T^\rho,\ S=T^\sigma,\ M=T^m,\ K=T^k,
 \ L=T^\ell,\ H=T^h,\ q=T^\kappa,
\]

the zero-slack exponent polytope recorded by the audit is

\[
\begin{gathered}
 \rho,\sigma,m,k,\ell,h,\kappa\ge0,\qquad
 \kappa+\rho\le3,\quad \kappa+\sigma\le3,\\
 k+m\le1,\qquad k+\sigma=m+\rho,\\
 0\le\ell\le m+\rho-1,\qquad
 0\le h\le\sigma-m,\\
 a:=\ell+h\le\rho+\sigma-1.
\end{gathered}
\]

The paper proof will retain the dyadic constants and \(T^{O(\eta)}\)
slack. A small exact-rational checker may verify algebraic implications and
produce witness boxes, but it is a regression tool and not a substitute for
the written inequalities.

## Phase 2: test whether MWKF(3) is the correct gate

The smooth separation that produces parameters \(x,y\) can strengthen the
required statement if absolute values are taken too early. The audit must
compare three candidate gates:

1. **Uniform separated gate:** MWKF(3) for every admissible \(x,y\).
2. **Integrated separated gate:** the same local sums after integration
   against the actual Fourier/Mellin transform norm of the kernel.
3. **Coupled-kernel gate:** a bound for the original four-variable smooth
   kernel before separating \(h,\delta,r,s\).

The weakest gate that still sums to
\(O_{\varepsilon,W}(T^{1+\varepsilon})\) is the accepted target. A stronger
uniform gate is retained only if its necessity is proved or if it follows
from the estimates used later.

Diagnostics will probe boundary boxes such as:

- balanced \(R\asymp S\) with maximal \(LH\);
- \(H\asymp S/M\), where completion in \(h\) may be effective;
- \(L\asymp MR/T\), where the archimedean \(\delta\)-phase has only bounded
  total variation;
- maximally unbalanced ratios allowed by \(KM\ll T\) and
  \(KS\asymp MR\);
- small \(q\) and large \(q\) endpoints.

Any counterexample to the uniform gate changes the gate; it does not refute
the original twisted-moment target.

## Phase 3: unconditional parameter-space decomposition

Every retained box is assigned to exactly one route. Overlaps are allowed,
but the final coverage table must name a primary route for each region.

### Region A: generic trilinear range

When the third-variable length satisfies the hypotheses of the published
Bettin--Chandee trilinear Kloosterman-fraction estimate, apply that theorem
with the exact \(L^2\) norms

\[
 \|\mu(r)p_N(qr)U_1(r/R)\|_2\ll R^{1/2},
 \quad
 \|\mu(s)p_N(qs)V_1(s/S)\|_2\ll S^{1/2},
 \quad
 \|\nu\|_2\ll A^{1/2+\varepsilon}.
\]

The output is an explicit inequality in
\((\rho,\sigma,m,k,\ell,h,\kappa)\), not the phrase “BCR applies.”

### Region B: completion in a factor of \(a=h\delta\)

When \(H\) is comparable with or longer than the modulus scale, complete the
\(h\)-sum modulo \(s\). When \(L\) is the favorable factor, reverse the roles
of \(h\) and \(\delta\). The calculation must retain the incomplete-interval
boundary and gcd \((\delta,s)\), respectively \((h,s)\), instead of assuming
complete cancellation.

This region is intended to recover the factorization information discarded
when \(\nu(a)\) is treated as an arbitrary sequence.

### Region C: unbalanced Kloosterman fractions

For strongly unbalanced \(R,S\), test the August 2026
partially-fixed-modulus estimate of Wright. Its divisor-boundedness,
Siegel--Walfisz, fixed-factor, and size hypotheses must be translated into
the present variables line by line. It is used only in the intersection of
the proven hypotheses with the effective polytope.

### Region D: Möbius Type I/II decomposition

In the remaining balanced or medium region, decompose one Möbius weight at a
time using a fixed, explicitly stated combinatorial identity. The resulting
Type I and Type II sums must keep the other Möbius weight and the product
phase \(h\delta\bar r/s\). Apply complementary-divisor, spectral-large-sieve,
or published Kloosterman bounds only after listing their exact lengths.

The decomposition parameters are optimized against the exponent polytope.
If the resulting inequalities leave a region uncovered, record a rational
witness point and the exact missing power of \(T\).

## Phase 4: result classification

The research has three legitimate terminal outcomes.

### Unconditional closure

Every effective box is covered with total contribution
\(O_{\varepsilon,W}(T^{1+\varepsilon})\). The final note contains the exact
reduction, the coverage table, the summation over dyadic variables and \(q\),
and the unconditional twisted-moment theorem.

### Correct conditional closure

The exact reduction is proved, but one explicitly named local inequality
remains. The final theorem is written as an implication from that inequality.
No abstract assumption is described as a consequence of BCR unless the
published theorem's hypotheses cover its whole range.

### Certified obstruction

Published estimates cover only part of the parameter polytope. The final
note gives:

- all covered regions;
- a rational witness box in every uncovered component;
- the best available exponent for that box;
- the exact power saving still required;
- whether the obstruction comes from the long \(a\)-range, incomplete
  completion, Möbius Type II sums, or loss caused by kernel separation.

This is a valid research result but not completion of the unconditional
twisted-moment target.

## Repository artifacts

The research implementation is limited initially to:

```text
docs/research/2026-08-24-mobius-weighted-off-diagonal.md
scripts/audit_mwkf_ranges.py
tests/test_mwkf_range_audit.py
```

The research note contains the mathematical proof and status ledger. The
Python script uses exact rational arithmetic to check stated linear exponent
implications and emit witness boxes. The test fixes known boundary boxes and
guards against silently weakening or enlarging the admissible polytope.

Lean work begins only after the exact reduction and accepted local gate have
survived the audit. The first possible Lean slice is finite arithmetic:

- gcd extraction \(d=qr,e=qs\);
- equivalence of the shifted equation and its residue class;
- finite dyadic reindexing after explicit truncation;
- implication from a finite local-box bound to a finite remainder bound.

Analytic Poisson summation, gamma-factor contour shifts, and the new
Kloosterman estimate remain outside Lean until suitable library interfaces
and genuinely proved inputs exist.

## Execution decomposition

This design is intentionally broader than one implementation plan. Work is
split into three reviewable slices, and a later slice does not start by
assuming the conclusions of an unreviewed earlier slice.

1. **Exact reduction and gate validation.** Audit the AFE, diagonal/zero-mode
   identity, nonzero Poisson formula, effective ranges, and the choice among
   the uniform, integrated, and coupled gates. This is the first executable
   plan and produces a corrected research note plus range-regression tests.
2. **Published-estimate coverage.** Build the exact exponent coverage table
   for Regions A--C, including primary-source hypothesis tables and rational
   witness boxes for every uncovered component.
3. **New structured estimate.** Attack only the residual Region D using the
   factorization \(a=h\delta\) and the two Möbius weights. This slice either
   closes the remaining boxes or produces the final certified obstruction.

Each slice receives its own implementation plan, verification record, and
review decision. A PR may combine the first two documentation-only slices if
their diffs remain coherent; a new analytic theorem or Lean formalization is
kept in a separate PR.

## Verification

The research branch is acceptable for review only after:

1. every equality labeled exact has a derivation with convergence or finite
   reindexing justification;
2. every external theorem has a primary-source citation and a hypothesis
   table;
3. the range checker passes with exact rational arithmetic;
4. every claimed coverage region has both a written inequality and a checker
   assertion;
5. boundary witness boxes are printed deterministically by the test suite;
6. searches for `MWKF(3)` distinguish proved uses from conditional uses;
7. the document states prominently whether the final result is
   unconditional, conditional, or an obstruction certificate;
8. the diff contains no new Lean axiom, `sorry`, `admit`, or theorem whose
   name overstates a conditional input.

## PR boundary

The off-diagonal PR is separate from the LCM main-term PR. It is opened only
after the exact-reduction audit is complete and the result classification is
known. Its title and summary must use one of these scopes:

- unconditional bound, if every box is proved;
- exact reduction to a named local gate, if conditional;
- parameter-range obstruction audit, if a gap remains.

The existing 783-line note is not published as a completed proof merely
because it defines MWKF(3).
