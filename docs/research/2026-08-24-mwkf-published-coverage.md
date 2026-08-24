# Published-estimate coverage of the MWKF polytope

## 1. Scope and status

This note consumes the corrected core-box formula (5.15) and the exact
zero-slack variables

\[
 (\rho,\sigma,m,k,\ell,h,\kappa),\qquad a=\ell+h,
\]

from `2026-08-24-mobius-weighted-off-diagonal.md`.  Its target is the fixed
local saving

\[
 |\mathfrak S_q[\Psi]|\ll RS T^{-1/1000}.
\tag{1.1}
\]

Every comparison below is exact rational linear algebra.  The Python report
is a regression ledger, not an analytic proof.  In particular, this note
does not claim that the published theorems cover all core boxes.

## 2. Exact BCR adapter

Apply Bettin--Chandee, arXiv:1502.00769, Theorem 1, with

\[
 M=R,\qquad N=S,\qquad A=T^a,
\]

and exact norm exponents

\[
 \|\alpha\|_2=T^{\rho/2},\quad
 \|\beta\|_2=T^{\sigma/2},\quad
 \|\nu\|_2\leq T^{a/2+o(1)}.
\]

Put \(u=\max(\rho,\sigma)\) and
\(p=\max(0,a-\rho-\sigma)\).  The two terms in the published theorem have
exponents

\[
 E_1=\frac{17}{20}(a+\rho+\sigma)+\frac14u+\frac12p,
\tag{2.1}
\]

\[
 E_2=a+\frac78(\rho+\sigma)+\frac18u+\frac12p.
\tag{2.2}
\]

Thus the exact saving returned by the adapter is

\[
 s_{\rm BC}=\rho+\sigma-\max(E_1,E_2).
\tag{2.3}
\]

The core relation \(a\leq\rho+\sigma-1\) makes \(p=0\).  The BCR primary
cell is therefore the intersection of the admissible polytope with the two
strict affine inequalities

\[
 \rho+\sigma-E_1>\frac1{1000},\qquad
 \rho+\sigma-E_2>\frac1{1000}.
\tag{2.4}
\]

The strict sign absorbs the fixed polylogarithmic separation norm.  The
hypothesis table is:

| published hypothesis | local realization | result |
|---|---|---|
| \(m,n,a\) dyadically supported | \(r,s,h\delta\) after smooth separation | satisfied |
| \((m,n)=1\) | \((r,s)=1\) | satisfied |
| arbitrary complex coefficients | Möbius and divisor-convolution coefficients | allowed but structure unused |
| \(L^2\) norms | the three norms displayed above | exact |
| fixed power saving (1.1) | (2.4) | only on the BCR cell |

For \((\rho,\sigma,a)=(1,1,0)\), (2.3) gives \(s_{\rm BC}=1/20\).
For the balanced maximal box \((3,3,5)\), it gives
\(s_{\rm BC}=-37/8\).

## 3. Completion adapters

Completion in \(h\) modulo \(s\) is kinematically available only when
\(h\geq\sigma\).  Since the core has \(h\leq\sigma-m\), this forces the
critical face

\[
 m=0,\qquad h=\sigma.
\tag{3.1}
\]

Completion in \(\delta\) is kinematically available on

\[
 \ell\geq\sigma,qquad
 \ell\leq m+\rho-1.
\tag{3.2}
\]

Neither kinematic condition is itself an estimate.  No cited theorem in the
current source set bounds the original coupled kernel on (3.1) or (3.2)
with the saving (1.1).  Accordingly the adapters return
`no_cited_completed_kernel_bound`; these faces remain residual rather than
being silently declared covered.

## 4. Wright fixed-factor adapter

Wright, arXiv:2604.25177v2, treats

\[
 e\!\left(\vartheta\frac{a\bar m}{nR_{\rm fix}}\right)
\]

with \(R_{\rm fix}\) fixed across the trilinear sum.  The base MWKF phase is
\(e(-a\bar r/s)\).  Its extracted common divisor \(q\) is absent from this
phase, so \(q\) cannot be used as \(R_{\rm fix}\).  Without a later
factorization \(s=nR_{\rm fix}\), the exact rejection reason is
`no_fixed_denominator_factor`.

For use after such a factorization, write the exponent of
\(R_{\rm fix}\) as \(f\), and put

\[
 M=T^\rho,\qquad N=T^{\sigma-f},\qquad A=T^a.
\]

The adapter encodes the displayed v2 theorem term by term, including
\(M\ll N^2\), \(R_{\rm fix}\ll M^C\), the factor
\((1+A/(MN))^{1/4}\), and all five bracket exponents.  It uses the
\(A^{-1/20}\) exponent in the published theorem statement.  This adapter is
available to a later Type-I factorization, but it covers no base cell before
that factor has actually been fixed.

## 5. Exact residual witnesses

The deterministic report is:

| witness | primary route | BCR saving | reason |
|---|---|---:|---|
| bcr_small_a | BCR | \(1/20\) | covered |
| balanced_max_a | Möbius Type I/II | \(-37/8\) | published routes exhausted |
| large_q_endpoint | Möbius Type I/II | \(-7/8\) | published routes exhausted |
| r_long | Möbius Type I/II | \(-15/4\) | published routes exhausted |
| s_long | Möbius Type I/II | \(-15/4\) | published routes exhausted |

The routing priority is BCR, completion, Wright fixed-factor, then Möbius
Type I/II.  A route becomes primary only when its analytic estimate—not
merely its kinematic condition—is available.  Hence the completion faces
and all base Wright calls currently flow to the residual route.

**published coverage result: residual cells remain.**  In particular, the
balanced witness has a fixed positive deficit of \(37/8\), and the separate
tail obligation \(\mathrm{TAIL}_{B,D}\) is also uncovered.  The next slice
must prove a new Möbius Type I/II estimate; a zero-residual coverage report
cannot be produced from the cited results.
