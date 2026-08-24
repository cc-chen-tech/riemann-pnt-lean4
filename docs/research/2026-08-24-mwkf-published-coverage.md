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

Smooth Poisson summation in \(h\) is an exact identity at every relative
scale; it is not restricted to \(H\geq S\).  For fixed \(r,s,\delta\),
write the coupled normalized \(h\)-weight as \(u(h/H)\), with Fourier
transform \(\widehat u(\xi)=\int u(x)e(-x\xi)\,dx\).  Then

\[
 \sum_{h\in\mathbb Z}u(h/H)e\!\left(-\frac{h\delta\bar r}s\right)
 =H\sum_{k\in\mathbb Z}
 \widehat u\!\left(H\left(k+\frac{\delta\bar r}s\right)\right).
\tag{3.1}
\]

Put

\[
 v=k s+\delta\bar r.
\tag{3.2}
\]

The right side of (3.1) is therefore an infinite smooth sum over

\[
 rv\equiv\delta\pmod s,
 \qquad
 \delta=rv-js,\quad j\in\mathbb Z,
\tag{3.3}
\]

with transform argument \(Hv/s\).  Repeated integration by parts in the
normalized \(h\)-variable gives the effective dual range

\[
 |v|\leq \frac SH\mathscr L^C,
 \qquad
 |j|\leq
 4\frac RH\mathscr L^C+4\frac LS,
\tag{3.4}
\]

while the complement remains an explicit transform tail.  Hence the exact
zero-slack dual exponents are

\[
 v_{\rm dual}=\max(0,\sigma-h),
 \qquad
 j_{\rm dual}=\max(0,\rho-h,\ell-\sigma).
\tag{3.5}
\]

For the balanced maximal witness both are \(1/2\).  Poisson summation in
\(\delta\) has the analogous dual exponent
\(\max(0,\sigma-\ell)=1/2\), with the nonlinear logarithmic phase retained
inside its coupled Fourier transform.

No cited theorem in the current source set bounds the shifted equation
(3.3), with its original Möbius weights and coupled transform, by the saving
(1.1).  Accordingly both adapters return
`no_cited_completed_kernel_bound`.  The correction is that short-frequency
boxes now expose a nonempty short dual sum instead of being rejected as
kinematically unavailable.

For the actual coupled box, let \(\widehat\Psi_h\) denote the Fourier
transform only in its normalized \(h/H\) coordinate, including the smooth
dyadic \(h\)-cutoff.  Equations (3.1)--(3.3) give the exact identity

\[
 \mathfrak S_q[\Psi]=H\,\mathfrak C_q[\widehat\Psi_h],
\tag{3.6}
\]

where

\[
\begin{aligned}
 \mathfrak C_q[\widehat\Psi_h]
 :={}&\sum_{\substack{r\asymp R,\ s\asymp S,\\
                      \delta\asymp L,\ v,j\in\mathbb Z\\
                      \delta=rv-js\\
                      (r,s)=1,\ (q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\\
 &\quad\times
 \widehat\Psi_h\!\left(
  \frac rR,\frac sS,\frac\delta L,\frac{Hv}s
 \right).
\end{aligned}
\tag{3.7}
\]

The Fourier transform in (3.7) is not compactly supported; its rapid decay
is retained in the displayed weight, so (3.6) has no truncation remainder.
The exact local inequality sufficient for the accepted coupled-kernel gate
is therefore

\[
 \boxed{\mathrm{SM}_{1/1000}:\qquad
 |\mathfrak C_q[\widehat\Psi_h]|
 \ll_W \frac{RS}{H}T^{-1/1000}.}
\tag{3.8}
\]

At the balanced maximal witness, (3.4) gives

\[
 r,s\sim T^3,\qquad
 |v|,|j|\ll T^{1/2}\mathscr L^C,\qquad
 |\delta|\sim T^{5/2},
\tag{3.9}
\]

and (3.8) is the explicit bound

\[
 |\mathfrak C_q[\widehat\Psi_h]|
 \ll_W T^{7/2-1/1000}.
\tag{3.10}
\]

The zero-slack lattice-volume exponent of (3.7) is \(6\): the four free
scales contribute \(3+3+1/2+1/2\), while the window
\(|rv-js|\sim T^{5/2}\) inside products of scale \(T^{7/2}\) imposes one
power of codimension.  Thus square-root cancellation would have exponent
\(3\), leaving a margin \(1/2-1/1000\) over (3.10).  This volume comparison
is only a target ledger, not a proof of cancellation.

Writing \(v=g v_0\), \(j=g j_0\), \((v_0,j_0)=1\), and requiring
\(g\mid\delta\), every solution can be parameterized exactly as

\[
 r=r_0+j_0t,\qquad s=s_0+v_0t,
 \qquad v_0r_0-j_0s_0=\delta/g.
\tag{3.11}
\]

The fixed bounded dual box \(v=j=1\) is already a sharp obstruction to a
routine use of averaged Chowla.  In this box (3.3) becomes

\[
 \delta=r-s,
\tag{3.12}
\]

and its exact contribution is

\[
\begin{aligned}
 \mathfrak C_{q;1,1}
 :={}&\sum_{\substack{s\asymp S,\ \delta\asymp L\\
                      s+\delta\asymp R\\
                      (s,\delta)=1,\ (q,s(s+\delta))=1}}
 \mu(s+\delta)\mu(s)
 p_N(q(s+\delta))p_N(qs)\\
 &\quad\times
 \widehat\Psi_h\!\left(
  \frac{s+\delta}{R},\frac sS,\frac\delta L,\frac Hs
 \right).
\end{aligned}
\tag{\mathrm{RES}_{1,1}}
\]

For \(R=S=T^3\) and \(L=T^{5/2}\), this box has lattice-volume scale

\[
 RL=T^{11/2},
\tag{3.13}
\]

whereas its dyadic local version of (3.8) asks for

\[
 |\mathfrak C_{q;1,1}|
 \ll_W T^{7/2-1/1000}.
\tag{3.14}
\]

Thus this cell requires the explicit saving \(T^{2+1/1000}\) over its
volume bound.  Square-root cancellation has exponent \(11/4\), which is
stronger than (3.14) by \(3/4-1/1000\).

For comparison, inserting \(X=T^3\) and shift range \(H_0=T^{5/2}\)
into Matomäki--Radziwiłł--Tao, arXiv:1503.05121, Theorem 1.1, has the
quantitative scale

\[
 T^{11/2}
 \left(
  \frac{\log\log T}{\log T}
  +\frac1{\log^{1/3000}T}
 \right),
\tag{3.15}
\]

before the extra coprimality and coupled weights in
\(\mathrm{RES}_{1,1}\) are addressed.  This is an explicit logarithmic
improvement at exponent \(11/2\), not the two-power saving in (3.14).
Consequently the bounded-dual resonance cell remains uncovered even before
the growing slopes in (3.11) are considered.

This identifies (3.8) as an averaged two-linear-form Möbius correlation
with slopes as large as \(T^{1/2}\).  Matomäki--Radziwiłł--Tao,
arXiv:1503.05121, Theorem 1.6, has a factor \(A^{2k}\) for slopes bounded
by \(A\) and supplies logarithmic rather than the required \(T^{5/2}\)
reduction from the volume exponent.  Consequently it is not an adapter for
(3.8).  The remaining new input can now be stated as the single shifted
Möbius inequality \(\mathrm{SM}_{1/1000}\), with transform-tail seminorms
kept uniform.

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
