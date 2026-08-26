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

### 2.1 Exact mutually exclusive coverage cells

The accepted local gate requires a strict saving, not merely a
nonnegative exponent.  Put

\[
 \eta:=\frac1{1000},\qquad
 u:=\max(\rho,\sigma),\qquad
 v:=\min(\rho,\sigma),\qquad a:=\ell+h.
\tag{2.5}
\]

Equations (2.1)--(2.3) give the two exact BCR savings

\[
 s_1=\frac{3v-2u-17a}{20},\qquad
 s_2=\frac v8-a.
\tag{2.6}
\]

Because the theorem has a \(T^\varepsilon\) loss and the separated kernel
has polylogarithmic seminorm costs, its direct cell is

\[
 \boxed{s_{\rm BC}:=\min(s_1,s_2)>\frac1{1000}.}
\tag{2.7}
\]

Equality in (2.7) is not enough.  This corrects the older executable
predicate, which tested only \(s_1,s_2\geq0\).  For example, the admissible
box

\[
 (\rho,\sigma,m,k,\ell,h,\kappa)
 =\left(1,1,0,0,0,\frac{99}{1700},0\right)
\tag{2.8}
\]

has \(s_1=1/2000\) and \(s_2>1/1000\).  Its saving is positive but smaller than
the required threshold, so it is not a published-coverage cell.

Intersecting throughout with the admissible polytope from Section 5 of
the exact-audit note gives the following mutually exclusive table.  The
ordering convention assigns \(\rho=\sigma\) to the first wing.

| cell | exact additional conditions | route | proved? |
|---|---|---|---|
| A_rho_ge_sigma | \(\rho\geq\sigma\), \(s_1>\eta\), \(s_2>\eta\) | Bettin--Chandee Theorem 1 | yes |
| A_sigma_gt_rho | \(\sigma>\rho\), \(s_1>\eta\), \(s_2>\eta\) | Bettin--Chandee Theorem 1 | yes |
| B_ell_zero | not A, \(\ell=0\) | exact \(\delta\)-factor completion | yes |
| B_h_zero | not A, \(\ell>0\), \(h=0\) | exact \(h\)-factor completion | yes |
| D_rho_ge_sigma | not A, \(\ell,h>0\), \(\rho\geq\sigma\) | coupled residual | no |
| D_sigma_gt_rho | not A, \(\ell,h>0\), \(\sigma>\rho\) | coupled residual | no |

The table is exhaustive: every admissible box is either in A or not; in
the complement, nonnegativity makes \(\ell=0\), else \(h=0\), else
\(\ell,h>0\); the last region is split by the total order of
\(\rho,\sigma\).  The cases are disjoint by the displayed priority.

Wright Theorem 2.1 and Pascadi Corollary 18 have empty *direct* cells in
this table.  Wright first requires an actually fixed denominator factor;
Pascadi first requires the coefficient tuple in Assumption 14 and a
nondegenerate incomplete-Kloosterman adapter.  Neither hypothesis is
created by a linear inequality in the base polytope, so neither theorem
may be credited with a cell before the corresponding exact factorization
and coefficient transfer have been proved.

The helper published_coverage_cell implements precisely this partition.
The helper published_coverage_witnesses supplies one admissible rational
witness for each of the six nonempty cells, and the report prints the two
BCR savings and completion losses for every witness.

### 2.2 Exact residual Type-I/II routing

Only the two D cells are passed to the Möbius factorization.  For integer
cutoffs \(U_R,V_R,U_S,V_S\geq1\), with \(r>U_R\) and \(s>U_S\), put

\[
 c_U(a):=\sum_{d\mid a,\ d\leq U}\mu(d).
\tag{2.9}
\]

Applying the finite identity separately to \(r\) and \(s\) gives, with no
boundary or truncation remainder,

\[
 \mu(r)\mu(s)
 =\sum_{X,Y\in\{\mathrm I,\mathrm {II}\}}
   \sum_{ab=r,\,cd=s}
   \mathcal C_X(r;a,b)\mathcal C_Y(s;c,d),
\tag{2.10}
\]

where

\[
 \mathcal C_{\mathrm I}(r;a,b)
 =c_{U_R}(a)\mu(b)
  \mathbf1_{a>U_R,\,b\leq V_R},\qquad
 \mathcal C_{\mathrm {II}}(r;a,b)
 =c_{U_R}(a)\mu(b)
  \mathbf1_{a>U_R,\,b>V_R},
\tag{2.11}
\]

and the \(s\)-side uses \(c_{U_S}(c)\mu(d)\).  The two minus signs in the
one-variable identities cancel, so (2.10) consists of exactly the four
I/I, I/II, II/I, and II/II sectors.

Most importantly, (2.10) is inserted *before* changing or estimating the
oscillatory kernel.  Every nonzero finite term therefore retains

\[
 c_{U_R}(a)\mu(b)c_{U_S}(c)\mu(d)
 e\!\left(-\frac{h\delta\bar r}{s}\right),
 \qquad ab=r,\quad cd=s.
\tag{2.12}
\]

Thus both Möbius sides remain explicit and the third frequency is still
the product \(h\delta\), not an arbitrary coefficient of length \(HL\).
There is no factorization error and no phase replacement error in this
step.

For the symmetric exponent choice \(U_R=V_R=R^{1/3}\) and
\(U_S=V_S=S^{1/3}\), the exact scale ledger is

| side | Type I | Type II |
|---|---|---|
| \(r=ab\) | \(b\leq R^{1/3}\), \(a\gg R^{2/3}\) | \(R^{1/3}<b\ll R^{2/3}\), \(R^{1/3}\ll a\ll R^{2/3}\) |
| \(s=cd\) | \(d\leq S^{1/3}\), \(c\gg S^{2/3}\) | \(S^{1/3}<d\ll S^{2/3}\), \(S^{1/3}\ll c\ll S^{2/3}\) |

The executable `residual_type_i_ii_ledger` rejects A and B cells and
records these four scale sectors on D.  The finite helper
`residual_coupled_type_certificate` checks (2.10)--(2.12) with exact
integer arithmetic, including the normalized reciprocal phase.

This closes only the decomposition step.  It proves no new saving: after
the exact reindexing, each of the four sectors still requires a uniform
global, pre-Cauchy estimate that permits cancellation across
\((h,\delta)\), slopes, gcd parameters, and dyadic blocks.  In particular,
the two D cells remain uncovered.

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

This calculation is a diagnostic for what would be required after applying
the triangle inequality in \((v,j)\).  It is not a necessary local
consequence of (3.8): the original moment only requires the full sum
\(\mathfrak C_q[\widehat\Psi_h]\) to be small, and cancellation between
different dual cells is allowed.  The global determinant-lattice
reparametrization and the resulting no-triangle interface are recorded in
`2026-08-24-mwkf-global-coupled-coefficient-first.md`.
Section 9 of that note quantifies the kernel issue: isolating bounded \(v\)
at the hard box requires a Fourier window of width \(T^{-1/2}\), costs
\(T^{A/2}\) in the \(A\)-th cutoff seminorm, and spreads the physical
\(h\)-weight from \(T^{5/2}\) to \(T^3\).  Hence
\(\mathrm{RES}_{1,1}\) is not uniformly isolated in the accepted kernel
class.

This identifies (3.8) as an averaged two-linear-form Möbius correlation
with slopes as large as \(T^{1/2}\).  Matomäki--Radziwiłł--Tao,
arXiv:1503.05121, Theorem 1.6, has a factor \(A^{2k}\) for slopes bounded
by \(A\) and supplies logarithmic rather than the required \(T^{5/2}\)
reduction from the volume exponent.  Consequently it is not an adapter for
(3.8).  The remaining new input can now be stated as the single shifted
Möbius inequality \(\mathrm{SM}_{1/1000}\), with transform-tail seminorms
kept uniform.

### 3.10 Long-cutoff quotient split

The exact long cutoff \(r=ab\), \(a>T^{401/200}\), followed by
\[
 c_U(a)=\sum_{\substack{d\mid a\\d\le U}}\mu(d),\qquad a=de,
\]
turns the completed determinant into
\[
 d e b v-j s=\delta.
\tag{3.16}
\]
On dyadic boxes \(b\in[B,2B]\), \(|v|\in[V,2V]\), use
\[
 D_{B,V}=\frac{S^{1/2}}{4BV\mathscr L^{C_0}}
\tag{3.17}
\]
before taking the integer floor.  The sector \(d\le D_{B,V}\) has
\(bd|v|<S^{1/2}\mathscr L^{-C_0}\); the complement retains
\(\mu(d)\mu(s)\) and has \(e\ll T^2\mathscr L^{C_0}\).  The two exact residual names are
\(\mathrm{QBV}_{\epsilon}\) and \(\mathrm{QII}_{\epsilon}\), both with
local target \(T^{3499/1000}\mathscr L^{-A}\).

This is only an exponent-level opening.  The standard Bombieri--Vinogradov hypotheses are not verified: after fixing
\((\delta,j,b,d,v)\), the progression modulus is
\(bd|v|/(j,bd|v|)\), while the residue multiplicities and transformed
kernel remain coupled to all five outer variables.  No theorem adapter in
this audit controls that joint weighted average, and the complementary
QII sector is a new two-Möbius determinant sum.  Both published-coverage
flags therefore remain false.

### 3.11 Pascadi incomplete-Kloosterman adapter

Pascadi, arXiv:2404.04239v3, Corollary 18, equation (5.35), bounds an
incomplete Kloosterman form with phase
\[
 e\!\left(\frac{\pm n\overline{rd}}{sc}\right)
\]
by \(\|w_{r,s}A_{N,r,s}\|_2 I\), where
\[
 I^2
 =D^2NR+
 \left(1+\frac{C^2}{R^2S Y_N}\right)^{2\theta_{\max}}
 CS(C+DR)(RS+N).
\tag{3.18}
\]

For an optimistic direct comparison with the MWKF core, take the level
factors \(R=S=1\), the incomplete variables
\(d=r_{\rm MWKF}\asymp T^3\),
\(c=s_{\rm MWKF}\asymp T^3\), and collapse
\(n=h\delta\asymp T^5\).  Also pretend that the coupled
\((h,\delta,r,s)\)-kernel separates into a coefficient satisfying
Assumption 14 with the best generic norm \(A_N=T^{5/2+o(1)}\).  Then both
terms of \(I^2\) have exponent \(11\):
\[
 D^2N=T^{11},\qquad
 C(C+D)(1+N)=T^{11+o(1)}.
\tag{3.19}
\]
Hence \(I=T^{11/2+o(1)}\), and the optimistic Corollary 18 output is
\[
 T^{5/2}T^{11/2}=T^8.
\tag{3.20}
\]
Against \(T^{3499/1000}\), its deficit is
\[
 8-\frac{3499}{1000}=\frac{4501}{1000}.
\tag{3.21}
\]

The actual direct hypotheses are weaker, not stronger: the product
coefficient does not separate, Assumption 14 has not been verified for
the coupled kernel, and QCT has a linear centered phase rather than the
inverse phase in (3.18).  Thus Corollary 18 supplies no published
coverage here.  The adapter pascadi_incomplete_kloosterman_audit records
the regular and exceptional terms separately and sets all hypothesis and
coverage flags to false.

### 3.12 Drappeau double-quotient cells after the exact Möbius split

[Drappeau, Theorem 2.1](https://arxiv.org/abs/1504.05549) bounds, for
(q=1),

\[
 \sum_{c,d,n,r,s} b_{n,r,s}g(c,d,n,r,s)
 e\!\left(\frac{n\overline{rd}}{sc}\right)
 \ll (CDNRS)^{\varepsilon+O(\varepsilon _0)}
 K(C,D,N,R,S)\lVert b\rVert _2,
\]

where

\[
 K^2=CS(RS+N)(C+RD)
     +C^2DS\sqrt{(RS+N)R}
     +D^2NRS^{-1}.
\tag{3.22}
\]

This is not a direct base-cell estimate, but the exact two-sided Möbius
identity supplies a literal post-Type adapter.  Write

\[
 r=b_r d_r e_r,\qquad s=b_s d_s e_s,
\]

where (d_r,d_s) are the truncated Möbius divisors, (e_r,e_s) are the
unsigned quotients, and (b_r,b_s) retain the second Möbius weights.  Set

\[
 (r_{\rm Dra},d_{\rm Dra},s_{\rm Dra},c_{\rm Dra},n_{\rm Dra})
 =(b_rd_r,e_r,b_sd_s,e_s,-h\delta).
\tag{3.23}
\]

Then the Drappeau phase is exactly the original phase:

\[
 e\!\left(\frac{-h\delta\,\overline{b_rd_re_r}}
                   {b_sd_se_s}\right)
 =e\!\left(\frac{n_{\rm Dra}\overline{r_{\rm Dra}d_{\rm Dra}}}
                   {s_{\rm Dra}c_{\rm Dra}}\right).
\tag{3.24}
\]

Both Möbius weights and the product frequency remain in the arbitrary
coefficient (b_{n,r,s}).  The multiplicity in
((b_r,d_r)\mapsto b_rd_r), and similarly on the (s)-side, is divisor
bounded.  If

\[
 d=\log_T e_r,\quad c=\log_T e_s,\quad
 r_0=\rho-d,\quad s_0=\sigma-c,\quad a=\ell+h,
\]

the coefficient norm has exponent

\[
 B=\frac{a+r_0+s_0}{2}.
\tag{3.25}
\]

The three terms of (3.22) have exact exponents

\[
\begin{aligned}
 K_1&=\sigma+\max(r_0+s_0,a)+\max(c,\rho),\\
 K_2&=\sigma+c+d
       +\frac{\max(r_0+s_0,a)+r_0}{2},\\
 K_3&=a+\rho-\sigma+d+c,
\end{aligned}
\tag{3.26}
\]

and hence

\[
 E_{\rm Dra}=B+\frac12\max(K_1,K_2,K_3).
\tag{3.27}
\]

The remaining boundary distinction is essential.  If
(pi_r=\log_T d_r), (u_r=\log_T U_r), the exact Type support is

\[
 \pi_r\le u_r<\pi_r+d,
\tag{3.28}
\]

and similarly on the (s)-side.  Each side is partitioned as follows.

| exponent relation | Type subcell status |
|---|---|
| (pi>u) or (pi+d<u) | asymptotically empty |
| (pi=u) or (pi+d=u) | sharp boundary; still residual |
| (pi<u<pi+d), both with strict exponent gap | `strict_far`; both sharp indicators are eventually constant on the dyadic box |

Only the last row removes the coefficient--smooth-variable coupling without
a Mellin truncation or boundary error.  There the original dyadic kernel is
an admissible smooth (g), Drappeau's coprimality is exactly the original
reciprocal coprimality, and the signs of (n_{\rm Dra}) are handled as two
packets.  Thus a strict cell with
(E_{\rm Dra}<\rho+\sigma-1/1000) is genuine published coverage.

For example, take the admissible residual base box

\[
 (\rho,\sigma,a)=(3,3,1/2),\quad
 (d,c)=(3,5/2),\quad
 (\pi_r,\pi_s)=(0,0),\quad (u_r,u_s)=(1,1).
\]

Both hyperbolas are `strict_far`, and (3.27) gives

\[
 E_{\rm Dra}=\frac{39}{8}<\frac{5999}{1000}.
\tag{3.29}
\]

This is the first registered post-Type published subcell inside a base
Region-D box.  It does **not** cover the base box, since every remaining
factor cell must also be estimated.

At the hard witness ((\rho,\sigma,a)=(3,3,5)), optimizing (3.27) over
(0\le d,c\le3) gives

\[
 \min E_{\rm Dra}=\frac{33}{4},
 \qquad d=3,\quad \frac52\le c\le3.
\tag{3.30}
\]

If (c+d\le1), the first (K)-term gives
(E_{\rm Dra}\ge21/2).  If (c+d\ge1), the second gives

\[
 E_{\rm Dra}\ge 9-\frac d4\ge\frac{33}{4},
\]

with equality on the interval in (3.30).  Thus even a strict-far adapter
misses the hard target by

\[
 \frac{33}{4}-\frac{5999}{1000}=\frac{2251}{1000}.
\tag{3.31}
\]

This is a theorem-strength no-go result for this Drappeau adapter on the
hard box, not a lower bound for the original coupled sum.

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

| witness cell | primary route | decisive BCR saving | result |
|---|---|---:|---|
| A_rho_ge_sigma | BCR | \(1/20\) | covered |
| A_sigma_gt_rho | BCR | \(3/100\) | covered |
| B_ell_zero | elementary completion | \(-7/8\) | covered despite BCR failure |
| B_h_zero | elementary completion | \(-9/10\) | covered despite BCR failure |
| D_rho_ge_sigma | global coupled operator | \(-37/8\) | residual |
| D_sigma_gt_rho | global coupled operator | \(-15/4\) | residual |

The routing priority is BCR, completion, Wright fixed-factor, the exact
signed-\(j\) Farey reduction when \(L<S\), and finally the unreduced global
coupled operator.  The Möbius Type-I/II split remains an exact diagnostic
decomposition inside the residual routes, but it is no longer imposed box
by box before global cancellation.  A route becomes covered only when its
analytic estimate—not merely its kinematic condition—is available.  Hence
the completion faces and all base Wright calls currently flow to one of the
two global residual interfaces.

**published coverage result: residual cells remain.**  In particular, the
balanced witness has a fixed positive deficit of \(37/8\), and the separate
tail obligation \(\mathrm{TAIL}_{B,D}\) is also uncovered.  The next slice
must prove the two signed Farey trilinear bounds
FTF\(_{\epsilon,1/1000}\) in the balanced box, without first taking
absolute values in the size of the Poisson-dual variable; a zero-residual
coverage report cannot be produced from the cited results.

The refined post-Type table now contains nonempty Drappeau-covered subcells,
such as (3.29).  This does not change either Region-D base row: the sharp
boundary faces remain, and (3.30)--(3.31) show that no Drappeau factor
allocation covers the balanced hard witness at all.

The coefficient-first note also gives the exact finite-residue completion

\[
 \mathfrak F_{q,\epsilon}=\frac LS\mathfrak D_{q,\epsilon},
 \qquad
 \mathfrak D_{q,\epsilon}\ \,\text{has phase}\ \,
 e\left(\frac{crv}{s}\right).
\]

In the balanced box, \(c,v\ll T^{1/2}\mathscr L^C\).  The equivalent
completed gate is

\[
 \mathrm{CFK}_{\epsilon,1/1000}:
 \qquad
 |\mathfrak D_{q,\epsilon}|\ll_W T^{4-1/1000}.
\]

Its normalized ambient exponent is \(7\), so it needs saving
\(3001/1000\).  An optimistic generic Bettin--Chandee treatment after
collapsing \(a=cv\) has exponent \(67/10\), leaving the exact deficit
\(2701/1000\).  CFK is therefore an equivalent explicit
Kloosterman-fraction interface, not a published-coverage claim.

The completion zero mode is not an additional residual cell.  For each
signed weight, \(G(0)=0\), hence

\[
 \sum_{c\bmod s}\Omega(c)=0,
 \qquad
 \sum_{c\bmod s}\Omega(c)e(crv/s)
 =\sum_{c\ne0}\Omega(c)\{e(crv/s)-1\}.
\]

Thus CFK may be posed with nonzero residue frequencies only, provided the
centered phase is retained.  The determinant cell \(v=0\) is independently
empty because \(0<|\delta|<s\).

Korolev--Shparlinski Theorem 2.1 does not cover this centered family.  Its
prime-modulus and nonexceptional-trace hypotheses fail because \(s\) is a
general squarefree modulus and \(e(cvr/s)\) is precisely an
exceptional linear additive trace.  The adapter returns
`linear_additive_trace_is_exceptional`; moreover the theorem supplies only
\(X(\log\log p)/(\log p)\), not the power saving needed to move the CFK
ambient exponent from \(7\) below \(4\).

Finally, grouping the nonzero completion variables by \(a=cv\) gives the
exact coefficient

\[
 \Gamma_{r,s,\epsilon}(a)
 =\sum_{\substack{c\mid a\\c\in\mathcal C_s\setminus\{0\}}}
 \Omega_{r,s,a/c,\epsilon}(c)
\]

and reduces CFK to the two centered trilinear sums
\(\mathrm{CMT}_{\epsilon,1/1000}\) in \((r,s,a)\), with
\(|a|\ll T\mathscr L^{2C}\) and phase \(e(ar/s)-1\).  This is an
exact finite reindexing, but \(\Gamma\) depends on \((r,s)\), so it is not
an arbitrary separated third-variable coefficient covered by BCR.

The additive large sieve is no substitute.  Under the optimistic fiction
that all \(a/s\) are distinct it gives exponent \(13/2\), still
\(2501/1000\) above the target.  Since \((a,s)\) is unrestricted, a reduced
fraction can occur with multiplicity as large as \(T\); the resulting
Cauchy cost \(T^{1/2}\) returns exponent \(7\), with deficit
\(3001/1000\).  This calculation already assumes separated coefficients,
which the actual \(\Gamma_{r,s,\epsilon}\) are not.

There is also an exact symmetric finite completion on
\((\mathbb Z/s\mathbb Z)^2\):

\[
 \mathfrak S_q[\Psi]=\frac{HL}{S}\mathfrak D_q^{(2)}[\Theta],
 \qquad
 \sum_c\Theta(c,v)=\sum_v\Theta(c,v)=0.
\]

The finite Gauss kernel is
\(\sum_{x,y}e((cx+vy-\bar rxy)/s)=s e(rcv/s)\).  This gives the same CMT
target and a finite coefficient \(\Lambda_{r,s}(a)\) after \(a=cv\); it
does not add a published estimate.

## 6. Published coverage after global sector Type reassembly

The residual transition face admits an exact finer partition before any
absolute value.  For the critical sector resolution \(s\le Q\), all
nonempty sectors reassemble to

\[
 \bigsqcup_{0\le b<Q}
 \{w:bs\le Qw<(b+1)s\}=\{0,1,\ldots,s-1\}.
\tag{6.1}
\]

After retaining a nonzero sector character \(0<\xi<Q\), the one-factor
log identity gives

\[
 \mathcal A_\xi
 =-\sum_{s,w}e\!\left(
   \frac{\xi\lfloor Qw/s\rfloor}{Q}
  \right)
  \mu(s)\mu^2(ks+w)
  \sum_{dm=ks+w}\mu(d)\Lambda(m)
  \widetilde G_{s,w;h,\delta,\nu,\sigma}.
\tag{6.2}
\]

Thus the original \(a_{\rm AFE}=h\delta\), the two Möbius factors
\(\mu(s)\mu(d)\), and every packet label remain coupled.  On squarefree
support, \(m=p\) is prime.  At cutoff \(U=T^{1/3}\), the Type-II range is

\[
 T^{1/3}<d,p\ll T^{2/3},
 \tag{6.3}
\]

and the Type-I range has one factor at most \(T^{1/3}\).  Both separate
square-function estimates still require \(T^{1/2}\) before squaring.

The resulting exact coverage table is:

| published input | theorem-level gain | parameter/hypothesis mismatch | covers the Type gate? |
|---|---:|---|---|
| Blomer--Pascadi, arXiv:2607.24311v1 | \(T^{1/32}\) | standard fixed-modulus Kloosterman kernel not derived from the entry packet | no |
| Milićević--Qin--Wu, arXiv:2511.07550v1 | \(T^{1/100}\) | same kernel and coefficient-separation failure | no |
| Pascadi, [arXiv:2511.08445v2](https://arxiv.org/abs/2511.08445), Theorem 1.1 | \(T^{1/700}\), or \(T^{1/276}\) with one 1-bounded side | uniform in the modulus, but the entry-dependent coefficient adapter is absent | no |
| Pascadi v2, Theorem 1.2 | \(T^{1/12}\) on favorable factorable moduli | determinant shell is not uniformly favorable | no |
| Pascadi v2, Corollary 1.4 | no power when the common divisor is \(q=1\) | primitive determinant shell has no larger common fixed divisor | no |
| Tao--Teräväinen, [arXiv:2107.02158](https://arxiv.org/abs/2107.02158) | \((\log\log T)^{-c}\) | fixed-complexity linear systems and logarithmic, not half-power, decay | no |
| [Crnčević--Hernández--Rizk--Sereesuchart--Tao, arXiv:2211.15830v4](https://arxiv.org/abs/2211.15830), Theorem B; subsumed by [Teräväinen--Walker, arXiv:2303.12574v1](https://arxiv.org/abs/2303.12574), Theorem 1.2 | qualitative logarithmic limit; the latter also classifies the fixed rational-ratio Liouville resonance | fixed slopes and no power rate, not a moving rational \(Q\)-grid or Hilbert packet family | no |
| Lichtman, [arXiv:2009.08969v2](https://arxiv.org/abs/2009.08969), Theorem 1.1 | \((\log T)^{-1/3+\delta}\), power exponent \(0\) | scalar \(L^1\) shift average, fixed weight, and \(H=X^\theta<X\), not the moving-weight endpoint vector \(L^2\) packet | no |
| Technau--Zafeiropoulos, [arXiv:1907.06050](https://arxiv.org/abs/1907.06050), Theorem 2.1 and Corollary 4.4 | square-root \(L^2\) error for one fixed arithmetic function in continuous/metric slope; structured Sobolev sampling transfers this to separated reciprocal nodes with \(T^\varepsilon\) loss | the actual coefficient changes with the Beatty preimage, so no fixed length-\(T\) Hilbert family has been derived from the two-Möbius packet | no |
| Kim, arXiv:2603.23250 | \(<T^{1/600}\) in the entering range | deficit \(T^{299/600}\) and Möbius coefficient hypothesis fails | no |

For Pascadi Corollary 1.4, substituting
\(q=d=d'=e=f=1\) gives the constant factor \(2^{-1/6}\), so its
modulus average cannot be counted as a power saving.  This corrects the
older v1 statement: Pascadi v2 is uniform for all fixed moduli, but its
uniform saving and its modulus-average corollary still do not close the
coupled packet.

The executable helpers `farey_global_mobius_type_partition`,
`farey_global_type_scale_ledger`, and
`transition_published_kloosterman_entry_audit` record (6.1)--(6.3), the
two half-power deficits, and the updated fixed/averaged-modulus
Kloosterman rows.  The Beatty and ternary-correlation rows are recorded by
their separate adapters in the alternative-routes audit.
Their analytic coverage flags remain false.  Hence the two base Region-D
cells and the full \(\theta=3\) off-diagonal gate remain open.

The closest Type-I subpacket can be made still more explicit.  On the
\(d=1,k=1\) face, \(p=s+w\), so regrouping by \(w\) gives exactly

\[
 -\sum_w\sum_p
 e\!\left(\frac{\xi\lfloor Qw/(p-w)\rfloor}{Q}\right)
 \mu(p-w)\log p\,
 \widetilde G_{p-w,w;h,\delta,\nu,\sigma}.
 \tag{6.4}
\]

This is a shifted-prime Möbius coordinate with a moving Farey/AFE weight,
not Lichtman's scalar family.  The finite witness \(Q=11,w=1\) has sector
labels \(5,1,1\) at \((s,p)=(2,3),(6,7),(10,11)\), so the phase varies even
after the shift is fixed.  Moreover the full range reaches \(w\asymp p\),
whereas Lichtman's quantitative polynomial statement has
\(H=X^\theta<X\), and its logarithmic saving leaves the required
\(T^{1/2}\) deficit unchanged.  The executable adapters
farey_type_i_unit_divisor_shifted_prime_reassembly and
lichtman_shifted_prime_type_i_coverage_audit record this exact
reindexing and the three independent mismatches; neither asserts a Type-I
estimate.

Technau--Zafeiropoulos gives a closer scalar \(L^2\) comparison.  Its
continuous metric estimate has coefficient energy \(\|f\|_2^2\), so if
one fixed arithmetic function represented every sector, \(Q\asymp T\)
copies would have the desired total exponent two.  That fixed-function
hypothesis already fails for the actual two-Möbius coefficient.  At
\(Q=6,k=1\), the entries

\[
 (b,s,w,r)=(1,6,1,7),\qquad(2,5,2,7)
\]

give the same Beatty value \(r=7\), but
\(\mu(6)\mu(7)=-1\) and \(\mu(5)\mu(7)=1\).  Hence no scalar value
\(f(7)\) works for both slopes.  Independently, the finite
trigonometric polynomial used to expose Beatty membership has bandwidth
\(K\asymp T^{3/2}\).  On a uniform \(Q\)-grid,

\[
 \frac1Q\sum_{b\bmod Q}\left|\sum_kc_ke(kb/Q)\right|^2
 =
 \sum_{\rho\bmod Q}\left|\sum_{k\equiv\rho\;(\bmod Q)}c_k\right|^2.
 \tag{6.5}
\]

Generic Cauchy costs the largest alias multiplicity
\(1+K/Q\asymp T^{1/2}\); the corresponding separated-node large sieve has
the same power on the actual reciprocal slope grid.  Consequently the
continuous exponent \(2\) becomes the generic sampled exponent \(5/2\).
The exact finite witness \(Q=5\), \(c_1=c_6=c_{11}=1\) has continuous
energy \(3\) and normalized grid energy \(9\), so the alias factor is not
an artifact of the inequality for arbitrary coefficients.

The actual Beatty polynomial is not arbitrary: its coefficients satisfy

\[
 F(\lambda)=\sum_{m\leq X}g_m
 \sum_{1\leq |j|\leq X^{1/2}}c_j e(mj\lambda),
 \qquad |c_j|\ll |j|^{-1}.
 \tag{6.6}
\]

For \(h\)-separated nodes, Hilbert-valued \(H^{1/2+\eta}\) sampling,
followed by divisor Cauchy on the product frequency \(mj\), proves

\[
 h\sum_\beta\|F(\lambda_\beta)\|^2
 \ll_\varepsilon T^\varepsilon\sum_{m\leq T}\|g_m\|^2
 \qquad(X=Q=T,\ h\asymp Q^{-1}).
 \tag{6.7}
\]

The proof is (9.498)--(9.503).  It uses
\(\sum_{j\leq T^{1/2}}j^{-1+2\eta}\ll_\eta T^\eta\), so it supports the
actual nonuniform reciprocal nodes and introduces no positive power.
Thus the generic alias factor above is not an obstruction for a fixed
Hilbert coefficient family.  A direct arbitrary-alias treatment would
have asked for

\[
 \sum_{\rho\bmod Q}
 \left\|\sum_{k\equiv\rho\;(\bmod Q)}
 c_{k;h,\delta,\nu,\sigma}\right\|_2^2
 \ll T^\varepsilon\sum_k
 \|c_{k;h,\delta,\nu,\sigma}\|_2^2.
 \tag{6.8}
\]

The structured sampling lemma makes (6.8) unnecessary once a valid
fixed-coefficient adapter exists.  Technau--Zafeiropoulos still treats one
fixed coefficient function, whereas the actual second Möbius factor and
vector packet change with the Beatty preimage.  The helpers
trigonometric_grid_aliasing_sides and
technau_zafeiropoulos_grid_coverage_audit record the exact alias identity
and generic half-power diagnostic.  The corrected helper
structured_beatty_sobolev_sampling_audit proves the \(T^\varepsilon\)
structured transfer.  The helper
beatty_divisor_fourier_coefficient_sides verifies its finite
product-frequency Hilbert-Cauchy step over exact rational vectors.  The helper
farey_scalar_beatty_fixed_coefficient_collision verifies the independent
finite fixed-\(f\) obstruction.  The exact fixed-family map from the
original Type packet is still missing, so the coverage flag remains false.

The later labelled Type split gives a strictly weaker target than an
absolute nonzero-determinant estimate.  For the complete nonprincipal
sector packet, character orthogonality gives the positive projector square
(9.489).  After the determinant-zero diagonal is bounded, it is enough to
prove the one-sided joint inequality \({\rm JNT}_{2}^{+}\), (9.491), for
the signed sum of all four nonzero-determinant Type blocks.  This removes
the unnecessary lower bound on that signed sum, but no published theorem
in the coverage table proves the required uniform upper bound or supplies
the exhaustive packet adapter.

Reindexing a primitive entry by \(n=rs\) removes the separate moving
coefficient signs: \(\mu(r)\mu(s)=\mu(n)\).  For fixed product and sector,
the possible \(s\) lie in (9.495), and the critical relation
\(s\leq C(kQ+b)\) bounds their multiplicity by \(C=O(1)\), (9.496).
This repairs the scalar fixed-coefficient mismatch at the arithmetic
coefficient level.  It does not repair the theorem mismatch: the retained
coefficient is a factorization-dependent vector packet
\(B_{b,n,s}\), supported on a sparse divisor-selected product sequence.
None of the scalar Beatty/Farey results audited above accepts that weight
or proves the required sector square function.

The exact positive sector square can now be stated without the product
coordinate.  For the complete labelled vector packet set

\[
 X_b=\sum_{\substack{s\le Q,\ 0\le w<s,
                     \\ (ks+w,s)=1\\
                     \lfloor Qw/s\rfloor=b}}
 \mu(s)\mu(ks+w)\sum_\lambda G_{s,w,\lambda}.
 \tag{6.9}
\]

Character orthogonality and the recombined diagonal give

\[
 \begin{aligned}
 \mathcal E_{\ne0}
 &=\sum_b\|X_b\|^2-Q^{-1}\left\|\sum_bX_b\right\|^2,\\
 \mathcal E_{\ne0}
 &=D_{\Delta=0}+J_{\Delta\ne0},\qquad D_{\Delta=0}\ge0,
 \end{aligned}
 \tag{6.10}
\]

and hence

\[
 J_{\Delta\ne0}\le \mathcal E_{\ne0}
 \le\sum_b\|X_b\|^2.
 \tag{6.11}
\]

Consequently the centered positive gate

\[
 {\rm BC}^{\rm mov,cent}_{\mathcal H}(2):\qquad
 \sum_{b<Q}\|X_b\|^2
 -Q^{-1}\left\|\sum_{b<Q}X_b\right\|^2
 \ll_{\varepsilon,W}T^{2+\varepsilon}
 \tag{6.12}
\]

implies the one-sided joint Type gate.  Dropping the nonnegative
principal subtraction gives a stronger, also sufficient, uncentered
sector-square estimate.  The scalar specialization of (6.12) is a
centered moving rational Beatty correlation with slope \(k+b/Q\).  The published
Crnčević et al. theorem is fixed-irrational and qualitative logarithmic;
Teräväinen--Walker subsume it and identify fixed rational resonances, but
still give no uniform power rate.  Thus neither theorem supplies the
required one-power energy saving (equivalently \(T^{1/2}\) before
squaring).  The executable helpers
`farey_beatty_chowla_projector_sides` and
`beatty_chowla_power_gate_audit` verify (6.9)--(6.11) and the exponent
ledger, respectively; both keep the analytic coverage flag false.

There is one newly closed subrow inside this gate.  For
\(F_{\xi,Q}(x)=e(\xi\lfloor Qx\rfloor/Q)\), Fourier integration gives

\[
 F_{\xi,Q}(x)
 =\sum_{j\in\mathbb Z}
 \frac{Q(1-e(-\xi/Q))}{2\pi i(\xi+jQ)}
 e((\xi+jQ)x)
 +\frac{1-e(-\xi/Q)}2e(\xi x)
  \mathbf1_{Qx\in\mathbb Z}.
 \tag{6.13}
\]

On \(x=w/s\), primitivity turns the jump condition into \(s\mid Q\),
and reduction of the fractions \(b/Q\) gives

\[
 \{0,\ldots,Q-1\}\longleftrightarrow
 \{(s,w):(w,s)=1, s\mid Qw},qquad
 b\mapsto\left(Q/(b,Q),b/(b,Q)\right).
 \tag{6.14}
\]

Thus every sector contains exactly one primitive boundary entry and the
boundary projector is bounded by its recombined original-entry diagonal,
already \(O(T^{2+\varepsilon})\).  This closes all endpoint corrections
in (6.13).

Away from the boundary, \(dp=ks+w\) changes each harmonic exactly into

\[
 e((\xi+jQ)w/s)=e((\xi+jQ)dp/s).
 \tag{6.15}
\]

This linear-fraction form still does not make the standard additive large
sieve sufficient.  At \(s,Q\asymp T\), \(d\asymp T^\delta\), its
optimistic fixed-\(d\) energy is \(T^{3-\delta}\); even orthogonal summation
over the \(T^\delta\) divisors leaves \(T^3\), one power above the target.
The exact boundary helper, phase ledger, and scale audit are
`primitive_beatty_fourier_boundary_sides`,
`beatty_sector_fourier_type_phase_ledger`, and
`beatty_type_i_additive_large_sieve_audit`.  Only the boundary row is
marked proved; the continuous joint Type-I/II spectrum remains open.
