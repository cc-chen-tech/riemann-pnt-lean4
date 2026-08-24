# Möbius Type-I/II reduction for the residual MWKF cells

## 1. Status and input

This note consumes the exact coupled box

\[
 \mathfrak S_q[\Psi]
 =\sum_{r,s,h,\delta}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\Psi(r,s,h,\delta)
 e\!\left(-\frac{h\delta\bar r}{s}\right),
\tag{1.1}
\]

where the sums have the ranges and coprimality conditions in (5.3)--(5.14)
of the exact-audit note.  Published estimates leave the balanced witness

\[
 (\rho,\sigma,m,k,\ell,h,\kappa)
 =(3,3,1/2,1/2,5/2,5/2,0)
\tag{1.2}
\]

uncovered, with BCR saving \(-37/8\).  The purpose here is to reduce (1.1)
to two Möbius-sensitive local inequalities.  This note does not prove those
inequalities.

## 2. Exact Möbius identity

For a real cutoff \(U\geq1\), define

\[
 c_U(a)=\sum_{\substack{d\mid a\\d\leq U}}\mu(d).
\tag{2.1}
\]

For every integer \(n>U\),

\[
 \boxed{
 \mu(n)=-\sum_{\substack{ab=n\\a>U}}c_U(a)\mu(b).}
\tag{2.2}
\]

Indeed,

\[
 \sum_{ab=n}c_U(a)\mu(b)
 =\sum_{\substack{d\mid n\\d\leq U}}\mu(d)
   \sum_{bc=n/d}\mu(b)=0,
\tag{2.3}
\]

because the inner convolution is nonzero only for \(d=n\), which is
excluded by \(n>U\).  For \(a\leq U\), (2.1) is
\(\sum_{d\mid a}\mu(d)=\mathbf1_{a=1}\), so this part of (2.3) is
exactly \(\mu(n)\), proving (2.2).  This proof uses only finite
reindexing.

Fix

\[
 U=R^{1/3},\qquad V=R^{1/3}.
\tag{2.4}
\]

For a dyadic box with \(R\geq8\), every \(r\in[R/2,2R]\) satisfies
\(r>U\), so (2.2) applies term by term.  The finitely many smaller boxes
are absorbed into the already elementary bounded-variable regime.

The original support (5.1) of the exact-audit note is squarefree.  We first
restrict the \(r\)-sum to \(\mu^2(r)=1\), which changes no term, and only
then insert (2.2).  Hence every surviving factorization also satisfies

\[
 \mu^2(ab)=1,\qquad (a,b)=1.
\tag{2.4a}
\]

This squarefree restriction is part of the exact factorized sum; discarding
it would throw away useful CRT structure.

Splitting the right side of (2.2) at \(b\leq V\) is exact:

\[
 \mu(r)=-\sum_{\substack{ab=r\\a>U\\b\leq V}}c_U(a)\mu(b)
         -\sum_{\substack{ab=r\\a>U\\b>V}}c_U(a)\mu(b).
\tag{2.5}
\]

Integer endpoints may be read as \(d\leq\lfloor U\rfloor\) in (2.1) and
\(b\leq\lfloor V\rfloor\) in (2.5); no smoothing error is introduced.

## 3. Reciprocity and exact Type-I/II sums

If \(R<S\), first use, for \((r,s)=1\),

\[
 \frac{\bar r}{s}+\frac{\bar s}{r}\equiv\frac1{rs}\pmod1,
\qquad
 e\!\left(-\frac{h\delta\bar r}{s}\right)
 =e\!\left(\frac{h\delta\bar s}{r}\right)
  e\!\left(-\frac{h\delta}{rs}\right).
\tag{3.1}
\]

The last factor is absorbed into the coupled smooth weight.  Since
\(|h\delta|/(RS)\ll\mathscr L^{2B}/T\), its normalized derivatives have
the same polylogarithmic bounds as (5.14).  We may therefore relabel so that
\(R\geq S\) before applying (2.5).

For dyadic \(A_0,B_0\), let

\[
\begin{aligned}
 \mathfrak S^{\rm I}_q(A_0,B_0):={}&
 \sum_{\substack{a>U,\ b\leq V\\
                  A_0\leq a\leq2A_0,
                  \ B_0\leq b\leq2B_0\\
                  \mu^2(ab)=1}}
 c_U(a)\mu(b)
 \sum_{\substack{s,h,\delta\\
                  (ab,s)=1\\(q,abs)=1}}
 \mu(s)p_N(qab)p_N(qs)\\
 &\qquad\times F_R(ab)F_S(s)U_H(h)V_L(\delta)
 \Psi(a b,s,h,\delta)
 e\!\left(-\frac{h\delta\overline{ab}}s\right),
\end{aligned}
\tag{3.2}
\]

and define \(\mathfrak S^{\rm II}_q(A_0,B_0)\) by the identical formula
with \(b>V\).  Condition (2.4a), inherited from the original Möbius
support, implies \((a,b)=1\) in every one of these sums.

Inserting smooth dyadic partitions in \(a,b\) gives the exact identity

\[
 \mathfrak S_q[\Psi]
 =-\sum_{A_0,B_0}
 \left(\mathfrak S^{\rm I}_q(A_0,B_0)
      +\mathfrak S^{\rm II}_q(A_0,B_0)\right).
\tag{3.3}
\]

For \(R=T^\rho\), the choice (2.4) gives these exact exponent intervals:

| piece | \(b\)-exponent | \(a\)-exponent |
|---|---|---|
| Type I | \([0,\rho/3]\) | \([2\rho/3,\rho]\) |
| Type II | \([\rho/3,2\rho/3]\) | \([\rho/3,2\rho/3]\) |

Thus at the balanced residual witness \(R=T^3\), Type I has
\(b\leq T\), \(a\geq T^2\), while Type II has both factors between
\(T\) and \(T^2\).

### 3.1 Exact Wright mapping for Type I

For a fixed Type-I factor \(a\), reciprocity gives

\[
 e\!\left(-\frac{h\delta\overline{ab}}s\right)
 =e\!\left(\frac{h\delta\bar s}{ab}\right)
  e\!\left(-\frac{h\delta}{abs}\right).
\tag{3.4}
\]

The first factor has exactly Wright's fixed-denominator shape, with

\[
 M=S,\qquad N=B_0,\qquad A=LH,\qquad R_{\rm fix}=A_0.
\tag{3.5}
\]

The second factor in (3.4) is absorbed into the coupled smooth weight.  If
\(A_0=T^\alpha\), \(B_0=T^\beta\), then
\(\alpha+\beta=\rho\).  Wright's hypothesis \(M\ll N^2\) becomes

\[
 \sigma\leq2\beta.
\tag{3.6}
\]

On the balanced hard Type-I interval, \(\sigma=3\) and
\(0\leq\beta\leq1\), so (3.6) fails everywhere.  At the least unbalanced
endpoint \((\alpha,\beta)=(2,1)\), formal substitution into all five terms
of the displayed Wright v2 bound, including the outer sum over fixed
\(a\), gives saving

\[
 s_{\rm Wright,I}=-\frac{45}{8}.
\tag{3.7}
\]

Thus Wright is a valid structural adapter after (3.4), but it supplies no
estimate on the balanced residual Type-I region.

## 4. Two precise local inequalities

There are \(O(\mathscr L^2)\) dyadic factor pairs in (3.3).  A fixed
power twice as strong as the accepted CK target absorbs this loss.  It is
therefore sufficient to prove, uniformly over every residual core box,

> **TI\(_{1/500}\).** For every Type-I factor box in (3.2),
> \[
>  |\mathfrak S^{\rm I}_q(A_0,B_0)|
>  \ll_W RS\,T^{-1/500}.
> \tag{4.1}
> \]

and

> **TII\(_{1/500}\).** For every Type-II factor box,
> \[
>  |\mathfrak S^{\rm II}_q(A_0,B_0)|
>  \ll_W RS\,T^{-1/500}.
> \tag{4.2}
> \]

Equations (3.3)--(4.2) then imply CK\(_{1/1000}\) for all sufficiently
large \(T\).  Type I retains the Möbius weights \(\mu(b)\mu(s)\), the
truncated-divisor coefficient \(c_U(a)\), and the factorization
\(h\delta\); it is not an arbitrary-coefficient BCR sum.  Type II has two
medium factor variables and the independent Möbius weight \(\mu(s)\).

The proposed Type-II chain is

\[
 \text{Cauchy} \longrightarrow\
 \text{diagonal/non-diagonal expansion}\ \longrightarrow\
 \text{reciprocity}\ \longrightarrow\
 \text{complementary divisor}\ \longrightarrow\
 \text{Kuznetsov plus spectral large sieve}.
\tag{4.3}
\]

### 4.1 Double Möbius split and denominator-factor audit

Set \(U_R=V_R=R^{1/3}\) as in (2.4), and independently set
\(U_S=V_S=S^{1/3}\).  Applying (2.5) to \(s=cd\), with the latter
cutoffs, is again a finite identity.  Since the two one-variable identities
each carry a minus sign, their product gives

\[
 \mu(r)\mu(s)
 =\sum_{X,Y\in\{\mathrm I,\mathrm {II}\}}
   \sum_{a,b,c,d\geq1}
   \mathcal C_X(r;a,b)\mathcal C_Y(s;c,d),
\tag{4.3a}
\]

where

\[
 \mathcal C_{\mathrm I}(r;a,b)
 =c_{U_R}(a)\mu(b)
  \mathbf1_{a>U_R,\,b\leq V_R,\,ab=r,\,\mu^2(ab)=1},
 \qquad
 \mathcal C_{\mathrm {II}}(r;a,b)
 =c_{U_R}(a)\mu(b)
  \mathbf1_{a>U_R,\,b>V_R,\,ab=r,\,\mu^2(ab)=1},
\tag{4.3b}
\]

and the \(s\)-coefficients use \(c_{U_S}(c)\mu(d)\), the cutoffs
\(U_S,V_S\), and \(\mu^2(cd)=1\).
Thus (4.3a) has exactly four sectors and no remainder.  At the balanced
box, the exponent of \(d\) is in \([0,1]\) in denominator Type I and in
\([1,2]\) in denominator Type II.

Fixing \(c\sim C_0\) in the denominator split gives Wright's parameters

\[
 M=R,\qquad N=D_0,\qquad A=LH,\qquad R_{\rm fix}=C_0.
\tag{4.3c}
\]

If \(D_0=T^d\), then \(C_0=T^{3-d}\), and the hypothesis \(M\leq N^2\)
requires \(d\geq3/2\).  The outer sum over the fixed values of \(c\) costs
the full factor \(T^{3-d}\).  At the endpoint \(d=2\), exact substitution
in the five displayed Wright terms gives the base saving \(-4\), hence

\[
 s_{\rm Wright,den}=-5
 \qquad\bigl(=-4-(3-2)\bigr).
\tag{4.3d}
\]

Consequently even the endpoint with the longest allowed remaining
denominator factor fails the required positive saving.  Splitting the
second Möbius weight is exact and useful for locating its structure, but a
trivial outer sum over the fixed factor cannot prove any of the four
balanced sectors.

To make the first arrow precise, for a fixed \(b\sim B_0\) define

\[
\begin{aligned}
 \mathcal A_b:={}&
 \sum_{\substack{a\sim A_0,\ a>U\\ab\asymp R}}
 c_U(a)
 \sum_{\substack{s\asymp S,\ h\asymp H,\ \delta\asymp L\\
                  (ab,s)=1,\ (q,abs)=1}}
 \mu(s)\,\mathcal W_q(a,b,s,h,\delta)\\
 &\hspace{35mm}\times
 e\!\left(-\frac{h\delta\overline{ab}}s\right),
\end{aligned}
\tag{4.4}
\]

where \(\mathcal W_q\) is exactly the product of the six smooth factors in
(3.2), including \(p_N(qab)p_N(qs)\) and the coupled kernel.  Then

\[
 \mathfrak S_q^{\rm II}(A_0,B_0)
 =\sum_{b\sim B_0}\mu(b)\mathcal A_b,
 \qquad
 |\mathfrak S_q^{\rm II}|^2
 \leq B_0\sum_{b\sim B_0}|\mathcal A_b|^2.
\tag{4.5}
\]

Consequently the exact post-Cauchy spectral target sufficient for
TII\(_{1/500}\) is

\[
 \boxed{
 \mathcal E_b:=\sum_{b\sim B_0}|\mathcal A_b|^2
 \ll_W \frac{R^2S^2}{B_0}\,T^{-1/250}.}
\tag{SP\(_b\)}
\]

Writing \(n_i=h_i\delta_i\), its non-diagonal expansion is the sum over

\[
\begin{gathered}
 b\sim B_0,\quad a_1,a_2\sim A_0,\quad a_ib\asymp R,\\
 s_1,s_2\asymp S,\quad h_1,h_2\asymp H,
 \quad\delta_1,\delta_2\asymp L,\\
 (a_ib,s_i)=1,\qquad(q,a_1a_2bs_1s_2)=1,
\end{gathered}
\tag{4.6}
\]

with coefficient

\[
 c_U(a_1)c_U(a_2)\mu(s_1)\mu(s_2)
 \mathcal W_q(a_1,b,s_1,h_1,\delta_1)
 \overline{\mathcal W_q(a_2,b,s_2,h_2,\delta_2)}
\tag{4.7}
\]

and phase

\[
 e\!\left(
 -\frac{n_1\overline{a_1b}}{s_1}
 +\frac{n_2\overline{a_2b}}{s_2}
 \right).
\tag{4.8}
\]

The squarefree support now makes the reciprocity arrow in (4.3) exact
rather than formal.  For \((a,b)=(s,ab)=1\), CRT gives

\[
 \frac{n\bar s}{ab}
 \equiv
 \frac{n\overline{sb}}a+\frac{n\overline{sa}}b
 \pmod1.
\tag{4.8a}
\]

Applying (3.1) and then (4.8a) to (4.8) yields the product of a smooth
real phase

\[
 e\!\left(-\frac{n_1}{a_1bs_1}+\frac{n_2}{a_2bs_2}\right),
\tag{4.8b}
\]

the two fixed-factor phases

\[
 e\!\left(
 \frac{n_1\overline{s_1b}}{a_1}
 -\frac{n_2\overline{s_2b}}{a_2}
 \right),
\tag{4.8b'}
\]

and the common-\(b\) phase

\[
 e\!\left(
 \frac{n_1\overline{s_1a_1}-n_2\overline{s_2a_2}}b
 \right).
\tag{4.8c}
\]

All inverses in (4.8c) exist because
\((a_i,b)=(s_i,a_ib)=1\).  Its zero-frequency congruence is equivalent,
after multiplication by \(s_1a_1s_2a_2\), to

\[
 b\mid\Delta,
 \qquad
 \Delta:=n_1s_2a_2-n_2s_1a_1.
\tag{4.8d}
\]

For \(\Delta\ne0\), the complementary divisor is the nonzero integer

\[
 c=\frac\Delta b,
 \qquad
 1\leq |c|
 \leq \frac{32LHSA_0}{B_0},
\tag{4.8e}
\]

where the constant 32 follows from the displayed dyadic supports of
\(n_i=h_i\delta_i\), \(s_i\), and \(a_i\).  Thus in the balanced box
\(B_0=T^\beta\), \(A_0=T^{3-\beta}\), its zero-slack exponent is

\[
 |c|\ll T^{11-2\beta}.
\tag{4.8f}
\]

Equations (4.8c)--(4.8f) are the precise complementary-divisor data that a
Kuznetsov step must consume; neither the \(\Delta=0\) solutions nor the
nonzero \(c\)-sum may be dropped.

At the balanced witness, write \(B_0=T^\beta\),
\(1\leq\beta\leq2\).  The right side of SP\(_b\) has the explicit
exponent

\[
 T^{12-\beta-1/250}.
\tag{4.9}
\]

This is the exact quantity on which reciprocity, the complementary divisor,
and Kuznetsov must act.  A spectral large sieve used only through coefficient
\(L^2\) norms sees

\[
 \|\mu\mathbf1_{[B_0,2B_0]}\|_2\leq B_0^{1/2},
 \qquad
 \|\mu\mathbf1_{[S,2S]}\|_2\leq S^{1/2},
\tag{4.10}
\]

which are identical to arbitrary bounded coefficients.  Such an application
therefore returns to the BCR coverage ledger and cannot repair the
\(-37/8\) witness.  A proof of SP\(_b\) must retain cancellation in the
off-diagonal correlations \(\mu(s_1)\mu(s_2)\) in (4.7), rather than
discarding them in a second Cauchy step.

The trace-function result of Korolev--Shparlinski
(arXiv:1804.01337, Theorem 2.1) gives logarithmic cancellation for a single
Möbius sum against a bounded-conductor trace function modulo a fixed prime
when the interval is at least \(p^{1/2+\varepsilon}\).  It does not apply
directly to (4.6)--(4.8): the moduli \(s_i\) are varying general squarefree
integers, the trace family also varies with \(a_i,b,n_i\), and SP\(_b\)
requires their joint second moment.

No cited theorem currently supplies (4.2) with the coupled
\((h,\delta,a,b,s)\)-weight and the exponent \(1/500\).  In particular,
replacing the coefficients by their \(L^2\) norms returns to the BCR
deficit \(-37/8\) at (1.2).  Therefore the last arrow in (4.3) is a new
spectral proposition, not a routine adapter.

**new spectral proposition status: unproved.**

## 5. Tail and final-theorem boundary

The same finite identity (2.5) can be applied inside
\(\mathcal R_{\rm tail}^{(B)}\), but its rapidly decaying kernel seminorms
must survive the Type-I/II estimates.  This requires seminorm-sensitive
versions of (4.1)--(4.2) and is precisely the separate
TAIL\(_{B,D}\) obligation.  Neither (4.1), (4.2), nor TAIL\(_{B,D}\) is
proved here.

Consequently this slice reduces the residual problem to two explicit
Möbius-weighted multilinear inequalities, but it does not establish the
unconditional long-mollifier asymptotic.
