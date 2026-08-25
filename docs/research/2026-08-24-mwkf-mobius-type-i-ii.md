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

The later global-coupled audit shows that imposing these inequalities on
every factor box is sufficient but not necessary: it applies triangle
inequalities before cancellation between Poisson-dual cells.  Accordingly,
the Type-I/II sums below are retained as exact diagnostic identities and as
possible components of a global dispersion argument, not as the primary
logical gate for the original moment.

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

The Type-II chain surviving the diagonal audit in Section 4.2 is

\[
 \text{global product-fiber centering (4.8t)}\ \longrightarrow\
 \text{signed Gram expansion without a triangle inequality}\ \longrightarrow\
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

### 4.2 The zero complementary divisor forces a joint dispersion audit

The equation \(\Delta=0\) has an exact primitive-ray parametrization.
Put \(y_i=s_i a_i>0\).  Since \(n_i\ne0\), the equality

\[
 n_1y_2=n_2y_1
\tag{4.8g}
\]

first forces \(n_1,n_2\) to have the same sign.  Write uniquely

\[
 |n_1|=gu,\qquad |n_2|=gv,\qquad (u,v)=1.
\tag{4.8h}
\]

Then (4.8g) is equivalent to

\[
 \boxed{s_1a_1=uk,\qquad s_2a_2=vk}
\tag{4.8i}
\]

for a unique positive integer \(k\).  Conversely (4.8h)--(4.8i), with a
common sign for \(n_1,n_2\), imply \(\Delta=0\).  The finite helper
proportional_diagonal_coordinates checks this parametrization without
factorization or floating-point arithmetic.

The identical-tuple subcase

\[
 a_1=a_2,\qquad s_1=s_2,\qquad n_1=n_2
\tag{4.8j}
\]

is positive in the formal expansion of \(\mathcal E_b\): the two
Möbius signs and the two truncated-divisor coefficients become squares.
If \(B_0=T^\beta\), the cardinality-level \(L^2\) scale of its separate
majorant is

\[
 \underbrace{B_0}_{b}
 \underbrace{A_0}_{a}
 \underbrace{S}_{s}
 \underbrace{HL}_{n=h\delta\text{ second moment}}
 =RSHL=T^{11}.
\tag{4.8k}
\]

Only divisor and endpoint logarithms have been suppressed in (4.8k);
there is no Möbius sign left from which to obtain a fixed power.  By
contrast, the target SP\(_b\) is

\[
 \frac{R^2S^2}{B_0}T^{-1/250}
 =T^{12-\beta-1/250}.
\tag{4.8l}
\]

Thus the exponent-ledger ratio between this separate majorant and the
spectral target is

\[
 T^{\beta-1+1/250},\qquad 1\le\beta\le2.
\tag{4.8m}
\]

Even at \(\beta=1\), this cardinality-level diagonal majorant misses by
\(T^{1/250}\); at \(\beta=2\) it misses by \(T^{251/250}\).  After the
outer Cauchy inequality, the corresponding deficit against
\(RS T^{-1/500}\) is

\[
 T^{(\beta-1)/2+1/500}.
\tag{4.8n}
\]

Consequently the order displayed in (4.3) cannot be closed by “Cauchy,
apply a cardinality-level \(L^2\) bound to the positive diagonal, then
apply Kuznetsov to the rest.”  This does not assert a lower bound for an
arbitrary smooth box, and hence does not rule out every conceivable
post-Cauchy argument.  It does rule out the currently specified
separate-majorant implementation.  The replacement audited here is the
global factorization dispersion identity (4.8t), performed before a
triangle inequality while retaining the four signed Type-I/II sectors.
It extracts, rather than discards, an explicit single-Möbius main term.
Only that term, the centered \(\Delta=0\) remainder, and the
\(\Delta\ne0\) complementary-divisor sum may be passed to their
respective estimates.  The exact-rational function
type_ii_cauchy_diagonal_audit records the exponent ledger
(4.8k)--(4.8n), not a diagonal lower bound.

There is nevertheless an exact algebraic centering available on the
primitive subray \(u=v=1\).  Put

\[
 \mu_{\le U}(d):=\mu(d)\mathbf1_{d\le U}.
\tag{4.8o}
\]

Since \(c_U=\mu_{\le U}*1\), associativity of finite Dirichlet
convolution gives

\[
 \boxed{\mu*c_U=\mu_{\le U}.}
\tag{4.8p}
\]

Equivalently,

\[
 \sum_{sa=k}\mu(s)c_U(a)
 =\mu(k)\mathbf1_{k\le U}.
\tag{4.8q}
\]

The condition \(a>U\) in the actual Type sector is essential.  For
\(a\le U\), the definition of \(c_U\) gives
\(c_U(a)=\mathbf1_{a=1}\).  Removing this sole term from (4.8q) proves
the exact sector identity

\[
 \boxed{
 \sum_{\substack{sa=k\\a>U}}\mu(s)c_U(a)
 =-\mu(k)\mathbf1_{k>U}.}
\tag{4.8r}
\]

Both (4.8q) and (4.8r) remain valid on the original squarefree support:
there \(k=sa\) is squarefree, and the restrictions coprime to \(bq\)
depend only on \(k\).  The exhaustive helpers
full_truncated_mobius_convolution and
restricted_truncated_mobius_convolution verify the two finite identities
separately; the displayed convolution proof is general.

The same calculation applies to every primitive ray (4.8i), not only
to \(u=v=1\).  Provided \(uk>U\) and \(vk>U\), the two factorization
sums are exactly

\[
 \sum_{s_1a_1=uk\atop a_1>U}\mu(s_1)c_U(a_1)=-\mu(uk),
 \qquad
 \sum_{s_2a_2=vk\atop a_2>U}\mu(s_2)c_U(a_2)=-\mu(vk).
\tag{4.8r'}
\]

On the original support, \(uk\) and \(vk\) are squarefree and
\((u,v)=1\).  Hence \(u,v,k\) are pairwise coprime and squarefree, so

\[
 \boxed{\mu(uk)\mu(vk)=\mu(u)\mu(v)\mu(k)^2
 =\mu(u)\mu(v).}
\tag{4.8r''}
\]

Thus a product-only anchor on both sides moves the surviving Möbius pair
to the primitive slopes \((u,v)\); it leaves no Möbius cancellation in
the common radial variable \(k\).  The finite helper
restricted_zero_ray_pair_convolution checks (4.8r')--(4.8r'') and
explicitly rejects the simplification off squarefree support.

Let \(\mathcal V_{q,b,g,k}(s,a)\) denote the sum of the complete
factor-dependent weight over every signed factorization
\(h\delta=g\) allowed by the fixed \((H,L)\) box.  Thus it includes the
original \((h,\delta)\) weight after grouping equal products, the dyadic
factors, mollifier tapers, smooth real phase, and the
two reciprocal phases.  More precisely, for an admissible
\((q,b,s,a)\) with \(sa=k\), set

\[
 \boxed{
 \mathcal V_{q,b,g,k}(s,a)
 :=\sum_{\substack{h\delta=g\\h\sim H,\ \delta\sim L}}
 \mathcal W_q(a,b,s,h,\delta)
 e\!\left(-\frac{g}{abs}
           +\frac{g\overline{sb}}a
           +\frac{g\overline{sa}}b\right),}
\tag{4.8s}
\]

and set it to zero outside the original conditions in (4.4).  The last
phase depends only on \((g,k,b)\), but it is retained in (4.8s) so that
the displayed coefficient is exactly the first amplitude whose square
produces the \(u=v=1\) part of (4.8).

For any anchor \(\mathcal A_{q,b,g}(k)\) which depends on the product
\(k=sa\) but not on its factorization, (4.8r) gives

\[
\begin{aligned}
 &\sum_{\substack{sa=k\\a>U}}
   \mu(s)c_U(a)\mathcal V_{q,b,g,k}(s,a)\\
 &\quad=
 \sum_{\substack{sa=k\\a>U}}
   \mu(s)c_U(a)
   \{\mathcal V_{q,b,g,k}(s,a)-
      \mathcal A_{q,b,g}(k)\}
 -\mu(k)\mathcal A_{q,b,g}(k),
 \qquad k>U.
\end{aligned}
\tag{4.8t}
\]

Thus Linnik centering does not annihilate the sector: it extracts an
explicit single-Möbius main term and leaves a centered factorization
coefficient.  It must be performed before taking absolute values and
before localizing individual \((S,A_0)\) factor boxes, since extending a
dyadic weight by zero makes the anchor term range over the complementary
factorizations of the same \(k\).

At the balanced box,

\[
 B_0=T^\beta,\quad A_0=T^{3-\beta},\quad
 |g|\asymp HL=T^5,\quad k\asymp SA_0=T^{6-\beta}.
\tag{4.8u}
\]

The exact zero-ray input replacing a separate identity-diagonal bound is
therefore the following **joint** Gram inequality.  It is written with a
product-only anchor satisfying
\(|\mathcal A_{q,b,g}(k)|\ll_W\mathscr L^C\); the whole expression is
algebraically independent of the chosen anchor by (4.8t):

\[
\boxed{
 \mathrm{ZRG}_{\beta}:\quad
 \sum_{\substack{b\asymp B_0,\ b>V\\
                   \mu^2(b)=1,\ (b,q)=1}}
 \sum_{0<|g|\asymp HL}
 \sum_{\substack{k\asymp SA_0\\
                   \mu^2(k)=1,\ (k,bq)=1}}
 \left|
  \sum_{\substack{sa=k\\a>U}}
  \mu(s)c_U(a)
  \{\mathcal V_{q,b,g,k}(s,a)-
    \mathcal A_{q,b,g}(k)\}
  -\mu(k)\mathcal A_{q,b,g}(k)
 \right|^2
 \ll_W T^{12-\beta-1/250}.}
\tag{4.8v}
\]

If the explicit term
\(-\mu(k)\mathcal A_{q,b,g}(k)\) in (4.8t) is bounded separately after
squaring, its Möbius sign is lost.  For an anchor of unit or
polylogarithmic size on a positive-density part of the box, its
cardinality-level scale is again

\[
 B_0\cdot HL\cdot(SA_0)=T^{11}.
\tag{4.8w}
\]

Thus the corresponding exponent-ledger margin against (4.8v) is the same
\(1-\beta-1/250\) as in (4.8m), which is negative throughout
\(1\le\beta\le2\).  A proof using only that separate cardinality bound
therefore has to keep the centered coefficient, the explicit Möbius
main, and their cross term together inside the signed product-fiber Gram
form, or replace the bound by a genuinely sharper argument.  No
assertion in this note proves that joint estimate.  The
exact-rational function
zero_ray_convolution_centering_audit distinguishes the vanishing full
convolution (4.8q), the nonzero Type-sector main term (4.8r), and the new
joint Gram gate (4.8v), and records the repeated \(T^{11}\) obstruction
(4.8w).

For the general primitive ray, put \(u,v\asymp D=T^\theta\).  The
conditions \(|gu|,|gv|\asymp HL=T^5\) and
\(uk,vk\asymp SA_0=T^{6-\beta}\) give the exact zero-slack dyadic
ledger

\[
 g\asymp T^{5-\theta},\qquad
 k\asymp T^{6-\beta-\theta},\qquad
 0\le\theta\le6-\beta.
\tag{4.8x}
\]

The cardinality exponent of the anchor--anchor term is independent of
the slope depth:

\[
 \underbrace{B_0}_{\beta}
 \underbrace{D^2}_{2\theta}
 \underbrace{(HL/D)}_{5-\theta}
 \underbrace{(SA_0/D)}_{6-\beta-\theta}
 =T^{11}.
\tag{4.8y}
\]

By (4.8r''), a hypothetical square-root saving in each of the two
primitive Möbius slope sums saves at most the benchmark power
\(T^\theta\) relative to (4.8y).  The required power is

\[
 11-(12-\beta-1/250)=\beta-1+1/250.
\tag{4.8z}
\]

Therefore this benchmark can have positive slack only in

\[
 \boxed{\theta>\beta-1+1/250.}
\tag{4.8aa}
\]

The complementary low-slope cells
\(0\le\theta\le\beta-1+1/250\) still require cancellation involving
the centered factors, \(g\), or the nonsplit signed Gram; no
\(k\)-Möbius estimate is available there.  The exact-rational adapter
primitive_slope_zero_ray_audit records (4.8x)--(4.8aa).  Its
double-square-root field is a feasibility benchmark, not a cited or
proved estimate.

There is also an exact conductor collapse on each general ray.  Because
\(u\) and \(k\) are coprime and squarefree, every factorization
\(sa=uk\) has a unique prime allocation

\[
 s=s_us_k,\qquad a=a_ua_k,\qquad
 s_ua_u=u,\qquad s_ka_k=k.
\tag{4.8ab}
\]

Using \((s,a)=(uk,b)=1\), cancellation of the \(u\)-part in the
fixed-factor phase is exact:

\[
 \boxed{
 \frac{gu\,\overline{sb}}a
 \equiv
 \frac{g\,\overline{s_kb}}{a_k}\pmod1.}
\tag{4.8ac}
\]

The other two phases in (4.8b) and (4.8c) become

\[
 -\frac{gu}{abs}=-\frac{g}{kb},
 \qquad
 \frac{gu\,\overline{sa}}b
 \equiv\frac{g\bar k}b\pmod1.
\tag{4.8ad}
\]

In the product with the conjugate \((v,k)) amplitude, both phases in
(4.8ad) cancel identically.  The only residual reciprocal oscillation
on the zero ray is therefore attached to the allocation of the common
\(k\)-primes between \(s_k\) and \(a_k\), not to the primitive slopes
\(u,v\).  Any square-root estimate in \(u,v\) must consequently exploit
their Möbius correlation with the dyadic and coupled smooth weights; it
cannot invoke a nonexistent trace-function conductor in those variables.
The helper zero_ray_phase_reduction verifies (4.8ab)--(4.8ad) with exact
rational residues.

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
unconditional long-mollifier asymptotic.  In the balanced short-shift box,
the active primary gate is now the pair of no-triangle signed Farey sums
FTF\(_{\epsilon,1/1000}\) in
`2026-08-24-mwkf-global-coupled-coefficient-first.md`; together they are
exactly GCO\(_{1/1000}\).  Proving the two local inequalities here would
imply that gate, but failure to prove them does not disprove the possibility
of global cancellation.

Finite Fourier inversion in the signed shift residue gives the equivalent
completed interface CFK\(_{\epsilon,1/1000}\): a pair of sums with phase
\(e(crv/s)\), \(c,v\ll T^{1/2}\mathscr L^C\), and target
\(T^{4-1/1000}\).  The exact generic-coefficient deficit is
\(2701/1000\).  A subsequent Type-I/II argument must therefore retain both
Möbius weights and the product structure \(a=cv\); treating the collapsed
frequency coefficients as arbitrary cannot close the gate.

The signed support gives the exact centering relation
\(\sum_{c\bmod s}\Omega(c)=0\).  Hence the completion may be rewritten
using only \(c\ne0\) and the phase \(e(crv/s)-1\); no separate \(c=0\)
estimate is required.  The determinant range also has no \(v=0\) solution.
Any Type-I/II or spectral step applied after completion must preserve this
centered difference.

Equivalently, group \(a=cv\) and retain the exact coefficient family
\(\Gamma_{r,s,\epsilon}(a)\) from the coefficient-first note.  The active
balanced input is then the pair CMT\(_{\epsilon,1/1000}\), with
\(|a|\ll T\mathscr L^{2C}\), phase \(e(ar/s)-1\), and target
\(T^{4-1/1000}\).  A Type-I/II proof must act on this
\((r,s)\)-dependent divisor convolution rather than replace it by an
arbitrary \(a\)-coefficient.

The same gate also has a symmetric finite-group realization.  The
two-dimensional Fourier coefficient \(\Theta_{r,s}(c,v)\) has zero row and
column sums, effective lengths \(S/H\) and \(S/L\), and finite product
coefficient \(\Lambda_{r,s}(a)\).  This removes the infinite transform
index from CFK but leaves the CMT exponent unchanged.
