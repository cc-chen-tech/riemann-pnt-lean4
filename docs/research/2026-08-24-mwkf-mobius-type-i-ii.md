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
 \text{full determinant phase (4.8c'')}\ \longrightarrow\
 \text{completion with zero/nonzero modes}\ \longrightarrow\
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

At this stage the phase has not been separated or majorized.  Every finite
summand still has the form

\[
 c_{U_R}(a)\mu(b)c_{U_S}(c)\mu(d)
 e\!\left(-\frac{h\delta\bar r}{s}\right),
 \qquad ab=r,\quad cd=s.
\tag{4.3a'}
\]

The helper \`coupled_product_double_mobius_certificate\` verifies (4.3a')
with exact integer arithmetic for independent cutoffs on the two sides.
It records the same normalized reciprocal phase in all four sectors and
checks that their signed sum is exactly \(\mu(r)\mu(s)\).  This is an exact
reindexing certificate only; it supplies no analytic saving.

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
\((a_i,b)=(s_i,a_ib)=1\).  Put \(y_i=s_i a_i\).  Without imposing any
congruence, the full common phase is exactly

\[
 e\!\left(\frac{\Delta\,\overline{y_1y_2}}b\right),
 \qquad
 \Delta:=n_1y_2-n_2y_1.
\tag{4.8c'}
\]

Reciprocity gives the second exact form

\[
 \boxed{
 e\!\left(\frac{\Delta\,\overline{y_1y_2}}b\right)
 =
 e\!\left(\frac{\Delta}{b y_1y_2}\right)
 e\!\left(-\frac{\Delta\bar b}{y_1y_2}\right).}
\tag{4.8c''}
\]

On the balanced box,
\(|\Delta|/(b y_1y_2)\ll T^{-1}\) up to fixed dyadic constants, so the
first factor in (4.8c'') belongs to the smooth weight.  The second factor
is the genuine reciprocal oscillation, with modulus \(y_1y_2\).

The special congruence for which the common-\(b\) phase is \(1\) is

\[
 b\mid\Delta.
\tag{4.8d}
\]

Condition (4.8d) is not present in the full expanded square.  Only on
this special subfamily, when \(\Delta\ne0\), is the complementary divisor
the nonzero integer

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

Equations (4.8c')--(4.8c'') are the phase data for the full determinant
sum.  Equations (4.8d)--(4.8f) describe only its \(b\mid\Delta\)
subfamily.  A completion may isolate that subfamily as a zero mode, but
no such completion has yet been inserted in (4.6)--(4.8).  The helper
common_b_phase_reciprocity verifies both exact phase forms and exhibits
examples with \(b\nmid\Delta\).

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
\(\Delta\ne0\) full determinant phase may be passed to their respective
estimates.  A complementary divisor occurs only after a completion has
isolated the special mode (4.8d).  The exact-rational function
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

In the product with the conjugate \((v,k)\) amplitude, both phases in
(4.8ad) cancel identically.  The only residual reciprocal oscillation
on the zero ray is therefore attached to the allocation of the common
\(k\)-primes between \(s_k\) and \(a_k\), not to the primitive slopes
\(u,v\).  Any square-root estimate in \(u,v\) must consequently exploit
their Möbius correlation with the dyadic and coupled smooth weights; it
cannot invoke a nonexistent trace-function conductor in those variables.
The helper zero_ray_phase_reduction verifies (4.8ab)--(4.8ad) with exact
rational residues.

### 4.3 A longer Möbius cutoff removes the cardinality diagonal

The choice \(U=R^{1/3}=T\) in (2.4) is not forced by the finite identity
(2.2).  At the balanced box, instead set

\[
 \boxed{U=T^{401/200}.}
\tag{4.8ae}
\]

For all sufficiently large \(T\), every \(r\asymp T^3\) still satisfies
\(r>U\), so (2.2) remains an exact termwise identity.  Omitting the
auxiliary \(V\)-split altogether gives one sector

\[
 a>U,\qquad ab=r,\qquad
 a\gg T^{401/200},\qquad b\ll T^{199/200}.
\tag{4.8af}
\]

The implicit constants in (4.8af) come only from the fixed dyadic support
of \(r\); no terms are discarded.  Write \(B_0=T^\beta\).  Then
\(0\le\beta\le199/200\), while the cardinality-level identity diagonal
still has exponent \(11\).  Its post-Cauchy spectral target is

\[
 T^{12-\beta-1/250}.
\tag{4.8ag}
\]

The target is smallest at \(\beta=199/200\), where

\[
 12-\frac{199}{200}-\frac1{250}
 =\frac{11001}{1000}=11+\frac1{1000}.
\tag{4.8ah}
\]

Thus this cutoff gives a fixed \(T^{1/1000}\) margin over the
cardinality diagonal in every factor box.  In fact it covers the entire
zero complementary divisor.  For a primitive-slope box
\(u,v\asymp T^\theta\), the count in (4.8y) is \(T^{11}\), independently
of \(\theta\).  There are \(O(\log T)\) slope boxes, while
\(|c_U(a)|\le\tau(a)\ll_\varepsilon T^\varepsilon\) and grouping
\(h\delta=n\) costs another divisor factor.  Consequently, for every
fixed \(\varepsilon>0\),

\[
 \boxed{\mathcal E_b^{\Delta=0}\ll_{W,\varepsilon}T^{11+\varepsilon}.}
\tag{4.8ah'}
\]

Taking \(\varepsilon<1/1000\), (4.8ah') is smaller than the worst target
in (4.8ah).  Thus the zero-ray obstruction in (4.8m) is an obstruction
to the earlier balanced factorization, not to every use of (2.2).

This does **not** prove the new single sector.  The original reciprocal
modulus still contains

\[
 ab=r\asymp T^3,
\tag{4.8ai}
\]

so the original reciprocal conductor has not shortened.  In the full
post-Cauchy phase (4.8c''), the remaining reciprocal modulus is
\(y_1y_2\asymp T^{12-2\beta}\).  Moreover, on the special
\(b\mid\Delta\) subfamily, the shortest complementary-divisor range,
attained at \(\beta=199/200\), has exponent

\[
 5+3+\frac{401}{200}-\frac{199}{200}
 =\frac{901}{100},
\tag{4.8aj}
\]

and it is longer for smaller \(\beta\).  This exponent belongs only to
the special subfamily (4.8d), not to every nonzero determinant.  No
published adapter audited in this branch estimates the full coupled
off-diagonal.  More precisely, let
\(\mathcal E_{b,\ne0}^{(401/200)}\) be the exact expansion
(4.6)--(4.8), with (4.8ae)--(4.8af) in place of (2.4), restricted to

\[
 \Delta=n_1s_2a_2-n_2s_1a_1\ne0.
\tag{4.8ak}
\]

After the unconditional zero-ray bound (4.8ah'), the sole post-Cauchy
local input for this factorization is

\[
 \boxed{
 \mathrm{LCO}_{\beta}:\quad
 \left|\mathcal E_{b,\ne0}^{(401/200)}\right|
 \ll_W \frac{R^2S^2}{B_0}T^{-1/250},
 \qquad 0\le\beta\le\frac{199}{200}.}
\tag{4.8al}
\]

All variables, coefficients, coprimality conditions, weights, and phases
in LCO are exactly those in (4.6)--(4.8), with the common phase retained
in either exact form (4.8c') or (4.8c'').  There is no global condition
\(b\mid\Delta\); the integer \(c=\Delta/b\) from (4.8e) occurs only on
the special subfamily (4.8d).  The exact-rational function
long_mobius_cutoff_audit records the positive zero-ray margin and the
zero-mode complementary-divisor endpoint separately from the full
off-diagonal.  It deliberately sets published off-diagonal coverage to
false: (4.8al) is unproved.

The short common factor \(b\) does not by itself license Poisson
summation in \(h\).  If one looks only at the common-\(b\) factor in
(4.8c), then \(H/B_0\) has exponent

\[
 \frac52-\beta\ge\frac{301}{200}.
\tag{4.8am}
\]

But the same \(h\) occurs simultaneously in the fixed-\(a\) phase
(4.8b').  Its normalized frequency across the \(h\)-box is

\[
 \frac{HL}{A_0}
 =T^{5-(3-\beta)}
 =T^{2+\beta},
\qquad
 2\le2+\beta\le\frac{599}{200}.
\tag{4.8an}
\]

This is a positive power throughout the long-cutoff range, so the
fixed-\(a\) phase cannot be absorbed into a smooth amplitude before a
\(b\)-Poisson step.  Recombining both CRT phases returns the legitimate
full modulus \(ab\asymp T^3\), for which

\[
 \frac{H}{ab}=T^{-1/2}.
\tag{4.8ao}
\]

Therefore the inference “\(b<H\), Poisson in \(h\), hence
\(b\mid\delta\)” is invalid for LCO.  Any completion must transform the
full phase and retain the fixed-\(a\) oscillation.  The adapter
long_cutoff_h_completion_audit records (4.8am)--(4.8ao) and rejects the
\(b\)-only completion uniformly.

### 4.4 The remaining Möbius determinant average

Applying Poisson to the **complete** \(h\)-phase returns the exact
determinant lattice from the global-coupled note:

\[
 \delta=rv-js,\qquad
 r,s\asymp T^3,\qquad
 |v|,|j|\ll T^{1/2},\qquad
 \delta\asymp T^{5/2}.
\tag{4.8ap}
\]

For a fixed nonzero \(\delta\), put
\[
 M_1=|v|\asymp T^{1/2},\quad
 M_2=|j|\asymp T^{1/2},\quad
 N_1=r\asymp T^3,\quad
 N_2=s\asymp T^3.
\]
The determinant scale in Bettin--Chandee Corollary 1 is

\[
 \mathcal R=M_1N_2+M_2N_1\asymp T^{7/2}.
\tag{4.8aq}
\]

Direct counting of one determinant fiber has exponent
\[
 \frac{M_1M_2N_1N_2}{\mathcal R}=T^{7/2}.
\tag{4.8ar}
\]
This exponent has an elementary congruence proof.  For fixed nonzero
\(v,j\), put \(g=(v,j)\).  The equation \(rv-js=\delta\) is soluble only
if \(g\mid\delta\); when it is, \(s\) occupies one residue class modulo
\(|v|/g\), and \(r\) is then determined.  Hence the number of
\((r,s)\)-pairs is
\[
 O\!\left(1+\frac{Sg}{|v|}\right).
\]
On dyadic \(v\asymp V\), \(j\asymp J\),
\[
 \sum_{v\asymp V}\sum_{j\asymp J}\frac{(v,j)}{|v|}
 \ll J\log(2V),
\]
by writing \(d\mid(v,j)\) and summing first over \(v/d,j/d\).
Consequently one fixed shift has
\[
 O\!\left(VJ+SJ\log(2V)\right)
 \ll T^{7/2}\log T
\]
solutions in the hard box.  Thus (4.8ar) is an unconditional
cardinality bound, not a random-determinant heuristic.

Even if one optimistically separates the actual coupled kernel into the
short-variable product required by the corollary, its published error has
the exponent of
\[
 \mathcal R^{3/2}
 \|\alpha\|_2\|\beta\|_2
 (N_1N_2)^{7/20}(N_1+N_2)^{1/4},
\]
which under (4.8ap) is
\[
 \frac32\cdot\frac72+3+\frac7{20}\cdot6+\frac14\cdot3
 =\frac{111}{10}.
\tag{4.8as}
\]
It is therefore much worse than the direct fixed-shift count in this
aspect.  Without that optimistic separation, the coupled kernel does not
directly satisfy the displayed product-weight hypotheses in the first
place.  Thus the corollary supplies no saving under either reading.

Summing (4.8ar) over the \(T^{5/2}\) shift range gives the cardinality
exponent \(6\).  The exact global target is

\[
 \frac{RS}{H}T^{-1/1000}=T^{3499/1000}.
\tag{4.8at}
\]

Consequently the surviving arithmetic input must save exactly

\[
 \boxed{6-\frac{3499}{1000}=\frac{2501}{1000}}
\tag{4.8au}
\]
over the summed determinant-fiber cardinality.  Equivalently, with the
full transformed kernel and all conditions of (6.2) in the
global-coupled note retained, the remaining proposition is

\[
 \boxed{
 \mathrm{MD}_{2501/1000}:\quad
 \left|
 \sum_{\substack{r,s\asymp T^3\\(r,s)=1,\ (q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)
 \sum_{\substack{\delta\asymp T^{5/2}\\
                  |v|,|j|\ll T^{1/2}\\
                  rv-js=\delta}}
 \widehat\Psi_h(r,s,\delta,v)
 \right|
 \ll_W T^{3499/1000}.}
\tag{4.8av}
\]

Here \(\widehat\Psi_h(r,s,\delta,v)\) abbreviates exactly the normalized
four-variable kernel in (6.2), not a separated coefficient.  Inserting
the long-cutoff identity into the \(r\)-sum gives the equivalent
long-\(a\), short-\(b\) LCO formulation, while summing the factorization
back gives (4.8av).  Thus the cutoff closes the zero determinant but does
not alter the required nonzero-determinant Möbius saving.  The adapter
bc_fixed_determinant_audit records (4.8aq)--(4.8au), with published
coverage and direct-hypothesis flags both false.

### 4.5 Quotient-hyperbola split at the level-one-half face

There is one further exact decomposition which is lost if Cauchy is
applied first.  Insert \(r=ab\), \(a>U=T^{401/200}\), into (4.8ap), and
expand the quotient coefficient before taking absolute values:

\[
 c_U(a)=\sum_{\substack{d\mid a\\d\le U}}\mu(d),
 \qquad a=de,
 \qquad d e b v-j s=\delta.
\tag{4.8aw}
\]

Fix a nonnegative \(\omega\in C_c^\infty((1/2,2))\) satisfying
\(\sum_{k\in\mathbb Z}\omega(x/2^k)=1\) for \(x>0\).  Put
\(\omega_B(b)=\omega(b/B)\) and
\(\omega_V(v)=\omega(|v|/V)\) for \(B,V\in2^{\mathbb Z}\).  For
\(\mathcal D\subset\mathbb N\), define

\[
\begin{aligned}
 \mathfrak Q_{q,\epsilon}(B,V;\mathcal D)
 :={}&-\sum_{b\ge1}\mu(b)\omega_B(b)
 \sum_{\substack{d\in\mathcal D\\d\le U}}\mu(d)
 \sum_{\substack{e\ge1\\de>U}}
 \sum_{\substack{s\asymp S\\
                  (bde,s)=1\\(q,bdes)=1}}
 \mu(s)p_N(qbde)p_N(qs)\\
 &\times\sum_{v\in\mathbb Z\setminus\{0\}}
 \omega_V(v)
 \mathbf1_{j_\epsilon(bde,s,v)\ {\rm exists}}
 \widehat\Psi_{h,\epsilon}\!\left(
 \frac{bde}{R},\frac{s}{S},
 \frac{bdev-j_\epsilon(bde,s,v)s}{L},
 \frac{Hv}{s}\right).
\end{aligned}
\tag{4.8ax}
\]

The support restrictions \(bde\asymp R\) and \(qbde,q s\le N\) are
imposed exactly by the first kernel coordinate and the two displayed
\(p_N\)-weights.  The minus sign is the one in (2.2).  Summing (4.8ax)
over all \(B,V\), and partitioning \(1\le d\le U\), gives exactly the
long-cutoff insertion into (10.5) of the coefficient-first note.

For fixed \((\delta,j,b,d,v)\), set

\[
 M=bd|v|,\qquad g=(j,M).
\tag{4.8ay}
\]

There is no integral \(e\) unless \(g\mid\delta\).  When
\(g\mid\delta\), (4.8aw) is equivalent to

\[
 s\equiv
 -\frac{\delta}{g}
 \left(\frac{j}{g}\right)^{-1}
 \pmod{M/g},
 \qquad
 e=\frac{\delta+js}{bdv}>0.
\tag{4.8az}
\]

The inverse exists because \((j/g,M/g)=1\); hence gcd reduction never
enlarges the modulus.  The finite helper
long_cutoff_quotient_progression checks (4.8ay)--(4.8az) exactly.

Let \(C_0>0\) be fixed and define the integer cutoff

\[
 \boxed{
 D_{B,V}=\left\lfloor
 \frac{S^{1/2}}{4BV\mathscr L^{C_0}}
 \right\rfloor.}
\tag{4.8ba}
\]

On the support of \(\omega_B\omega_V\), \(b<2B\), \(|v|<2V\), so
every \(d\le D_{B,V}\) satisfies

\[
 bd|v|<\frac{S^{1/2}}{\mathscr L^{C_0}}.
\tag{4.8bb}
\]

Write \(B=T^\beta\), \(V=T^\nu\).  In the hard box,
\(0\le\beta\le199/200\) and \(0\le\nu\le1/2\).  Apart from the
explicit logarithmic retreat in (4.8ba), the endpoint exponents are

\[
 \kappa_D=\frac32-\beta-\nu\ge\frac1{200},
 \qquad
 \beta+\nu+\kappa_D=\frac32.
\tag{4.8bc}
\]

In the complementary range \(D_{B,V}<d\le U\), the cofactor obeys

\[
 e\ll T^{(3-\beta)-\kappa_D}\mathscr L^{C_0}
 =T^{3/2+\nu}\mathscr L^{C_0}
 \le T^2\mathscr L^{C_0}.
\tag{4.8bd}
\]

Thus this route reduces the remaining estimate to the following two
uniform local inequalities:

\[
\begin{aligned}
 \mathrm{QBV}_{\epsilon}:\quad
 &\left|\mathfrak Q_{q,\epsilon}
 (B,V;\{1\le d\le D_{B,V}\})\right|
 \ll_{A,W}T^{3499/1000}\mathscr L^{-A},\\
 \mathrm{QII}_{\epsilon}:\quad
 &\left|\mathfrak Q_{q,\epsilon}
 (B,V;\{D_{B,V}<d\le U\})\right|
 \ll_{A,W}T^{3499/1000}\mathscr L^{-A}.
\end{aligned}
\tag{4.8be}
\]

Uniformity is required in \(q,B,V,\epsilon\) and in the original kernel
seminorms.  QBV reaches the formal Bombieri--Vinogradov modulus boundary
for a length-\(S=T^3\) Möbius sum.  This exponent match is not a theorem
adapter: standard Bombieri--Vinogradov hypotheses are not verified for
(4.8ax), because the residue, its multiplicity, and the kernel are
jointly coupled to \((\delta,j,b,v,d)\).  Maximizing over the residue and
then summing those outer parameters loses the required \(2501/1000\)
power saving.  QII retains the essential pair
\(\mu(d)\mu(s)\), as well as \(\mu(b)\), and is a bilinear determinant
sum with \(e\ll T^2\mathscr L^{C_0}\).  No published result audited here
proves either inequality in (4.8be).

The function long_cutoff_quotient_split_audit records
(4.8bc)--(4.8bd), with both direct-BV and published-coverage flags false.
This is a new proof architecture, but it has not closed MD, FTF, or CMT.

### 4.6 The centered quotient form and the exact BDH deficit

The loss in QBV can be quantified before attempting a theorem adapter.
On a \(b\asymp T^\beta\), \(d\asymp T^\kappa\),
\(|v|\asymp T^\nu\), \(|j|\asymp T^\iota\) box, put

\[
 q_0=\beta+\kappa+\nu\le\frac32.
\tag{4.8bf}
\]

There are \(T^{q_0+\ell+\iota}\) progression queries in
\((b,d,v,\delta,j)\), while one residue modulo \(T^{q_0}\) has the
optimistic multiplicity \(T^{\ell+\iota-q_0}\).  At the hard endpoint
\((\ell,\iota,\sigma)=(5/2,1/2,3)\), the resulting outer coefficient
\(L^2\)-norm squared has exponent

\[
 (q_0+\ell+\iota)+(\ell+\iota-q_0)
 =2(\ell+\iota)=6.
\tag{4.8bg}
\]

Now grant the ideal common-weight variance

\[
 \sum_{m\asymp T^{q_0}}\sum_{a\bmod m}
 \left|E(m,a)\right|^2
 \ll T^{\sigma+q_0+\varepsilon}.
\tag{4.8bh}
\]

Cauchy with (4.8bg)--(4.8bh) gives only

\[
 T^{(6+3+q_0)/2+\varepsilon}
 =T^{9/2+q_0/2+\varepsilon}.
\tag{4.8bi}
\]

Relative to the FTF target \(T^{3499/1000}\), the remaining deficit is

\[
 \frac92+\frac{q_0}{2}-\frac{3499}{1000}
 =\frac{1001}{1000}+\frac{q_0}{2}.
\tag{4.8bj}
\]

It equals \(\frac{1751}{1000}\) at \(q_0=3/2\).  This is already an optimistic
calculation: the actual \(E(m,a)\) has a query-dependent transformed
kernel, so (4.8bh) is not directly available with one common weight.

The missing oscillation is exposed by inserting the long cutoff into the
double-centered finite completion (15.9) of the coefficient-first note.
With \(\mathcal C_s=(-s/2,s/2]\cap\mathbb Z\), define the exact sum

\[
\begin{aligned}
 \mathfrak Z_q(B,V;\mathcal D)
 :={}&-\sum_{b\ge1}\mu(b)\omega_B(b)
 \sum_{\substack{d\in\mathcal D\\d\le U}}\mu(d)
 \sum_{\substack{e\ge1\\de>U}}
 \sum_{\substack{s\asymp S\\
                  (bde,s)=1\\(q,bdes)=1}}
 \mu(s)p_N(qbde)p_N(qs)\frac Ss\\
 &\times
 \sum_{\substack{c,v\in\mathcal C_s\setminus\{0\}}}
 \omega_V(v)\Theta_{bde,s}(c,v)
 \left\{
 e\!\left(\frac{bdecv}{s}\right)-1
 \right\}.
\end{aligned}
\tag{4.8bk}
\]

All notation and normalization in (4.8bk) are those of
(15.3)--(15.10).  In particular,

\[
 \sum_{c\bmod s}\Theta_{r,s}(c,v)
 =\sum_{v\bmod s}\Theta_{r,s}(c,v)=0,
\tag{4.8bl}
\]

and the least absolute representatives have effective scales
\[
 |c|\ll\frac SH\mathscr L^C,\qquad
 |v|\ll\frac SL\mathscr L^C.
\tag{4.8bm}
\]
Summing (4.8bk) over \(B,V\) and partitioning \(1\le d\le U\) is exactly
the long-cutoff expansion of \(\mathfrak D_q^{(2)}[\Theta]\); no triangle
inequality or kernel separation is used.

Consequently the centered quotient theorem needed on either
\(\mathcal D=\{d\le D_{B,V}\}\) or
\(\mathcal D=\{D_{B,V}<d\le U\}\) is

\[
 \boxed{
 \mathrm{QCT}_{B,V,\mathcal D}:\qquad
 |\mathfrak Z_q(B,V;\mathcal D)|
 \ll_{A,W}T^{3999/1000}\mathscr L^{-A}.}
\tag{4.8bn}
\]

This target is the FTF target multiplied by the exact completion factor
\(S/L=T^{1/2}\).

The centered phase does create a new oscillatory resource.  If
\(E_0=R/(BD)\) is the \(e\)-length and
\(|c|\asymp T^\chi\), then its total phase variation across \(e\) is

\[
 E_0\frac{BD|cv|}{S}
 =\frac RS|cv|,
 \qquad 0\le\chi,\nu\le\frac12.
\tag{4.8bo}
\]

Even granting the full \(T^{\chi+\nu}\) as geometric cancellation, and
also granting (4.8bh), the completed bound has exponent

\[
 \frac92+\frac{q_0}{2}
 +\frac12-(\chi+\nu)
 =5+\frac{q_0}{2}-\chi-\nu.
\tag{4.8bp}
\]

At the maximal face
\((q_0,\chi,\nu)=(3/2,1/2,1/2)\), this is \(19/4\), still exceeding the
QCT target by

\[
 \frac{19}{4}-\frac{3999}{1000}
 =\frac{751}{1000}.
\tag{4.8bq}
\]

Thus neither an ideal BDH variance nor one-dimensional completion in the
unweighted quotient \(e\), even combined optimistically, proves QCT.
The remaining estimate must obtain joint cancellation involving at least
one of \(\mu(d)\), \(\mu(s)\), the \((c,v)\) double centering, or the
modulus average.  The function long_cutoff_quotient_bdh_audit records
(4.8bf)--(4.8bq); its common-weight, geometric-saving, and
published-coverage flags are all false.

### 4.7 Exact centered \(e\)-Poisson loop

The \(e\)-variable in (4.8bk) is not termwise unweighted.  Since the
left side of (2.2) is supported on squarefree \(r\), one may first write

\[
 \mu(r)
 =-\mu^2(r)
 \sum_{\substack{ab=r\\a>U}}c_U(a)\mu(b).
\tag{4.8br}
\]

After \(a=de\) and expansion of \(c_U\), (4.8br) imposes
\[
 \mu^2(bde)=1,\qquad (bde,sq)=1.
\tag{4.8bs}
\]
For fixed squarefree coprime \(b,d\), the exact remaining coefficient is
\[
\boxed{
 \mu^2(e)\mathbf1_{(e,M)=1}
 =
 \left(\sum_{k^2\mid e}\mu(k)\right)
 \left(\sum_{\ell\mid(e,M)}\mu(\ell)\right),
 \qquad M=bdsq.}
\tag{4.8bt}
\]
Equivalently, the right side is the double sum over
\(k^2\mid e\), \(\ell\mid e\), and \(\ell\mid M\).  The helper
restricted_squarefree_expansion verifies (4.8bt) for finite integers.

Put \(g=[k^2,\ell]\), write \(e=gn\), and include every smooth
\((r,s,c,v)\)-dependent factor in \(W_{c,v}(e)\).  With
\[
 \widehat W_{c,v}(\xi)
 :=\int_{\mathbb R}W_{c,v}(x)e(-\xi x)\,dx,
 \qquad
 \alpha=\frac{bdcv}{s},
\tag{4.8bu}
\]
ordinary Poisson summation gives the exact identity
\[
\boxed{
 \sum_{n\in\mathbb Z}W_{c,v}(gn)
 \{e(\alpha gn)-1\}
 =
 \frac1g\sum_{m\in\mathbb Z}
 \left\{
 \widehat W_{c,v}\!\left(\frac{m}{g}-\alpha\right)
 -
 \widehat W_{c,v}\!\left(\frac{m}{g}\right)
 \right\}.}
\tag{4.8bv}
\]

In particular, the \(m=0\) term is
\[
 \frac1g\{\widehat W_{c,v}(-\alpha)-\widehat W_{c,v}(0)\}.
\tag{4.8bw}
\]
When the oscillatory transform decays, (4.8bw) approaches
\(-g^{-1}\widehat W_{c,v}(0)\); it does not approach zero.  Hence rapid
decay of the first transform is not rapid decay of the centered
difference.

Nor does double centering remove this constant separately.  From (4.8bl),
finite inclusion--exclusion gives
\[
\boxed{
 \sum_{\substack{c\ne0\\v\ne0}}\Theta_{r,s}(c,v)
 =\Theta_{r,s}(0,0).}
\tag{4.8bx}
\]
Thus the centered minus-one mass over the nonzero frequencies is
\(-\Theta_{r,s}(0,0)\), not zero.  The finite helper
double_zero_sum_nonzero_mass checks (4.8bx) and rejects a table unless
all row and column sums vanish.

If the full \((c,v)\)-sum is retained, the apparent new transform closes
back to the original kernel.  Insert the lifted formula (4.90) from the
alternative-routes note:
\[
 \Theta_{r,s}(c,v)
 =\frac1{HL}\sum_{h,\delta}
 \Phi_{r,s}(h,\delta)
 e\!\left(-\frac{ch+v\delta}{s}\right).
\tag{4.8by}
\]
Since \((r,s)=1\), summing first in \(c\bmod s\) forces
\[
 rv\equiv h\pmod s.
\tag{4.8bz}
\]
The surviving \(v\) is \(h\bar r\bmod s\), and therefore
\[
\boxed{
 \sum_{c,v\bmod s}\Theta_{r,s}(c,v)e\!\left(\frac{rcv}{s}\right)
 =
 \frac{s}{HL}\sum_{h,\delta}
 \Phi_{r,s}(h,\delta)
 e\!\left(-\frac{h\delta\bar r}{s}\right).}
\tag{4.8ca}
\]
By (15.9), the left side of (4.8ca) is also exactly the centered
nonzero-frequency sum.  After \(r=bde\), condition (4.8bz) is
\[
 bdev-h=js.
\tag{4.8cb}
\]
This is the same determinant/Farey lattice with the two symmetric
physical variables interchanged.  In the hard box \(H=L=T^{5/2}\), so
even the scale ledger is unchanged.

Consequently an \(e\)-Poisson step has only two legitimate outcomes:
expand (4.8bt) and keep every centered transform in (4.8bv), or retain
the full double Fourier sum and return through (4.8ca) to FTF.  Dropping
the squarefree coefficient, the \(-\widehat W(0)\) term, or the
\((c,v)\)-coupling is not a valid estimate.  The function
centered_quotient_poisson_audit records this exact loop with no new
conductor reduction and no published coverage.

**centered e-Poisson status: no new conductor.**

For comparison with this new single-sector route, the remainder of
Section 4 returns to the earlier \(U=V=T\) Type-II split.

At the balanced witness, write \(B_0=T^\beta\),
\(1\leq\beta\leq2\).  The right side of SP\(_b\) has the explicit
exponent

\[
 T^{12-\beta-1/250}.
\tag{4.9}
\]

This is the exact quantity on which the full determinant phase, a valid
completion, and Kuznetsov must act.  A spectral large sieve used only
through coefficient \(L^2\) norms sees

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

### 4.8 A boundary-safe Drappeau subcell, but a hard-box no-go

The published-coverage note now records a theorem adapter that is valid only
after the exact Type identity.  In the notation
(r=b_rd_re_r), (s=b_sd_se_s), it sends the unsigned quotients
((e_r,e_s)) to Drappeau's smooth variables and the two signed products
((b_rd_r,b_sd_s)), together with (n=-h\delta), to the arbitrary
coefficient.  The reciprocal phase and coprimality condition are literal
identities, so neither Möbius side nor the product frequency is separated.

The sharp condition (d_re_r>U_r) is harmless only on a dyadic exponent
cell with

\[
 \log_T d_r+\log_T e_r>\log_T U_r
\]

by a fixed positive amount, and likewise on the (s)-side.  Equality is a
distinct uncovered boundary face.  This strict partition yields genuine
published coverage for some short-product cells; the exact witness and all
three terms of Drappeau's (K^2) are in Section 3.12 of the coverage note.

For the hard box, however, the theorem output has the exact global lower
bound (33/4), while the local target is (5999/1000).  No choice of the
two smooth quotient scales can repair the hard face, even before its
boundary cells are considered.  The hard task is therefore still the
pre-Cauchy outer-scale/slope-family cancellation isolated in Sections
4.67--4.68 of the alternative-routes note.

The finite helpers `drappeau_double_quotient_phase`,
`drappeau_double_quotient_audit`, and `drappeau_type_subcell_audit` keep the
algebraic phase, analytic exponent, and sharp-hyperbola status as separate
certificates.  A favourable exponent is never promoted to coverage on an
equality boundary.

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
