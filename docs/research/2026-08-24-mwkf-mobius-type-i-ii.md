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
                  \ B_0\leq b\leq2B_0}}
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
with \(b>V\).  No condition \((a,b)=1\) is inserted: (2.2) is valid for
all \(r\), including nonsquarefree \(r\), by cancellation among the
factorizations.

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
