# Global coupled and coefficient-first audit for MWKF(3)

## 1. Status

This note replaces the logically excessive requirement that every fixed
Poisson-dual \((v,j)\) subbox satisfy the full coupled target.  It gives two
exact representations of the remaining problem:

1. a determinant-lattice operator in which the \(v,j\) sum is never split
   before cancellation; and
2. a coefficient-first decomposition of \(\zeta(s)M_N(s)\) into a complete
   von-Mangoldt range and an exact boundary package.

Neither representation is, by itself, an estimate.  The unconditional
\(T^3\) asymptotic remains unproved.  In particular, this note does not
promote a reformulated operator bound to a theorem.

## 2. Exact coefficient-first identity

Let

\[
 p_N(d)=1-\frac{\log d}{\log N},\qquad
 M_N(s)=\sum_{d\leq N}\frac{\mu(d)p_N(d)}{d^s}.
\]

In the half-plane of absolute convergence,

\[
 \zeta(s)M_N(s)=\sum_{n\geq1}\frac{b_N(n)}{n^s},
 \qquad
 b_N(n)=\sum_{\substack{d\mid n\\d\leq N}}
 \mu(d)p_N(d).
\tag{2.1}
\]

For \(1<n\leq N\), every divisor of \(n\) is present, and the two finite
convolution identities

\[
 \sum_{d\mid n}\mu(d)=0,
 \qquad
 \sum_{d\mid n}\mu(d)\log d=-\Lambda(n)
\tag{2.2}
\]

give

\[
 \boxed{b_N(1)=1,\qquad b_N(n)=\frac{\Lambda(n)}{\log N}
 \quad(1<n\leq N).}
\tag{2.3}
\]

There is also an exact formula beyond the boundary.  For \(n>1\), put

\[
 \mathcal D_N(n)=\{d:d\mid n,\ d>N\}.
\]

Subtracting the omitted divisors from the complete convolution yields

\[
 \boxed{
 (\log N)b_N(n)
 =\Lambda(n)+
 \sum_{d\in\mathcal D_N(n)}\mu(d)\log\frac dN.}
\tag{2.4}
\]

This is an identity of finite sums, not an asymptotic formula.

## 3. A finite zeta polynomial creates a second boundary

For an integer \(X\geq1\), define

\[
 Z_X(s)=\sum_{m\leq X}m^{-s}.
\]

Then

\[
 Z_X(s)M_N(s)=\sum_{n\leq XN}\frac{c_{X,N}(n)}{n^s},
 \qquad
 c_{X,N}(n)=
 \sum_{\substack{d\mid n\\d\leq N\\n/d\leq X}}
 \mu(d)p_N(d).
\tag{3.1}
\]

Let

\[
 \mathcal D_{X,N}(n)=
 \{d:d\mid n,\ d>N\ \text{or}\ n/d>X\}.
\tag{3.2}
\]

For every \(n>1\), exactly the same finite subtraction gives

\[
 \boxed{
 (\log N)c_{X,N}(n)
 =\Lambda(n)+
 \sum_{d\in\mathcal D_{X,N}(n)}
 \mu(d)\log\frac dN.}
\tag{3.3}
\]

In particular, the guaranteed complete-von-Mangoldt range is only

\[
 1<n\leq\min(X,N).
\tag{3.4}
\]

If \(N=T^3\) and a standard one-piece zeta truncation has
\(X=T^{1/2}\), (3.4) reaches only \(T^{1/2}\), not \(T^3\).  If one
instead takes \(X=N=T^3\), the finite product reaches \(T^6\), and its
complete part reaches \(T^3\); the analytic correction to this very long
zeta truncation cannot then be discarded.

The file `scripts/mwkf_coefficient_first.py` checks (2.3)--(3.3) as exact
prime-log vectors, so no floating-point logarithm is used in the finite
audit.

## 4. Exact critical-line boundary package

For an integer \(X\geq1\), \(\Re s>0\), and \(s\ne1\), Stieltjes
integration gives the exact Euler--Maclaurin identity

\[
 \zeta(s)=Z_X(s)+\frac{X^{1-s}}{s-1}
 -s\int_X^\infty \{u\}u^{-s-1}\,du.
\tag{4.1}
\]

Taking \(X=N\), multiplying by \(M_N(s)\), and using (3.1)--(3.4)
gives

\[
\begin{aligned}
 \zeta(s)M_N(s)
 ={}&1+\frac1{\log N}
 \sum_{2\leq n\leq N}\frac{\Lambda(n)}{n^s}
 +\sum_{N<n\leq N^2}\frac{c_{N,N}(n)}{n^s}\\
 &+\frac{N^{1-s}}{s-1}M_N(s)
 -sM_N(s)\int_N^\infty\{u\}u^{-s-1}\,du.
\end{aligned}
\tag{4.2}
\]

All five terms in (4.2) are explicit and (4.2) has no remainder.  On
\(s=1/2+it\), \(t\asymp T\), and \(N=T^3\), the pole factor has size

\[
 \left|\frac{N^{1-s}}{s-1}\right|\asymp T^{1/2},
\tag{4.3}
\]

whereas

\[
 \left|s\int_N^\infty\{u\}u^{-s-1}\,du\right|
 \leq 2|s|N^{-1/2}\ll T^{-1/2}.
\tag{4.4}
\]

Thus the long finite prime polynomial, the range \(N<n\leq N^2\), and
the pole term in (4.2) must be estimated as one boundary package.  Taking
their absolute values separately destroys cancellation at a positive power
of \(T\).  The coefficient-first identity is therefore a structural input
to the coupled argument, not a stand-alone proof by a long Dirichlet
polynomial mean-value theorem.

## 5. Joint phase audit before h-Poisson

The exact archimedean phase in the \(x,t\) kernel is

\[
 \phi(x,t)=t\log\left(1+\frac{\delta}{xr}\right)
 -\frac{2\pi hx}{s},
\]

with

\[
 \partial_x\phi(x,t)
 =-\frac{t\delta}{x(xr+\delta)}-\frac{2\pi h}{s}.
\tag{5.1}
\]

If \(h\delta>0\), the two terms in (5.1) have the same sign.  This proves
the absence of a stationary point, but a power saving by integration by
parts additionally requires a growing normalized derivative.  In exponent
notation its two phase-variation parameters are

\[
 \omega_t=1+\ell-m-\rho,
 \qquad
 \omega_h=h+m-\sigma.
\tag{5.2}
\]

If \(h\delta<0\), the stationary face is

\[
 h=\sigma+1+\ell-2m-\rho.
\tag{5.3}
\]

For the balanced hard box

\[
 (\rho,\sigma,m,\ell,h)=(3,3,1/2,5/2,5/2),
\]

(5.2)--(5.3) give

\[
 \omega_t=\omega_h=0,
 \qquad
 h=\sigma+1+\ell-2m-\rho.
\tag{5.4}
\]

Consequently the opposite-sign box is exactly stationary, while even the
same-sign box has only constant-scale oscillation.  No half of the hard
box is removed with a power saving merely by observing the sign in (5.1).

## 6. Exact determinant-lattice form of the global coupled sum

After exact Poisson summation in \(h\), the published-coverage note gives

\[
 \mathfrak S_q[\Psi]=H\mathfrak C_q[\widehat\Psi_h]
\tag{6.1}
\]

and

\[
\begin{aligned}
 \mathfrak C_q[\widehat\Psi_h]
 ={}&\sum_{\substack{r\asymp R,\ s\asymp S\\
              \delta\asymp L,\ v,j\in\mathbb Z\\
              \delta=rv-js\\(r,s)=1,\ (q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\\
 &\qquad\times
 \widehat\Psi_h\left(
  \frac rR,\frac sS,\frac\delta L,\frac{Hv}s
 \right).
\end{aligned}
\tag{6.2}
\]

For each primitive pair \((r,s)\), choose integers \((j_0,v_0)\) with

\[
 rv_0-j_0s=1.
\tag{6.3}
\]

Every integral solution of \(rv-js=\delta\) is then uniquely

\[
 \boxed{
 j=\delta j_0+kr,\qquad
 v=\delta v_0+ks,qquad k\in\mathbb Z.}
\tag{6.4}
\]

Substitution in (6.2) gives the exact primitive-column operator

\[
\begin{aligned}
 \mathfrak C_q[\widehat\Psi_h]
 ={}&\sum_{\substack{r\asymp R,\ s\asymp S\\
                      (r,s)=1,\ (q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)
 \sum_{\delta\asymp L}\sum_{k\in\mathbb Z}\\
 &\quad \widehat\Psi_h\left(
 \frac rR,\frac sS,\frac\delta L,
 \frac{H(\delta v_0+ks)}s
 \right).
\end{aligned}
\tag{6.5}
\]

Rapid decay of the Fourier transform makes the \(k\)-sum absolutely
convergent; no truncation is inserted in (6.5).  Changing the Bezout pair
in (6.3) only translates \(k\), so (6.5) is independent of that choice.

Equation (6.5), rather than a collection of absolute values of fixed
\((v,j)\) cells, is the interface for a Poincare/Kuznetsov or dispersion
argument.  The formerly isolated \(v=j=1\) average-Chowla sum remains a
valid diagnostic witness, but bounding it separately by the full target is
not a logical consequence of the original moment problem.

## 7. The remaining global inequality

The exact sufficient bound remains

\[
 \boxed{
 |\mathfrak C_q[\widehat\Psi_h]|
 \ll_W \frac{RS}{H}T^{-1/1000},}
\tag{GCO\(_{1/1000}\)}
\]

uniformly with the kernel seminorms and all ranges from the exact-audit
note.  At

\[
 R=S=T^3,\qquad H=L=T^{5/2},
\]

this is

\[
 |\mathfrak C_q[\widehat\Psi_h]|
 \ll_W T^{7/2-1/1000}.
\tag{7.1}
\]

The difference from the previous Type-I/II formulation is the order of
operations: GCO is applied to (6.2) or (6.5) before any triangle inequality
in \(v,j\).  Independently, any coefficient-first implementation must keep
the boundary package in (4.2) coupled until a cancellation mechanism has
been proved.  None of the BCR, Bettin--Chandee, Wright, or standard
shifted-convolution adapters audited in this branch proves GCO at the hard
box.  Hence the exact current status is:

**global coupled operator estimate: unproved.**
