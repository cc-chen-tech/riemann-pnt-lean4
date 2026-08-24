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

## 8. Exact Perron ratio and zero residues

For any \(c>0\) with \(\Re s+c>1\), the second-order Perron kernel gives

\[
 \boxed{
 M_N(s)=\frac1{\log N}\frac1{2\pi i}
 \int_{(c)}\frac{N^w}{w^2\zeta(s+w)}\,dw.}
\tag{8.1}
\]

Indeed, the Dirichlet series for \(1/\zeta(s+w)\) is absolutely
convergent on this line, \(w^{-2}\) is integrable vertically, and

\[
 \frac1{2\pi i}\int_{(c)}\frac{y^w}{w^2}\,dw
 =\begin{cases}\log y,&y>1,\\0,&0<y\leq1,\end{cases}
\tag{8.2}
\]

with the value zero at \(y=1\).  Thus termwise inversion of (8.1) is
exactly \(\log(N/n)/\log N\) for \(n<N\), and the endpoint \(n=N\)
also has weight zero.

When \(\zeta(s)\ne0\), multiplication by \(\zeta(s)\) gives the ratio
integral

\[
 \zeta(s)M_N(s)=\frac1{\log N}\frac1{2\pi i}
 \int_{(c)}\frac{\zeta(s)}{\zeta(s+w)}
 \frac{N^w}{w^2}\,dw.
\tag{8.3}
\]

The local expansion

\[
 \frac{\zeta(s)}{\zeta(s+w)}
 =1-w\frac{\zeta'}{\zeta}(s)+O_s(w^2),
 \qquad
 N^w=1+w\log N+O_N(w^2)
\]

shows that the residue at \(w=0\) is

\[
 \boxed{1-\frac1{\log N}\frac{\zeta'}{\zeta}(s).}
\tag{8.4}
\]

If \(\rho\) is a simple zeta zero and \(\rho-s\ne0\), then shifting
the contour across \(w=\rho-s\) produces the exact residue

\[
 \boxed{
 \frac{\zeta(s)N^{\rho-s}}
 {\log N\,(\rho-s)^2\zeta'(\rho)}.}
\tag{8.5}
\]

Multiple zeros give the corresponding higher principal part.  On
\(s=1/2+it\), \(N=T^3\), and \(\rho=\beta+i\gamma\), the power carried
by (8.5) is

\[
 |N^{\rho-s}|=T^{3(\beta-1/2)}.
\tag{8.6}
\]

Equations (8.4)--(8.6) explain why a direct ratio-contour proof does not
remove the unknown zero distribution.  Moreover, an infinite contour shift
cannot be justified merely from (8.3): \(1/\zeta(s+w)\) is unbounded near
its poles.  One must use finite rectangles at verified zero-avoiding heights
and retain their horizontal integrals, or introduce a new smoothing kernel.
The latter changes the exact linear mollifier unless its inverse transform
is audited separately.

Bettin--Gonek, arXiv:1604.02740, assumes the moment upper bound for every
\(2\leq N\leq T^\theta\), not only for the endpoint \(N=T^\theta\).
Under that hypothesis their \([0,T]\) theorem gives the zero-free boundary

\[
 \Re\rho\leq\frac12+\frac1{2\theta},
\tag{8.7}
\]

while their dyadic \([T,2T]\) theorem gives

\[
 \Re\rho\leq\frac12+\frac2\theta.
\tag{8.8}
\]

At \(\theta=3\), (8.7) is \(2/3\), whereas (8.8) is \(7/6\) and hence
vacuous for nontrivial zeros.  The present target concerns a smooth dyadic
interval and the single length \(N=T^3\); it does not satisfy the
all-length hypothesis.  Therefore neither Bettin--Gonek theorem can be
used as an estimate for this PR, and the target must not be advertised as
already implying their zero-free conclusion.

## 9. Uncertainty cost of isolating a bounded dual cell

In (6.2) the Fourier variable dual to the normalized \(h/H\) coordinate is

\[
 \xi=\frac{Hv}{s}.
\tag{9.1}
\]

If \(H=T^h\), \(S=T^\sigma\), and \(|v|\asymp T^\nu\), a multiplier
that isolates this dual scale has Fourier-window exponent

\[
 \omega_{\rm win}=h+\nu-\sigma.
\tag{9.2}
\]

When \(\omega_{\rm win}<0\), differentiating such a multiplier \(A\)
times costs

\[
 T^{A(\sigma-h-\nu)}.
\tag{9.3}
\]

Equivalently, Fourier inversion convolves the normalized \(h/H\) weight
over a physical scale \(T^{\sigma-h-\nu}\), expanding the original
\(h\)-support from exponent \(h\) to

\[
 h+(\sigma-h-\nu)=\sigma-\nu.
\tag{9.4}
\]

For the hard box \((h,\sigma)=(5/2,3)\), isolating bounded \(v\) means
\(\nu=0\).  Equations (9.2)--(9.4) then give

\[
 \omega_{\rm win}=-\frac12,
 \qquad
 \text{seminorm cost}=T^{A/2},
 \qquad
 \text{new }h\text{-support}=T^3=S.
\tag{9.5}
\]

Thus the fixed \(v=j=1\) expression cannot be isolated while retaining the
uniform coupled-kernel seminorms used in GCO.  Its previously computed
average-Chowla gate is a correct bound for an artificially separated cell,
but it is not a uniform necessary subproblem of the original hard box.  At
the maximal dual scale \(\nu=\sigma-h=1/2\), the cost in (9.3) is zero;
only this top scale admits a power-uniform Fourier cutoff.

This uncertainty calculation makes the routing decision precise: the
bounded dual region must remain attached to the other \(v\)-scales inside
the global operator, unless a new argument explicitly pays and recovers the
power seminorm loss in (9.3).

## 10. Exact reduction to two signed trilinear Farey sums

Split the smooth \(\delta\)-weight into its positive and negative parts,
each supported where

\[
 L/2\leq \pm\delta\leq2L.
\tag{10.1}
\]

For all sufficiently large \(T\) in the hard box,

\[
 \frac{3L}{2}<S/2.
\tag{10.2}
\]

Consequently the interval of \(j\)'s defined by (10.1) has length less
than one.  For fixed \((r,s,v)\) and a sign \(\epsilon\in\{+1,-1\}\),
there is therefore at most one integer \(j_\epsilon(r,s,v)\) satisfying

\[
 L/2\leq\epsilon(rv-j_\epsilon s)\leq2L.
\tag{10.3}
\]

When it exists, put

\[
 \delta_\epsilon(r,s,v)=rv-j_\epsilon(r,s,v)s.
\tag{10.4}
\]

The exact finite endpoint calculation used to obtain (10.3) is implemented
by `signed_shift_solutions` in
`scripts/mwkf_mobius_type_identity.py`; it uses integer floor and ceiling
only.

Define

\[
\begin{aligned}
 \mathfrak F_{q,\epsilon}[\widehat\Psi_h]
 :={}&\sum_{\substack{r\asymp R,\ s\asymp S\\
                      (r,s)=1,\ (q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)
 \sum_{v\in\mathbb Z}
 \mathbf1_{j_\epsilon(r,s,v)\ \mathrm{exists}}\\
 &\quad\ \times
 \widehat\Psi_{h,\epsilon}\left(
 \frac rR,\frac sS,
 \frac{\delta_\epsilon(r,s,v)}L,
 \frac{Hv}s
 \right).
\end{aligned}
\tag{10.5}
\]

The rapid Fourier decay in the last coordinate makes the \(v\)-sum
absolutely convergent.  Splitting (6.2) by the sign of \(\delta\) and
using uniqueness gives the exact identity

\[
 \boxed{
 \mathfrak C_q[\widehat\Psi_h]
 =\mathfrak F_{q,+}[\widehat\Psi_h]
  +\mathfrak F_{q,-}[\widehat\Psi_h].}
\tag{10.6}
\]

No triangle inequality in the size of \(v\) has been used in (10.6), so
the bounded dual values remain coupled to the full Fourier kernel.  The
effective hard-box ranges in each of the two sums are

\[
\begin{gathered}
 r,s\asymp T^3,\qquad (r,s)=1,\qquad(q,rs)=1,\\
 |v|,|j_\epsilon|\ll T^{1/2}\mathscr L^C,qquad
 \epsilon\delta_\epsilon\asymp T^{5/2},\\
 \delta_\epsilon=rv-j_\epsilon s,qquad
 p_N(qr)p_N(qs)\ne0.
\end{gathered}
\tag{10.7}
\]

The ambient \((r,s,v)\)-volume has exponent

\[
 3+3+\frac12=\frac{13}{2}.
\]

The zero-slack codimension ledger assigns relative density
\(L/S=T^{-1/2}\) to the signed Farey window and therefore records volume
exponent \(6\).  This is a scale ledger, not an equidistribution theorem for
the fractions \(rv/s\).  Against the unconditional ambient bound of
exponent \(13/2\), the target below requires saving \(3001/1000\).
Square-root cancellation at the ambient exponent would have exponent
\(13/4\), still stronger than the target by \(249/1000\).

It is sufficient to prove, uniformly for both signs and the original
kernel seminorms,

\[
 \boxed{
 |\mathfrak F_{q,\epsilon}[\widehat\Psi_h]|
 \ll_W T^{7/2-1/1000}.}
\tag{FTF\(_{\epsilon,1/1000}\)}
\]

Thus the balanced GCO problem has now been reduced to exactly two
Möbius-weighted trilinear sums in \((r,s,v)\), with \(j\) and \(\delta\)
determined by the Farey window.  This is a strictly smaller interface than
the earlier four-variable determinant lattice, but the estimate
FTF\(_{\epsilon,1/1000}\) itself is new and remains unproved.

## 11. The maximal dual box is Farey-critical

For \(v\ne0\), the determinant equation in (6.2) gives the exact rational
approximation identity

\[
 \frac rs-\frac jv=\frac{\delta}{sv}.
\tag{11.1}
\]

If \(|v|\asymp T^\nu\), the approximation-window exponent in (11.1) is

\[
 \omega_{\rm app}=\ell-\sigma-\nu,
\tag{11.2}
\]

whereas the natural Farey spacing for denominators of size \(T^\nu\) is

\[
 \omega_{\rm Farey}=-2\nu.
\tag{11.3}
\]

For fixed \(r,s,v\), the interval of eligible \(j\)'s has length

\[
 \frac LS=T^{\ell-\sigma}.
\tag{11.4}
\]

At the hard box and maximal dual scale,

\[
 (\ell,\sigma,\nu)=(5/2,3,1/2).
\]

Therefore

\[
 \frac LS=T^{-1/2}<1,
 \qquad
 \omega_{\rm app}=-1,
 \qquad
 \omega_{\rm Farey}=-1.
\tag{11.5}
\]

Thus fixed \(r,s,v\) admits at most one integer \(j\), and the surviving
condition sits exactly at the natural \(1/v^2\) Farey spacing.  There is no
spare power from either a long \(j\)-average or a separation wider than the
Farey scale.  The maximal cell is therefore more accurately described as a
Möbius-weighted critical rational-approximation operator than as a generic
third-variable Kloosterman sum.

The route comparison after the three audits is now:

| representation | exact gain | remaining obstruction | status |
|---|---:|---|---|
| coefficient-first finite convolution | \(\Lambda/\log N\) on the complete range | the pole and \(N<n\leq N^2\) boundary must cancel jointly | structural only |
| Perron ratio | explicit residues (8.4)--(8.5) | off-line zero factor \(T^{3(\beta-1/2)}\), plus contour horizontals | rejected as an unconditional estimate |
| fixed bounded dual cell | two-linear-form Möbius sum | isolation costs \(T^{A/2}\) in kernel seminorms | not a uniform necessary gate |
| full signed \(v\)-sum | one \(j\) per \((r,s,v)\); maximal scale is Farey-critical | new Möbius-weighted Farey/Kuznetsov estimate at target (7.1) | active GCO route |
| local Type I/II | exact finite identities | existing adapters retain a fixed negative exponent gap | diagnostic fallback |

Consequently the next genuinely new analytic proposition must act at the
Farey-critical scale in (11.5), retain both Möbius weights, and remain
uniform in the original Fourier kernel.  A bound proved only after a
\(T^{-1/2}\)-scale dual cutoff does not close GCO because it has already
spent the required power in (9.3).

## 12. Exact finite completion of the Farey window

There is a second exact representation of each sum in (10.5).  It exposes
the Kloosterman-fraction phase without isolating any \(v\)-cell.  For fixed
\((r,s,v)\), define a function on \(\mathbb Z/s\mathbb Z\) by

\[
 G_{r,s,v,\epsilon}(x)
 :=\sum_{\substack{\delta\in\mathbb Z\\
                    \delta\equiv x\pmod s\\
                    L/2\leq\epsilon\delta\leq2L}}
 \widehat\Psi_{h,\epsilon}\left(
  \frac rR,\frac sS,\frac\delta L,\frac{Hv}s
 \right).
\tag{12.1}
\]

The sum in (12.1) is finite.  In the hard box, \(4L<s\) for all
sufficiently large \(T\), so it contains at most one term.  Its normalized
finite Fourier transform is

\[
 \widetilde G_{r,s,v,\epsilon}(k)
 :=\frac1s\sum_{x\bmod s}G_{r,s,v,\epsilon}(x)
 e\left(-\frac{kx}{s}\right),
 \qquad
 \Omega_{r,s,v,\epsilon}(k)
 :=\frac{s}{L}\widetilde G_{r,s,v,\epsilon}(k).
\tag{12.2}
\]

Finite Fourier inversion and \(rv\equiv\delta_\epsilon\pmod s\) give,
with no truncation,

\[
 G_{r,s,v,\epsilon}(rv)
 =\frac Ls\sum_{k\bmod s}
 \Omega_{r,s,v,\epsilon}(k)
 e\left(\frac{krv}{s}\right).
\tag{12.3}
\]

Consequently (10.5) is exactly

\[
 \boxed{
 \mathfrak F_{q,\epsilon}
 =\frac LS\mathfrak D_{q,\epsilon},}
\tag{12.4}
\]

where

\[
\begin{aligned}
 \mathfrak D_{q,\epsilon}
 :={}&\sum_{\substack{r\asymp R,\ s\asymp S\\
                       (r,s)=1,\ (q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\frac Ss\\
 &\quad\times\sum_{v\in\mathbb Z}\sum_{k\bmod s}
 \Omega_{r,s,v,\epsilon}(k)
 e\left(\frac{krv}{s}\right).
\end{aligned}
\tag{12.5}
\]

Writing \(|k|_s\) for the least absolute representative modulo \(s\),
repeated finite summation by parts in (12.2), together with the original
Fourier decay in \(v\), gives for every fixed \(A\geq0\)

\[
 \Omega_{r,s,v,\epsilon}(k)
 \ll_{A,W}
 \left(1+\frac{L|k|_s}{s}\right)^{-A}
 \left(1+\frac{H|v|}{s}\right)^{-A},
\tag{12.6}
\]

The same estimate survives normalized derivatives of the continuous
kernel arguments while the finite group is fixed.  Turning these
coefficient families into a single smooth symbol across changing integer
moduli \(s\) requires residue-chart splitting; no such unproved symbol
claim is used in (12.4).  The effective, but not sharply truncated, ranges
are

\[
 |k|_s\ll\frac SL\mathscr L^C,
 \qquad
 |v|\ll\frac SH\mathscr L^C.
\tag{12.7}
\]

At the hard box both lengths are \(T^{1/2}\mathscr L^C\), and the phase
only sees their product \(a=kv\), of length at most
\(T\mathscr L^{2C}\).  The kernel still depends separately on \(k\) and
\(v\); collapsing them to a single divisor-weighted coefficient therefore
requires a kernel separation argument and is not part of the identity
(12.4).

Because \(L/S=T^{-1/2}\), FTF\(_{\epsilon,1/1000}\) is equivalent to
the normalized completed gate

\[
 \boxed{
 |\mathfrak D_{q,\epsilon}|
 \ll_W T^{4-1/1000}.}
\tag{CFK\(_{\epsilon,1/1000}\)}
\]

The ambient \((r,s,k,v)\)-volume has exponent \(7\), so CFK asks for
saving \(3001/1000\).  Its square-root exponent is \(7/2\), stronger
than the target by \(499/1000\).  Even after an optimistic lossless
collapse to a generic trilinear sum with frequency length \(T\), the two
Bettin--Chandee terms have exponents

\[
 \frac{67}{10}
 \qquad\text{and}\qquad
 \frac{53}{8}.
\tag{12.8}
\]

The first dominates and exceeds the CFK target by \(2701/1000\).
Therefore finite completion supplies a concrete Kloosterman-fraction
interface, but the generic-coefficient theorem still does not close it.
The new analytic question is whether the two Möbius weights, together with
the product structure \(a=kv\), recover that exact deficit.
