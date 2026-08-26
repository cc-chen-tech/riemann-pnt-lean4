# Möbius-weighted long mollifier: exact off-diagonal reduction

> **Current proof status.** Exact reduction and main term verified;
> analytic remainder gate open.
>
> | component | status in this note |
> |---|---|
> | LCM main quadratic form | proved separately; its normalization is rechecked below |
> | Exact AFE and shifted-divisor identity | proved after audit in Sections 2--3 |
> | Poisson zero/nonzero-mode identity | proved after the corrections in Section 4 |
> | Coupled-kernel local estimate at length \(T^3\) | open: reduced to weighted primitive-conductor PEVP in `2026-08-25-mwkf-alternative-routes-spike.md`, Sections 4.109y--4.109zf |
> | Polylogarithmic and AFE tails | conditional on seminorm-stable PEVP; Section 4.109zg |
> | Full \(T^3\) asymptotic | unproved; one residual analytic cell remains |
>
> This note supplies the exact decomposition.  The companion route note
> audits the candidate analytic estimate and conditional final assembly;
> historical statements below are retained to show the unresolved PEVP
> dependency.

## 1. Statement and normalization

Let

\[
  N=T^3,\qquad
  p_N(n)=1-\frac{\log n}{\log N},\qquad
  a_N(n)=\mu(n)p_N(n)\mathbf 1_{n\leq N},
\]

and

\[
  M_N(s)=\sum_{n\leq N}\frac{a_N(n)}{n^s}.
\]

Throughout, \(W\in C_c^\infty(\mathbb R)\) is real and
\(\operatorname{supp}W\subset[1,2]\), and

\[
  e(x)=e^{2\pi i x},\qquad s_t=\frac12+it.
\]

The object is

\[
 I_{N,W}(T)=\int_{\mathbb R}|\zeta(s_t)|^2|M_N(s_t)|^2W(t/T)\,dt.
\]

The exact finite main term used below is

\[
\boxed{
 \mathcal Q_{N,T}
 =\sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{[d,e]}
  \int_1^2 W(u)
  \left(
    \lambda(Tu)-\log\frac{de}{(d,e)^2}+2\gamma
  \right)du, }
\tag{1.1}
\]

where

\[
 \lambda(t)=-\log\pi+\Re\frac{\Gamma'}{\Gamma}
 \left(\frac14+\frac{it}{2}\right).
\tag{1.2}
\]

Stirling's formula gives, uniformly for \(t\in[T,2T]\),

\[
 \lambda(t)=\log\frac{t}{2\pi}+O(T^{-2}).
\tag{1.3}
\]

Since

\[
 \sum_{d,e\leq N}\frac1{[d,e]}\ll (\log(2N))^3,
\tag{1.4}
\]

replacing \(\lambda(t)\) by \(\log(t/2\pi)\) in (1.1) changes
\(T\mathcal Q_{N,T}\) by \(O(T^{-1}(\log T)^3)\). Thus (1.1) is the
exact-gamma version of the BCR main quadratic form.

For this linear mollifier, the standard residue calculation for the finite
quadratic form gives

\[
 \mathcal Q_{T^3,T}
 =\frac43\int_1^2W(u)\,du+o_W(1).
\tag{1.5}
\]

Formula (1.5) is not used in the off-diagonal reduction; (1.1), not (1.5),
is the definition of the main term.

## 2. An exact approximate functional equation

The \(O(T^{-2/3})\) version used in BCR cannot simply be multiplied by a
Dirichlet polynomial of length \(T^3\): the elementary mean-value bound for
the polynomial would turn that pointwise error into a term larger than \(T\).
Use the following exact completed functional equation instead.

Put

\[
 \Lambda(s)=\gamma(s)\zeta(s),\qquad
 \gamma(s)=\pi^{-s/2}\Gamma(s/2),
\tag{2.0}
\]

so that \(\Lambda\) is meromorphic with simple poles only at \(0\) and
\(1\), and \(\Lambda(s)=\Lambda(1-s)\).  Also put

\[
 G_t(z)=e^{z^2}
 \left(1-4z^2\right)
 \left(1-\frac{z^2}{s_t^2}\right)
 \left(1-\frac{z^2}{(1-s_t)^2}\right),
\tag{2.1}
\]

and

\[
 g_t(z)=
 \frac{\gamma(s_t+z)\gamma(1-s_t+z)}
      {\gamma(s_t)\gamma(1-s_t)}.
\tag{2.2}
\]

For \(x>0\), define

\[
 V_t(x)=\frac1{2\pi i}\int_{(2)}G_t(z)g_t(z)x^{-z}\frac{dz}{z}.
\tag{2.3}
\]

### 2.1 Completion and pole cancellation

Let

\[
 \mathscr J_t=
 \frac1{2\pi i}\int_{(2)}
 G_t(z)\Lambda(s_t+z)\Lambda(1-s_t+z)\frac{dz}{z}.
\tag{2.3a}
\]

The poles of \(\Lambda(s_t+z)\) occur at \(z=-s_t,1-s_t\), and those of
\(\Lambda(1-s_t+z)\) occur at \(z=s_t-1,s_t\).  Respectively, they are
cancelled by the zeros

\[
 1-z^2/s_t^2\quad\hbox{at }-s_t,s_t,
 \qquad
 1-z^2/(1-s_t)^2\quad\hbox{at }1-s_t,s_t-1.
\]

The additional even factor \(1-4z^2\) makes
\(G_t(1/2)=G_t(-1/2)=0\).  It is not needed for the four moving poles,
but it cancels the \(z=1/2\) boundary pole that appears when the zero
Poisson mode is Mellin transformed in Section 4.  It satisfies
\(G_t(0)=1\), so it changes neither (2.3b) nor the residue at \(z=0\).

For \(V>0\), integrate around the rectangle with vertical sides
\(\Re z=2,-2\) and horizontal sides \(\Im z=\pm V\).  Stirling's formula
in fixed vertical strips, the polynomial vertical-strip bound for
\(\zeta\), and
\(|e^{(\sigma+iV)^2}|=e^{\sigma^2-V^2}\) give, uniformly for
\(-2\leq\sigma\leq2\),

\[
 \left|G_t(\sigma+iV)
 \Lambda(s_t+\sigma+iV)\Lambda(1-s_t+\sigma+iV)
 /(\sigma+iV)\right|
 \leq C_t(1+V)^{C_t}e^{-V^2}.
\tag{2.3c}
\]

Consequently both horizontal integrals tend to zero as \(V\to\infty\).
After the four cancellations above, the only pole inside the rectangle is
the pole at \(z=0\) contributed by \(1/z\), with residue
\(\Lambda(s_t)\Lambda(1-s_t)\).  Hence

\[
 \mathscr J_t=\Lambda(s_t)\Lambda(1-s_t)
 +\frac1{2\pi i}\int_{(-2)}
 G_t(z)\Lambda(s_t+z)\Lambda(1-s_t+z)\frac{dz}{z}.
\tag{2.3d}
\]

On the last integral, use the functional equation and set \(z=-w\).
The line \(\Re z=-2\), oriented upwards, becomes the line
\(\Re w=2\), oriented downwards.  The evenness of \(G_t\) and the identity
\(dz/z=dw/w\) therefore give

\[
 \frac1{2\pi i}\int_{(-2)}\cdots\frac{dz}{z}
 =-\frac1{2\pi i}\int_{(2)}
 G_t(w)\Lambda(s_t+w)\Lambda(1-s_t+w)\frac{dw}{w}
 =-\mathscr J_t.
\tag{2.3e}
\]

Consequently

\[
 2\mathscr J_t=\Lambda(s_t)\Lambda(1-s_t).
\tag{2.3b}
\]

### 2.2 Absolute convergence and termwise expansion

On \(\Re z=2\), both zeta factors have real part \(5/2\), and their
Dirichlet series have the absolute majorant

\[
 \sum_{m,n\geq1}(mn)^{-5/2}=\zeta(5/2)^2<\infty.
\tag{2.3f}
\]

For fixed \(t\), Stirling's formula makes the remaining vertical integrand
a polynomial in \(1+|\Im z|\) times \(e^{-(\Im z)^2}\).  Thus (2.3f)
and Tonelli's theorem justify expanding both zeta factors and interchanging
the double series with the integral.  Dividing (2.3b) by
\(\gamma(s_t)\gamma(1-s_t)\), then swapping the two summation names, gives
the exact identity

\[
\boxed{
 |\zeta(s_t)|^2
 =2\sum_{m,n\geq1}\frac1{\sqrt{mn}}
   \left(\frac mn\right)^{it}V_t(mn). }
\tag{2.4}
\]

There is no error term in (2.4). For every \(A,j,k\geq0\), uniformly for
\(T\leq t\leq2T\),

\[
 x^jT^k
 \left|\partial_x^j\partial_t^kV_t(x)\right|
 \leq C_{A,j,k}\left(1+\frac{x}{T}\right)^{-A}.
\tag{2.5}
\]

In particular, choosing any \(A>1/2\), the later double series has the
direct absolute majorant

\[
 \begin{aligned}
 \sum_{m,n\geq1}\frac1{\sqrt{mn}}
 \left(1+\frac{mn}{T}\right)^{-A}
 &=\sum_{v\geq1}\frac{d(v)}{\sqrt v}
   \left(1+\frac vT\right)^{-A}<\infty.
 \end{aligned}
\tag{2.5a}
\]

Indeed, for any \(0<\epsilon<A-1/2\), the tail is bounded using
\(d(v)\ll_\epsilon v^\epsilon\); the initial segment is finite.

### 2.3 Uniform weight bounds

Here are the details behind (2.5).  On a vertical line \(\Re z=c\),
\(x^j\partial_x^j x^{-z}=(-z)(-z-1)\cdots(-z-j+1)x^{-z}\).
Moreover, repeated \(t\)-differentiation of \(g_t(z)G_t(z)\) produces
finite sums of products of:

* that degree-\(j\) polynomial in \(z\);
* differences of polygamma functions at arguments separated by \(z/2\);
* derivatives of \(s_t^{-2}\) and \((1-s_t)^{-2}\).

Uniform Stirling expansions for \(T\leq t\leq2T\), after splitting the
vertical integral into \(|\Im z|\leq T/2\) and its Gaussian tail, give

\[
 \left|\partial_t^k\{G_t(z)g_t(z)\}\right|
 \leq C_{c,j,k}T^{c-k}(1+|z|)^{C_{c,j,k}}
 e^{-(\Im z)^2/2}.
\tag{2.5b}
\]

For \(x\geq T\), shift (2.3) to \(\Re z=A\); no pole is crossed and
(2.5b) gives \(x^jT^k|\partial_x^j\partial_t^kV_t(x)|
\ll_{A,j,k}(T/x)^A\).  For \(x\leq T\), shift to a fixed line
\(\Re z=-c\), \(0<c<1/4\).  When \(j=k=0\), the crossed residue is \(1\);
when \(j+k>0\), it is zero (the \(x\)-multiplier vanishes at \(z=0\), or
the residue \(G_t(0)g_t(0)=1\) is independent of \(t\)).  The new-line
integral is \(O_{j,k}((x/T)^c)\).  These two estimates prove (2.5), with
no factor \(T^{\epsilon_{j,k}}\).

Expanding the mollifier in (2.4) gives the exact twisted-moment formula

\[
\boxed{
 I_{N,W}(T)=
 2\sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{\sqrt{de}}
 \sum_{m,n\geq1}\frac{\mathcal K_T(m,n;d,e)}{\sqrt{mn}}, }
\tag{2.6}
\]

where

\[
 \mathcal K_T(m,n;d,e)=
 \int_{\mathbb R}W(t/T)V_t(mn)
 \exp\left(it\log\frac{me}{nd}\right)dt.
\tag{2.7}
\]

For fixed \(d,e\), (2.6) is the expansion of

\[
 \mathcal T_{d,e}(T)
 =\int_{\mathbb R}|\zeta(s_t)|^2(e/d)^{it}W(t/T)\,dt.
\]

Explicitly,

\[
\boxed{
 \mathcal T_{d,e}(T)
 =2\sum_{m,n\geq1}\frac1{\sqrt{mn}}
 \int_{\mathbb R}W(t/T)V_t(mn)
 \exp\left(it\log\frac{me}{nd}\right)dt, }
\tag{2.7a}
\]

and

\[
 I_{N,W}(T)=
 \sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{\sqrt{de}}\,
 \mathcal T_{d,e}(T).
\tag{2.7b}
\]

The diagonal equation is

\[
 me=nd.
\tag{2.8}
\]

Writing \(g=(d,e)\), \(d=gd^*\), \(e=ge^*\), it has precisely the
solutions

\[
 m=\ell d^*,\qquad n=\ell e^*,\qquad \ell\geq1.
\tag{2.9}
\]

Consequently its contribution is exactly

\[
 \mathcal D=
 2\sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{[d,e]}
 \int_{\mathbb R}W(t/T)
 \sum_{\ell\geq1}\frac{V_t(\ell^2d^*e^*)}{\ell}\,dt.
\tag{2.10}
\]

## 3. Exact shifted-divisor remainder

Choose once and for all \(F\in C_c^\infty([1/2,2])\) satisfying

\[
 \sum_{j\in\mathbb Z}F(x/2^j)=1\qquad(x>0),
\tag{3.1}
\]

and put \(F_X(x)=F(x/X)\), \(X\in2^{\mathbb Z}\). Define

\[
 \Delta=me-nd.
\tag{3.2}
\]

For dyadic \(D,E,M_1,M_2\), let

\[
\begin{aligned}
 \mathcal O(D,E,M_1,M_2)
 ={}&2\sum_{\substack{d,e,m,n\geq1\\me-nd\ne0}}
 \frac{a_N(d)a_N(e)}{\sqrt{demn}}
 F_D(d)F_E(e)F_{M_1}(m)F_{M_2}(n)\\
 &\quad\times
 \int_{\mathbb R}W(t/T)V_t(mn)
 \exp\left(it\log\left(1+\frac{me-nd}{nd}\right)\right)dt.
\end{aligned}
\tag{3.3}
\]

The countable sum in (3.3) is absolutely convergent by (2.5), and
opening the two mollifier sums causes no convergence issue because they are
finite.  For every fixed positive integer \(x\), only finitely many dyadic
factors \(F_X(x)\) are nonzero (in fact at most three for the support in
(3.1)).  Hence the four dyadic partitions may be inserted term by term and
then interchanged with the absolutely convergent off-diagonal sum.  Equation
(3.1) is an identity on \((0,\infty)\), so this reindexing produces neither
an endpoint term nor a limiting boundary term.  Therefore

\[
 I_{N,W}(T)=\mathcal D+
 \sum_{D,E,M_1,M_2}\mathcal O(D,E,M_1,M_2).
\tag{3.4}
\]

Thus an exact, non-asymptotic remainder formula is already

\[
\boxed{
 \mathcal R_{N,T}
 =\mathcal D-T\mathcal Q_{N,T}
  +\sum_{D,E,M_1,M_2}\mathcal O(D,E,M_1,M_2). }
\tag{3.5}
\]

No truncation is hidden in (3.5).

The box in (3.3) is a shifted-divisor box with the exact conditions

\[
\begin{gathered}
 D/2\leq d\leq2D,\qquad E/2\leq e\leq2E,\\
 M_1/2\leq m\leq2M_1,\qquad M_2/2\leq n\leq2M_2,\\
 me-nd=\Delta\ne0.
\end{gathered}
\tag{3.6}
\]

The phase and the full smooth weight are respectively

\[
 \Phi_{\Delta,n,d}(t)=t\log\left(1+\frac{\Delta}{nd}\right),
\tag{3.7}
\]

and

\[
 \frac{2a_N(d)a_N(e)}{\sqrt{demn}}
 F_D(d)F_E(e)F_{M_1}(m)F_{M_2}(n)W(t/T)V_t(mn).
\tag{3.8}
\]

Equations (3.3), (3.6), (3.7), and (3.8) give the requested exact
shifted-divisor formulation without using the words “approximately” or
“similar to”.

## 4. Exact Poisson/Kloosterman-fraction formula

### 4.1 Residue class and Poisson normalization

To retain the Möbius coefficients, Poisson summation must be applied to a
zeta variable, not to \(d\) or \(e\). Use the BCR orientation

\[
 m_1e-m_2d=\Delta.
\tag{4.1}
\]

Write

\[
 q=(d,e),\qquad d=qr,\qquad e=qs,\qquad (r,s)=1.
\tag{4.2}
\]

Then \(q\mid\Delta\). Put \(\Delta=q\delta\). Equation (4.1) becomes

\[
 m_1s-m_2r=\delta,
\qquad
 m_2r\equiv-\delta\pmod s,
 \qquad
 m_1=\frac{m_2r+\delta}{s}.
\tag{4.3}
\]

Because \((r,s)=1\), this is the single residue class

\[
 m_2\equiv-\bar r\delta\pmod s.
\tag{4.3a}
\]

Our Fourier convention is

\[
 \widehat f(\xi)=\int_{\mathbb R}f(x)e(-\xi x)\,dx,
 \qquad
 \sum_{n\equiv b\ ({\rm mod}\ s)}f(n)
 =\frac1s\sum_{h\in\mathbb Z}e(hb/s)\widehat f(h/s).
\tag{4.3b}
\]

For fixed \(r,s,\delta\), extend the smooth dyadic summand by zero unless
\(x>0\) and \(xr+\delta>0\).  Formula (4.3b), with
\(b=-\bar r\delta\), supplies the factor \(s^{-1}\), the Fourier factor
\(e(-hx/s)\), and the arithmetic phase
\(e(-h\delta\bar r/s)\).  Multiplication by the coefficient already
present before Poisson, \(2/(q\sqrt{rs})\), therefore gives exactly
\(2/(q\sqrt{rs}\,s)\), as displayed below.

For dyadic \(R,S,K,M\), define

\[
\begin{aligned}
 \mathscr K_{R,S,K,M}(r,s;\delta,h)
 ={}&\int_0^\infty
 \frac{F_M(x)F_K((xr+\delta)/s)}
 {\sqrt{x(xr+\delta)/s}}
 e(-hx/s)\\
 &\times\int_{\mathbb R}W(t/T)
 V_t\left(\frac{x(xr+\delta)}s\right)
 \exp\left(it\log\left(1+\frac{\delta}{xr}\right)\right)dt\,dx.
\end{aligned}
\tag{4.4}
\]

The integrand is declared to be zero when \(xr+\delta\leq0\). Poisson
summation in the residue class
\(m_2\equiv-\bar r\delta\pmod s\) gives

\[
\boxed{
\begin{aligned}
 \mathcal O^{\ne0}_{q;R,S,K,M}
 ={}&\frac2q
 \sum_{\substack{r,s\geq1\\(r,s)=1}}
 \frac{a_N(qr)a_N(qs)F_R(r)F_S(s)}{\sqrt{rs}\,s}\\
 &\times
 \sum_{\delta\ne0}\sum_{h\ne0}
 e\left(-\frac{h\delta\bar r}{s}\right)
 \mathscr K_{R,S,K,M}(r,s;\delta,h).
\end{aligned}}
\tag{4.5}
\]

Here \(\bar r\) is the inverse of \(r\bmod s\). Formula (4.5) is exact and
contains all nonzero Poisson modes.

### 4.2 Zero mode from a common Mellin integral

We next sum the \(K,M\) partitions in (4.4) before doing any Mellin
inversion.  The positivity condition remains \(x>0\) and \(xr+\delta>0\).
For fixed \(q,r,s\), the resulting \(h=0\) expression is

\[
\begin{aligned}
 Z_{q,r,s}={}&\frac{2a_N(qr)a_N(qs)}{q\sqrt{rs}\,s}
 \sum_{\delta\ne0}\int_0^\infty
 \mathbf1_{xr+\delta>0}\frac{dx}{\sqrt{x(xr+\delta)/s}}\\
 &\quad\times\int_{\mathbb R}W(t/T)
 V_t\!\left(\frac{x(xr+\delta)}s\right)
 \exp\!\left(it\log\left(1+\frac{\delta}{xr}\right)\right)dt.
\end{aligned}
\tag{4.5a}
\]

This order of summation is important.  There is no vertical line on which
one may naively insert (2.3), integrate \(x\), and sum \(\delta\) all by
absolute convergence: the beta integral asks for \(\Re z<1/2\), whereas
\(\sum_{\delta\ge1}\delta^{-2z}\) asks for \(\Re z>1/2\).  The baseline
derivation omitted this incompatibility.  The following common-kernel
calculation resolves it; the zero \(G_t(1/2)=0\) added in (2.1) is essential.

For \(0<c<1/4\), introduce symmetric cutoffs
\(|\delta|\leq Y\) and \(Y^{-1}\leq x,(xr+\delta)/s\leq Y\).
All sums and integrals are then finite.  First shift (2.3), without crossing
a pole, from \(\Re z=2\) to a fixed \(\Re z=\sigma\) with
\(1/2<\sigma<1\).  This choice lies to the left of the first uncancelled
moving beta poles at \(z=s_t+1\) and \(z=2-s_t\).  Insert that
representation, split the two signs of \(\delta\), and use respectively

\[
 x=\frac{\delta v}{r}\quad(\delta>0,\ v>0),
 \qquad
 x=\frac{|\delta|(1+v)}r\quad(\delta<0,\ v>0).
\tag{4.5b}
\]

The two complete beta integrals obtained after removing the cutoffs are

\[
\begin{aligned}
 B_+(t,z)&=
 \frac{\Gamma(1-s_t-z)\Gamma(2z)}
      {\Gamma(1-s_t+z)},\\
 B_-(t,z)&=
 \frac{\Gamma(s_t-z)\Gamma(2z)}
      {\Gamma(s_t+z)}.
\end{aligned}
\tag{4.5c}
\]

To justify removal of the cutoffs, first keep the incomplete beta integrals,
move their common Mellin line from \(\Re z=\sigma\) to \(\Re z=c\), and only
then let \(Y\to\infty\).  Euler--Maclaurin applied to the truncated
\(\delta\)-sum shows that its sole boundary term is the residue at
\(z=1/2\); the moving poles at \(s_t,1-s_t\) are cancelled by (2.1), and
the next such poles lie to the right of \(\sigma\).  The \(z=1/2\) term
vanishes because \(G_t(1/2)=0\).  The remaining boundary
integrals are
\(O_{A,t,r,s}(Y^{-A})\) after \(A+2\) integrations by parts in the logarithmic
variable in (4.5a), using (2.5).  Thus dominated convergence applies on
\(\Re z=c\).  This proves, rather than assumes, the regularized common
Mellin identity

\[
\begin{aligned}
 \sum_{R,S,K,M}\mathcal O^{h=0}_{q;R,S,K,M}
 ={}&\frac2{2\pi i}
 \sum_{\substack{r,s\ge1\\(r,s)=1}}
 \frac{a_N(qr)a_N(qs)}{qrs}
 \int_{\mathbb R}W(t/T)\\
 &\times\int_{(c)}(rs)^z\zeta(2z)g_t(z)G_t(z)
 H_t(z)\frac{dz}{z}\,dt,
\end{aligned}
\tag{4.5d}
\]

where the integral on \(\Re z=c\) is the continuation furnished by the
cutoff limit and

\[
 H_t(z)=\Gamma(2z)\left{
 \frac{\Gamma(s_t-z)}{\Gamma(s_t+z)}
 +\frac{\Gamma(1-s_t-z)}{\Gamma(1-s_t+z)}
 \right}.
\tag{4.5e}
\]

The duplication and reflection formulas for \(\Gamma\), followed by the
functional equation of \(\zeta\), give the exact meromorphic identity

\[
 \boxed{\zeta(2z)g_t(z)H_t(z)
 =C_t(z)\zeta(1-2z)g_t(-z),}
\tag{4.5f}
\]

where

\[
 C_t(z)=\frac1{2\cos(\pi z)}\left{
 \frac{\sin(\frac\pi2(1-s_t-z))}
      {\sin(\frac\pi2(1-s_t+z))}
 +\frac{\sin(\frac\pi2(s_t-z))}
      {\sin(\frac\pi2(s_t+z))}
 \right}.
\tag{4.5g}
\]

Thus the baseline replacement \(C_t(z)=1\) was not an exact identity.
There is no arithmetic Euler factor in (4.5f): after \(q=(d,e)\), the only
condition is \((r,s)=1\), and \(\delta\) is unrestricted.  Split
\(C_t=1+(C_t-1)\).  In the term with 1, set \(z=-w\); the upward
\((c)\)-line becomes the downward \((-c)\)-line.  Retain the other term as
the exact archimedean correction

\[
\begin{aligned}
 \mathcal E_{\rm arch}:={}&\frac2{2\pi i}
 \sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{[d,e]}
 \int_{\mathbb R}W(t/T)\\
 &\times\int_{(c)}(d^*e^*)^zG_t(z)\zeta(1-2z)g_t(-z)
 \bigl(C_t(z)-1\bigr)\frac{dz}{z}\,dt.
\end{aligned}
\tag{4.5h}
\]

For \(z=c+i\tau\), \(0<c<1/4\), the elementary exponential formulas for
the sines in (4.5g) show, when \(|\tau|\leq T/2\),

\[
 |C_t(c+i\tau)-1|\ll_c e^{-\pi T/2}(1+|\tau|)^2.
\tag{4.5i}
\]

When \(|\tau|>T/2\), the factor
\(|e^{z^2}|=e^{c^2-\tau^2}\), together with Stirling, bounds the integrand
in (4.5h) by \(e^{-\tau^2/2}T^{O_c(1)}\).  Since the \(d,e\)-sum is finite
and is at most \(T^{O_c(1)}\) under \(N=T^3\), (4.5i) and the Gaussian tail
give, for every \(A>0\),

\[
 \boxed{\mathcal E_{\rm arch}=O_{A,W}(T^{-A}).}
\tag{4.5j}
\]

Adding the diagonal (2.10), Mellin inversion gives

\[
 \mathcal D=
 \frac2{2\pi i}
 \sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{[d,e]}
 \int_{\mathbb R}W(t/T)
 \int_{(2)}
 (d^*e^*)^{-z}\zeta(1+2z)g_t(z)G_t(z)\frac{dz}{z}\,dt,
\tag{4.6a}
\]

so its factor \((d^*e^*)^{-z}\zeta(1+2z)g_t(z)G_t(z)\) agrees prime by
prime and power by power with (4.6b).  The sole discrepancy is the
archimedean factor \(\mathfrak A_t(z)\).

### 4.3 Residue and main-term normalization

Add and subtract the \((-c)\)-line without \(\mathfrak A_t\).  The difference
of the two common Mellin integrals crosses only \(z=0\), while the remaining
exact term is

\[
\begin{aligned}
 \sum_{q,R,S,K,M}\mathcal O^{h=0}_{q;R,S,K,M}
 ={}&-\frac2{2\pi i}
 \sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{[d,e]}
 \int_{\mathbb R}W(t/T)
 \int_{(-c)}
 (d^*e^*)^{-z}\zeta(1+2z)g_t(z)G_t(z)\frac{dz}{z}\,dt\\
 &+\mathcal E_{\rm arch}.
\end{aligned}
\tag{4.6b}
\]

The phrase “every interchange is absolutely convergent on an initial line”
in the baseline was false; (4.5b)--(4.5g) is the corrected cutoff argument.
After that correction, subtracting the two vertical integrals in
(4.6a)--(4.6b) crosses only \(z=0\). Hence

\[
 \mathcal D+\sum_{q,R,S,K,M}\mathcal O^{h=0}_{q;R,S,K,M}
 =T\mathcal Q_{N,T}+\mathcal E_{\rm arch}.
\tag{4.6}
\]

### 4.3 Residue and main-term normalization

At \(z=0\), use

\[
 \zeta(1+2z)=\frac1{2z}+\gamma+O(z),\qquad
 (d^*e^*)^{-z}=1-z\log(d^*e^*)+O(z^2),
\tag{4.6c}
\]

and

\[
 g_t(z)=1+z\lambda(t)+O_t(z^2),\qquad
 G_t(z)=1+O_t(z^2).
\tag{4.6d}
\]

The added factor \(1-4z^2\) in \(G_t\) has no linear term.  Multiplying
(4.6c)--(4.6d), then accounting for the outer \(1/z\), gives the following
residue at \(z=0\):

\[
\begin{gathered}
 \zeta(1+2z)=\frac1{2z}+\gamma+O(z),\qquad
 (d^*e^*)^{-z}=1-z\log(d^*e^*)+O(z^2),\\
 g_t(z)=1+z\lambda(t)+O_t(z^2),\qquad
 G_t(z)=1+O_t(z^2).
\end{gathered}
\tag{4.7a}
\]

They give

\[
\begin{aligned}
 \operatorname{Res}_{z=0}
 \left(
  (d^*e^*)^{-z}\zeta(1+2z)g_t(z)\frac{G_t(z)}z
 \right)
 &=\frac12\left(\lambda(t)-\log(d^*e^*)+2\gamma\right),\\
 \operatorname{Res}_{z=0}
 \left(
  (d^*e^*)^{-z}\zeta(1+2z)g_t(z)G_t(z)
  \frac{1-\mathfrak A_t(z)}z
 \right)
 &=-\frac{\pi}{2\cosh(\pi t)}.
\end{aligned}
\tag{4.7}
\]

The first line is the requested main residue.  The outer factor 2 in (2.4)
turns it into the bracket in (1.1).  Also

\[
 d^*e^*=rs=\frac{de}{(d,e)^2},\qquad
 -\log(d^*e^*)=2\log(d,e)-\log d-\log e,
\tag{4.7b}
\]

which is the logarithm in the independently proved LCM normalization.  The
second line of (4.7) records why the correction cannot be erased in an exact
identity.  To bound the complete correction, first use
\(|a_N(n)|\leq1\), \((d^*e^*)^c\leq N^{2c}\), and the finite gcd expansion

\[
\begin{aligned}
 \sum_{d,e\leq N}\frac1{[d,e]}
 &=\sum_{k\leq N}\frac{\varphi(k)}{k^2}
   H_{\lfloor N/k\rfloor}^2
 \leq(1+\log N)^2\sum_{k\leq N}\frac1k
 \ll\log^3(2N),\\
 \sum_{d,e\leq N}
 \frac{|a_N(d)a_N(e)|}{[d,e]}(d^*e^*)^c
 &\leq N^{2c}\sum_{d,e\leq N}\frac1{[d,e]}
 \ll N^{2c}\log^3(2N).
\end{aligned}
\tag{4.7c.0}
\]

The first equality follows from
\((d,e)=\sum_{k\mid d,\ k\mid e}\varphi(k)\), followed by
\(d=kd'\), \(e=ke'\); thus (4.7c.0) needs no external estimate.  On
\(z=-c+iv\),

\[
 1-\mathfrak A_t(z)
 =-\frac{\sin(\pi z)}{\cosh(\pi t)-\sin(\pi z)}.
\]

Since \(0<c<1/4\), direct comparison of numerator and denominator gives

\[
\begin{aligned}
 |1-\mathfrak A_t(-c+iv)|
 &\ll_c e^{-\pi(t-|v|)},&& |v|\leq t/2,\\
 |1-\mathfrak A_t(-c+iv)|
 &\leq1\leq2,&& |v|>t/2.
\end{aligned}
\tag{4.7c.1}
\]

Indeed, the central estimate uses
\(|\sin(\pi(-c+iv))|\ll_c e^{\pi|v|}\) and
\(\cosh(\pi t)\asymp e^{\pi t}\).  For the second estimate,
\(\Re\sin(\pi(-c+iv))<0\), and
\[
 |\cosh(\pi t)-\sin(\pi(-c+iv))|^2
 -|\sin(\pi(-c+iv))|^2
 =\cosh^2(\pi t)
  +2\sin(\pi c)\cosh(\pi t)\cosh(\pi v)>0.
\]

Apply (2.5i) on \(\Re z=-c\) and the polynomial vertical-strip bound for
\(\zeta(1-2c+2iv)\).  On \(|v|\leq t/2\), (4.7c.1) contributes
\(e^{-\pi t/2}\); on the complement, the Gaussian in \(G_t\) contributes
\(e^{-t^2/9}\), after absorbing every polynomial in \(v\).  Equations
(4.7c.0)--(4.7c.1), the length-\(T\) \(t\)-integral, and (2.5i) therefore give

\[
 |\mathcal C_{N,W}(T)|
 \ll_{c,W}
 T^{1-c}N^{2c}\log^3(2N)
 \left(e^{-\pi T/2}+e^{-T^2/9}\right).
\tag{4.7c.2}
\]

For \(N=T^3\), the right side is beyond all polynomial orders:

\[
 \mathcal C_{T^3,W}(T)=O_{B,W}(T^{-B})\qquad(B>0).
\tag{4.7c}
\]

Thus the exact correction is negligible for the later global estimate,
but it remains present in every exact formula.

zero-mode audit result: the baseline identity required correction;
(4.6b) contains the remaining archimedean factor \(\mathfrak A_t(z)\), and
(4.6), (4.6c), and (4.8) contain the remaining term
\(\mathcal C_{N,W}(T)\).

Combining (4.5) with the corrected (4.6) proves the exact decomposition

\[
\boxed{
 I_{N,W}(T)=T\mathcal Q_{N,T}+\mathcal R_{N,T},\qquad
 \mathcal R_{N,T}=
 \mathcal E_{\rm arch}+
 \sum_{q\geq1}\sum_{R,S,K,M}
 \mathcal O^{\ne0}_{q;R,S,K,M}. }
\tag{4.8}
\]

The nonzero-mode sum in (4.8) is taken in the complete dyadic Poisson
ordering used above.  The convergence supplied by (2.5) and repeated
integration by parts in \(t\) justifies that limit; no rearrangement of
individual Fourier modes and no truncated-AFE error is hidden in (4.8).

Since \(d^*e^*=de/(d,e)^2\), the logarithm in (4.7) is
\(2\log(d,e)-\log d-\log e\), exactly the LCM normalization used in the
separate main-term calculation.

**zero-mode audit result: the baseline identity required correction;** the
kernel (2.1) now contains \(1-4z^2\), and the incompatible raw Fubini step
has been replaced by the cutoff/common-Mellin argument (4.5b)--(4.5e).
Most importantly, the exact trigonometric multiplier \(C_t(z)\) in
(4.5f)--(4.5g) is retained.  Its difference from 1 is the explicit term
\(\mathcal E_{\rm arch}\), not a suppressed equality; (4.5j) makes this
correction smaller than every power of \(T\).  Equations (4.6a)--(4.8) are
the corrected identities.

## 5. Möbius support and all effective variable ranges

If \(a_N(qr)a_N(qs)\ne0\), then

\[
 q,r,s\text{ are squarefree},\qquad
 (q,r)=(q,s)=(r,s)=1,
\tag{5.1}
\]

and

\[
 a_N(qr)a_N(qs)
 =\mu(r)\mu(s)p_N(qr)p_N(qs).
\tag{5.2}
\]

Thus the common divisor carries no Möbius sign; both reduced variables
retain Möbius weights.

Put \(\mathscr L=\log(2T)\).  Fix a tail target \(D>20\), and then choose
an integer \(B=B(D,W)\geq100\).  Call the boxes satisfying (5.3)--(5.8)
the **polylogarithmic core**, and denote the exact sum of all remaining
nonzero modes by \(\mathcal R_{\rm tail}^{(B)}\).  Then (4.8) gives

\[
 \mathcal R_{N,T}=\mathcal E_{\rm arch}
 +\mathcal R_{\rm tail}^{(B)}
 +\sum_{\text{core }q,R,S,K,M,L,H}
  \mathcal O^{\ne0}_{q;R,S,K,M,L,H}.
\tag{5.2a}
\]

The core boxes satisfy

\[
 1\leq q,\qquad qR/2\leq N,\qquad qS/2\leq N;
\tag{5.3}
\]

\[
 R/2\leq r\leq2R,\qquad S/2\leq s\leq2S;
\tag{5.4}
\]

\[
 M/2\leq m_2\leq2M,\qquad K/2\leq m_1\leq2K;
\tag{5.5}
\]

\[
 KM\leq T\mathscr L^B;
\tag{5.6}
\]

\[
 \frac1{16}\leq\frac{KS}{MR}\leq16;
\tag{5.7}
\]

In particular,

\[
 M\leq4(T\mathscr L^B)^{1/2}\sqrt{\frac SR},\qquad
 K\leq4(T\mathscr L^B)^{1/2}\sqrt{\frac RS}.
\tag{5.7a}
\]

\[
 1\leq |\delta|\leq \frac{8MR}{T}\mathscr L^B,\qquad
 1\leq |h|\leq \frac{8S}{M}\mathscr L^B.
\tag{5.8}
\]

A retained nonempty box must consequently also satisfy

\[
 MR\geq\frac{T}{8\mathscr L^B},\qquad
 S\geq\frac{M}{8\mathscr L^B}.
\tag{5.8a}
\]

Here are the two integrations by parts used for (5.8).  With

\[
 \Phi_t(t)=t\log\left(1+\frac\delta{xr}\right),\qquad
 \mathcal L_t=
 \frac1{i\log(1+\delta/(xr))}\frac d{dt},
\tag{5.8b}
\]

we have \(\mathcal L_t e^{i\Phi_t}=e^{i\Phi_t}\).  The bounds (2.5) and
the derivatives of \(W(t/T)\) show that \(J\) integrations contribute
\(\ll_J(T|\log(1+\delta/(xr))|)^{-J}\).  Outside
\(|\log(1+\delta/(xr))|\leq\mathscr L^B/T\), this gives a
\(\mathscr L^{-BJ}\) seminorm gain for each kernel.  On dyadic support the
complementary logarithmic inequality implies the first core bound in (5.8).

For the Poisson phase use

\[
 \mathcal L_x=-\frac{s}{2\pi i h}\frac d{dx},\qquad
 \mathcal L_x e(-hx/s)=e(-hx/s).
\tag{5.8c}
\]

On the retained \(\delta\)-range, every \(x\)-derivative of the other
factors in (4.4) costs at most \(C_j\mathscr L^{Bj}/M^j\).  Hence \(J\)
integrations with \(\mathcal L_x\) give a \(\mathscr L^{-BJ}\) kernel
seminorm gain unless the second core bound in (5.8) holds.  A Mellin shift
in (2.3) gives analogous rapid seminorm decay outside (5.6).  Finally,
(4.3), (5.5), and the retained \(\delta\)-range give (5.7).

These pointwise seminorm gains do **not** by themselves prove
\(\mathcal R_{\rm tail}^{(B)}=o(T)\).  Indeed, the elementary absolute
majorants

\[
 \left(\sum_{d\leq T^3}\frac{|a_N(d)|}{\sqrt d}\right)^2
 \ll T^3,
 \qquad
 \sum_{m,n\geq1}\frac1{\sqrt{mn}}
 \left(1+\frac{mn}{T}\right)^{-A}\ll_A T^{1/2}\mathscr L
\tag{5.8d}
\]

leave a crude integrated scale \(T^{9/2}\mathscr L\).  No fixed power of
\(\mathscr L^{-1}\) removes the resulting \(T^{7/2}\) gap.  Thus the
polylogarithmic tail requires a Möbius-sensitive estimate and remains an
explicit analytic obligation below.

The constants 8 and 16 in (5.7)--(5.8) follow from the fixed support
\([1/2,2]\) in (3.1). They may be replaced by other fixed constants only if
the dyadic partition is changed.

Dyadically write

\[
 L\leq|\delta|\leq2L,\qquad H\leq|h|\leq2H.
\tag{5.9}
\]

Every retained box therefore satisfies

\[
 1\leq L\leq\frac{8MR}{T}\mathscr L^B,\qquad
 1\leq H\leq\frac{8S}{M}\mathscr L^B,
\tag{5.10}
\]

and hence

\[
 A:=LH\leq\frac{64RS}{T}\mathscr L^{2B}.
\tag{5.11}
\]

The oscillating arithmetic phase is exactly

\[
 e\left(-\frac{h\delta\bar r}{s}\right)
 =e\left(-\frac{a\bar r}{s}\right),\qquad a=h\delta.
\tag{5.12}
\]

At zero slack, write

\[
 (R,S,M,K,L,H,q)
 =(T^\rho,T^\sigma,T^m,T^k,T^\ell,T^h,T^\kappa).
\tag{5.12a}
\]

Equations (5.3), (5.6), (5.7), and (5.10) give the exponent polytope

\[
\begin{gathered}
 \kappa+\rho\leq3,\qquad \kappa+\sigma\leq3,\qquad
 k+m\leq1,\qquad k+\sigma=m+\rho,\\
 \ell\leq m+\rho-1,\qquad h\leq\sigma-m,\qquad
 a:=\ell+h\leq\rho+\sigma-1.
\end{gathered}
\tag{5.12b}
\]

Combining \(k+m\leq1\) with \(k+\sigma=m+\rho\) also gives

\[
 m\leq\frac{1+\sigma-\rho}{2},\qquad
 k\leq\frac{1+\rho-\sigma}{2}.
\tag{5.12c}
\]

The exact-rational script checks these linear implications and boundary
witnesses only.  It is a regression tool, not a proof of the analytic
truncations above.

After the changes \(x=MX\), \(t=T\tau\), the archimedean kernel in a
retained box has the normalization

\[
 \mathscr K_{R,S,K,M}(r,s;\delta,h)
 =T\sqrt{\frac SR}\,\Psi_{R,S,K,M,L,H}
 \left(\frac rR,\frac sS,\frac\delta L,\frac hH\right),
\tag{5.13}
\]

This scale can be read directly from the coupled kernel, without a Taylor
expansion.  Put

\[
 \lambda_0=\frac{L}{MR},\qquad
 \omega_0=\frac{HM}{S},\qquad
 \chi_0=\frac{M^2R}{ST},\qquad
 (u,v,\alpha,\beta)=
 \left(\frac rR,\frac sS,\frac\delta L,\frac hH\right).
\tag{5.13a}
\]

Apart from the fixed dyadic cutoffs, the dimensionless kernel in (5.13) is

\[
\begin{aligned}
 \Psi^\circ(u,v,\alpha,\beta)
={}&\int_0^\infty
 \frac{F(X)F\!\left(\dfrac{MR}{KS}
              \dfrac{Xu+\lambda_0\alpha}{v}\right)}
 {\sqrt{X(Xu+\lambda_0\alpha)/v}}\,
 e\!\left(-\frac{\omega_0\beta X}{v}\right)\\
 &\times\int_{\mathbb R}W(\tau)
 V_{T\tau}\!\left(
 T\chi_0\frac{X(Xu+\lambda_0\alpha)}v\right)
 \exp\!\left(iT\tau\log\left(
 1+\frac{\lambda_0\alpha}{Xu}\right)\right)d\tau\,dX .
\end{aligned}
\tag{5.13b}
\]

Thus the exact logarithm and its coupling to \(X,u,\alpha,\tau\) remain
inside \(\Psi^\circ\).  The bounds already proved give

\[
 T\lambda_0\ll T^\eta,\qquad
 \omega_0\ll T^\eta,\qquad
 \chi_0\ll T^\eta,\qquad
 \frac1{16}\leq\frac{KS}{MR}\leq16.
\tag{5.13c}
\]

Together with (2.5), these show that differentiating (5.13b) introduces no
power beyond \(T^{O(\eta)}\).  After the initial \(\eta_0\)-budget is
renamed as \(\eta\), for each multi-index \(\mathbf j\),

\[
 \|\partial^{\mathbf j}\Psi\|_\infty
 \leq C_{\mathbf j,W,D}\mathscr L^{B|\mathbf j|}.
\tag{5.14}
\]

Indeed, the Jacobian \(dx\,dt=MT\,dX\,d\tau\) and the square-root
denominator in (4.4) contribute \(T\sqrt{S/R}\).  Moreover

\[
 \frac{\sqrt{S/R}}{\sqrt{rs}\,s}
 =\frac1{RS}\,u^{-1/2}v^{-3/2}.
\tag{5.14a}
\]

The last two fixed smooth factors, together with \(F_R,F_S\), are absorbed
into \(\Psi\).  Consequently one box has the exact scale

\[
 \mathcal O^{\ne0}_{q;R,S,K,M,L,H}
 =\frac{2T}{qRS}\,\mathfrak S_{q;R,S,K,M,L,H}[\Psi].
\tag{5.15}
\]

## 6. The local coupled-kernel gate for an asymptotic

### 6.1 Gate comparison

For comparison with BCR, smooth Mellin/Fourier separation of the admissible
kernel in (5.14) produces the following three-variable sums. For

\[
\begin{aligned}
 \mathfrak S_q[\Psi]
={}&\sum_{\substack{R/2\leq r\leq2R,\ S/2\leq s\leq2S\\
                    qr,qs\leq N,\ (r,s)=(q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\\
 &\quad\times
 \sum_{\substack{L\leq|\delta|\leq2L\\
                  H\leq|h|\leq2H}}
 \Psi\left(\frac rR,\frac sS,\frac\delta L,\frac hH\right)
 e\left(-\frac{h\delta\bar r}{s}\right).
\end{aligned}
\tag{6.0}
\]

No absolute value has been taken between the \(r,s,\delta,h\) sums.
Factoring fixed outer cutoffs from \(\Psi\), smooth Mellin/Fourier inversion
produces the following separated family.  The correct additive Fourier
window is two-sided.  For a sufficiently large fixed \(C_0\), put

\[
 \mathcal X_\eta=
 \left\{(x,y)\in\mathbb R^2:
 |x|\leq C_0\left(\frac MS+\frac{T^\eta}{H}\right),\
 |y|\leq C_0\left(\frac T{MR}+\frac{T^\eta}{L}\right)\right\}.
\tag{6.1}
\]

Indeed, the \(\beta\)-phase in (5.13b) has Fourier centre
\[
 x=\frac{MX}{Sv}\asymp\frac MS
\]
and the fixed \(\beta\)-cutoff has Fourier width
\(T^{O(\eta_0)}/H\).  The derivative of the exact \(\alpha\)-phase is
\[
 \partial_\alpha\left[
 T\tau\log\left(1+\frac{\lambda_0\alpha}{Xu}\right)\right]
 =\frac{T\tau\lambda_0}{Xu+\lambda_0\alpha},
\]
so its \(y\)-centre is \(\asymp T/(MR)\), while the fixed
\(\alpha\)-cutoff has width \(T^{O(\eta_0)}/L\).  The enlargement from
\(\eta_0\) to \(\eta\) gives (6.1).  In particular, when either centre is
smaller than the reciprocal cutoff length, (6.1) retains zero and both
signs; no lower bound on \(HM/S\) or \(TL/(MR)\) is being assumed.
For example, the admissible box
\(R=S=T^3,\ M=K=T^{1/2},\ L=H=1\) has both centres \(T^{-5/2}\),
whereas (6.1) includes \(|x|,|y|\leq C_0(T^{-5/2}+T^\eta)\);
the low and negative frequencies are therefore present.

For every \((x,y)\in\mathbb R^2\), put

\[
 \nu_{x,y}(a)=
 \sum_{\substack{h\delta=a\\H\leq|h|\leq2H\\L\leq|\delta|\leq2L}}
 U(h/H)V(\delta/L)e\left(-hx+\frac{\delta y}{2\pi}\right),
\tag{6.2}
\]

where \(U,V\in C_c^\infty([-2,-1]\cup[1,2])\), with every fixed derivative
bounded by a constant.  For
\(\theta=(\theta_1,\theta_2)\in\mathbb R^2\), define

\[
\begin{aligned}
 \mathfrak T_q(\theta;R,S;L,H;x,y)
 ={}&\sum_{a\ne0}\nu_{x,y}(a)
 \sum_{\substack{R/2\leq r\leq2R\\S/2\leq s\leq2S\\
                  qr,qs\leq N\\(r,s)=(q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\\
 &\qquad\times U_1(r/R)V_1(s/S)
 \left(\frac rR\right)^{i\theta_1}
 \left(\frac sS\right)^{i\theta_2}
 e\left(-\frac{a\bar r}{s}\right),
\end{aligned}
\tag{6.3}
\]

with \(U_1,V_1\in C_c^\infty([1/2,2])\).  The Mellin twists may equivalently
be included in the two displayed weights.  The coefficient in (6.2) is
not arbitrary. It is a divisor-convolution coefficient and satisfies

\[
 \operatorname{supp}\nu\subset
 \{a:LH\leq|a|\leq4LH\},\qquad
 |\nu(a)|\ll_{U,V}\tau(|a|),\qquad
 \|\nu\|_2\ll_\varepsilon(LH)^{1/2+\varepsilon}.
\tag{6.4}
\]

Let a fixed separation scheme write the coupled weight as

\[
 \Psi(\mathbf u)=\int_{\Omega}\widehat\Psi(\xi)
 \prod_{j=1}^4\psi_{j,\xi}(u_j)\,d\xi,
 \qquad
 \|\widehat\Psi\|_{L^1(\Omega)}\ll_W\mathscr L^{C_{\rm sep}}.
\tag{6.5}
\]

Fourier/Mellin inversion and the triangle inequality give the exact chain

\[
 |\mathfrak S_q[\Psi]|
 \leq\int_\Omega|\widehat\Psi(\xi)|
       |\mathfrak T_q(\xi)|\,d\xi
 \leq\|\widehat\Psi\|_1\sup_{\xi\in\Omega}|\mathfrak T_q(\xi)|.
\tag{6.6}
\]

Consequently the three candidate gates, from strongest to weakest, are:

1. **Uniform-separated:**
   \(\sup_\xi|\mathfrak T_q(\xi)|
   \ll RS T^{-1/1000}\mathscr L^{-C_{\rm sep}}\).
2. **Integrated-separated:**
   \(\int|\widehat\Psi(\xi)||\mathfrak T_q(\xi)|d\xi
   \ll RS T^{-1/1000}\).
3. **Coupled-kernel:**
   \(|\mathfrak S_q[\Psi]|\ll RS T^{-1/1000}\).

Only the last expression occurs in the exact box formula (5.15).  Neither
Minkowski nor an early absolute value is needed after it.  Thus the formal
interface for the next analytic slice is the weakest of the three:

> **Accepted local gate after exact audit: coupled-kernel.** Uniformly for
> squarefree \(q\), all boxes satisfying (5.3), (5.6), (5.7), (5.10), and
> the actual coupled weights satisfying (5.14), prove
> \[
> \boxed{
>  |\mathfrak S_{q;R,S,K,M,L,H}[\Psi]|
>  \leq C_W RS\,T^{-1/1000}. }
> \tag{CK\(_{1/1000}\)}
> \]

At the end of this reduction phase the gate was unproved; the companion
route note reduces it to PEVP in Sections 4.109y--4.109zf but does not
prove the required uniform polylogarithmic spectral large sieve.  The
exponent \(1/1000\) is fixed merely to make the global target unambiguous;
any fixed positive power saving, or a fully
accounted logarithmic saving exceeding \(C_{\rm sep}+7\), would suffice.
The former \(RS T^\varepsilon\) gate proves only a
\(T^{1+\varepsilon}\) bound and is not sufficient for the asymptotic.
The second required local statement is the polylogarithmic-tail estimate

\[
 \boxed{\mathrm{TAIL}_{B,D}:\qquad
 |\mathcal R_{\rm tail}^{(B)}|\ll_W T\mathscr L^{-D}.}
\tag{6.6a}
\]

At the end of this reduction phase it too was unproved; (5.8d) explains
why it cannot be replaced by an absolute-value argument.  Section
4.109zg of the companion route note proves only its implication from a
seminorm-stable PEVP estimate, shell by shell.

### 6.2 Boundary diagnostics and global implication

The exact-rational checker prints the following non-proof diagnostics:

| witness | \((\rho,\sigma,m,k,\ell,h,\kappa)\) | \(a\) | \(a-(\rho+\sigma)/2\) |
|---|---|---:|---:|
| balanced_max_a | \((3,3,1/2,1/2,5/2,5/2,0)\) | 5 | 2 |
| large_q_endpoint | \((1,1,0,0,0,1,2)\) | 1 | 0 |
| r_long | \((3,2,0,1,2,2,0)\) | 4 | \(3/2\) |
| s_long | \((2,3,1,0,2,2,0)\) | 4 | \(3/2\) |

The \(T^2\) balanced gap is a failure of the arbitrary-coefficient BCR
third-variable range; it is not a counterexample to the coupled structured
gate.

Assuming CK\(_{1/1000}\), (5.15) gives each retained box the bound

\[
 |\mathcal O^{\ne0}_{q;R,S,K,M,L,H}|
 \ll_W\frac{T^{1-1/1000}}q.
\tag{6.7}
\]

There are \(O_W(\mathscr L^6)\) retained dyadic choices, and

\[
 \sum_{q\leq N}\frac{\mu^2(q)}q\ll\mathscr L.
\tag{6.8}
\]

Together with (4.5j), CK\(_{1/1000}\) and
TAIL\(_{B,D}\) give the precise implication

\[
 \boxed{\mathrm{CK}_{1/1000}+\mathrm{TAIL}_{B,D}
 \quad\Longrightarrow\quad
 \mathcal R_{T^3,T}
 \ll_W T^{1-1/1000}\mathscr L^7+T\mathscr L^{-D}=o_W(T).}
\tag{6.9}
\]

No separated supremum is used in this implication.

## 7. Term-by-term correspondence with Bettin--Chandee--Radziwiłł

The notation correspondence is:

| This note | BCR | Meaning |
|---|---|---|
| \(W(t/T)\) | \(\phi(t/T)\) | original height cutoff |
| \(V_t(m_1m_2)\) | \(W(2\pi m_1m_2/t)\) | exact-gamma AFE weight versus its leading Stirling term |
| \(d,e\) | \(n_1,n_2\) | Dirichlet-polynomial variables |
| \(q=(d,e)\) | \(d=(n_1,n_2)\) | extracted common divisor |
| \(r=d/q,s=e/q\) | reduced \(n_1,n_2\) | coprime variables |
| \(m_2\in[M/2,2M]\) | \(m_2\sim M\) | Poisson variable |
| \(q\delta=m_1e-m_2d\) | \(d\Delta=m_1n_2-m_2n_1\) after gcd extraction | shifted-divisor variable |
| \(L\leq|\delta|\leq2L\) | \(0<|\Delta|\leq D/d\) | short shift |
| \(H\leq|h|\leq2H\) | \(0<|h|<H_d\) | nonzero Poisson frequency |
| \(H\leq8S\mathscr L^B/M\) | \(H_d=N_2/(dM)T^\varepsilon\) | Fourier cutoff |
| \(a=h\delta\) | \(a=h\Delta\) | third trilinear variable |
| \(A=LH\leq64RS\mathscr L^{2B}/T\) | \(A=N_1N_2/(d^2T^{1-\varepsilon})\) | length of the \(a\)-variable |
| \(e(-a\bar r/s)\) | \(e(-a\bar n_1/n_2)\) | Kloosterman-fraction phase |
| \(\nu_{x,y}(a)\) in (6.2) | \(\nu_{x,y}(a)=\sum_{h\Delta=a}e(-hx+\Delta y/2\pi)\) | divisor-convolution coefficient |
| CK\(_{1/1000}\) | BCR Proposition 1 / Conjecture 1 slot | arithmetic input, before separation here |

The four methodological differences forced by \(N=T^3\) are exact:

1. **AFE error.** BCR use
   \(|\zeta|^2=2\sum W(2\pi m_1m_2/t)+O(T^{-2/3})\). Their polynomial has
   length below \(T\), so the integrated error is \(O(T^{1/3+\varepsilon})\).
   At length \(T^3\), that multiplication is not valid at the target scale.
   Formula (2.4) removes this issue.

2. **Taylor error.** BCR replace
   \(\log(1+\Delta/(m_2n_1))\) by its first terms and obtain, before using
   coefficient structure, an error containing
   \(N^2T^{-3/2+\varepsilon}\). At \(N=T^3\) this is
   \(T^{9/2+\varepsilon}\). Formula (4.4) retains the exact logarithm and
   exact square-root denominator.

3. **Range of the third variable.** BCR Conjecture 1 assumes
   \(A\leq(RS)^{1/2+\varepsilon}\). Here
   \(A\leq64RS\mathscr L^{2B}/T\). For \(R=S=T^3\), the latter permits
   \(A=64T^5\mathscr L^{2B}\), while the BCR hypothesis permits only
   \(A\leq T^{3+\varepsilon}\). Thus even BCR's conjectural arbitrary-
   coefficient estimate does not cover the present long-\(a\) boxes.

4. **Arithmetic structure.** BCR discard the nature of \(a_n\) and use only
   \(L^2\) norms. Equation (5.2) keeps both signs \(\mu(r)\mu(s)\), and
   (6.2) keeps the factorization \(a=h\delta\). CK\(_{1/1000}\) is posed
   only for the original coupled structured class, not for arbitrary
   coefficients.

For balanced \(R=S=X\), the BCR proven local calculation gives, after the
archimedean normalization in (5.15),

\[
 T^{3/20+\varepsilon}X^{33/20}+T^\varepsilon X^{15/8}.
\tag{7.1}
\]

Requiring the first term in (7.1) to be \(o(T)\) gives

\[
 X<T^{17/33-\varepsilon}.
\tag{7.2}
\]

At \(X=T^3\), the two terms in (7.1) are

\[
 T^{51/10+\varepsilon},\qquad T^{45/8+\varepsilon}.
\tag{7.3}
\]

CK\(_{1/1000}\) would instead give \(T^{1-1/1000}\) for the corresponding
box before logarithmic aggregation.  The missing savings relative to (7.3)
cannot come from a rearrangement of the BCR norm inequalities; it has to use
the simultaneous Möbius weights, the divisor-convolution restriction on
\(a\), and the coupled archimedean kernel.

The \(T^{3/4}\) result in BCR concerns a product of a smooth polynomial of
length \(T^{1/2}\) and a second polynomial of length \(T^{1/4}\), where Watt's
Kloosterman-sum estimate applies. The single polynomial
\(\mu(n)p_N(n)\mathbf1_{n\leq T^3}\) does not have that factorization, so
that theorem supplies no box estimate for (6.3).

## 8. What has and has not been proved

**Phase-1 classification: exact reduction verified.**  The later
analytic gate remains open.  The companion route note isolates the
PEVP and conditional tail implications but does not prove the required
uniform polylogarithmic spectral large sieve.

Proved in this note:

* the pole-cancelled exact AFE and its convergence bounds, (2.0)--(2.7);
* the finite diagonal and exact shifted-divisor reindexing, (2.8)--(3.8);
* the Poisson coefficient, phase, and complete nonzero-mode kernel,
  (4.1)--(4.5);
* the corrected zero-mode identity, including the previously omitted
  \(1-4z^2\) zero and the exact archimedean correction,
  (4.5a)--(4.8);
* the exact separation (5.2a) into a polylogarithmic core and a named tail,
  and the core-box normalization (5.3)--(5.15);
* the implication
  \(\mathrm{CK}_{1/1000}+\mathrm{TAIL}_{B,D}
  \Rightarrow\mathcal R_{T^3,T}=o_W(T)\),
  (6.7)--(6.9).

| Claim | Status | Complete derivation or exact status location |
|---|---|---|
| Completed AFE and diagonal extraction | verified | (2.0)--(2.10), including pole cancellation, absolute convergence, uniform weight bounds, and the diagonal parametrization |
| Shifted-divisor expansion | verified | (3.1)--(3.8), including the absolute dyadic reindexing and full smooth kernel |
| Poisson zero/nonzero-mode decomposition | verified after correction | (4.1)--(4.8); the omitted sine quotient is restored in (4.5i)--(4.6c), and the complete correction bound is (4.7c.0)--(4.7c) |
| Effective ranges and coupled-kernel normalization | verified | (5.1)--(5.15), including both nonstationary cutoffs and the exact kernel scale |
| Comparison of the three candidate gates | verified logical reduction | (6.0)--(6.8); only \({\rm(US)}\Rightarrow{\rm(IS)}\Rightarrow{\rm(CK)}\) is proved |
| Coupled-kernel estimate \(\operatorname{MWKF}_{\rm ck}(3)\) | **open** | the corrected local oldclass calculation leaves a weighted primitive-conductor PEVP/large-sieve gate; companion Sections 4.109y--4.109zf |
| Global remainder bound | **conditional** | compact and tail aggregation close once seminorm-stable PEVP is supplied |

The companion audit does not treat CK\(_{1/1000}\) or
TAIL\(_{B,D}\) as consequences of BCR.  It isolates the required signed
exact-level PEVP estimate after primitive-conductor regrouping.  A custom
polylogarithmic full-level harmonic large sieve would close it, but that
estimate is not yet proved.  Consequently the exact decomposition and
LCM main term currently give only the conditional implication

\[
 I_{\lfloor T^3\rfloor,W}(T)
 =\frac43T\int_1^2W(u)\,du+o_W(T).
\]

## 9. Primary references

* S. Bettin, V. Chandee, M. Radziwiłł, *The mean square of the product of
  the Riemann zeta function with Dirichlet polynomials*, arXiv:1411.7764,
  especially Proposition 1 and Sections 3.1--3.4.
* S. Bettin, V. Chandee, *Trilinear forms with Kloosterman fractions*,
  arXiv:1502.00769, Theorem 1, as a Region-A input for the next coverage
  slice; no claim of full-polytope coverage is made here.
* T. Wright, *A note on trilinear forms with partially fixed denominator*,
  arXiv:2604.25177v2, as a future fixed-factor Region-C input; its hypotheses
  have not yet been mapped over the whole polytope.
* arXiv:2601.00292 is **withdrawn from this project's admissible analytic
  inputs**: the author record reports a missing \(L^2\) factor (changing the
  relevant loss from \(L^5\) to \(L^7\)), so the advertised improvement is
  not used.
* M. Radziwiłł, *Limitations to mollifying \(\zeta(s)\)*,
  arXiv:1207.6583, for Farmer's all-\(\theta\) long-mollifier conjecture and
  the nontrivial role of the off-diagonal.
* K. Pratt, N. Robles, *Perturbed moments and a longer mollifier for
  critical zeros of \(\zeta\)*, arXiv:1706.04593, for later exploitation of
  Möbius/convolution structure up to lengths below \(T^{4/7}\) or
  \(T^{6/11}\), still far from \(T^3\).
