# Möbius-weighted long mollifier: exact off-diagonal reduction

> **Current proof status.**
>
> | component | status in this note |
> |---|---|
> | LCM main quadratic form | proved separately; its normalization is rechecked below |
> | Exact AFE and shifted-divisor identity | proved after audit in Sections 2--3 |
> | Poisson zero/nonzero-mode identity | proved after the corrections in Section 4 |
> | Power-enlarged tail for the \(O(T^{1+\varepsilon})\) target | proved in Section 6.3 |
> | Direct published Region A--C coverage | proved/classified in Section 8 |
> | Standalone cofactor primitive product spectrum, all gcd strata and smooth archimedean weights | proved in Sections 9.85--9.88 |
> | Residual coupled Region-D estimate at length \(T^3\) | unproved |
>
> Thus this note is not a proof of the \(T^3\) long-mollifier upper bound
> or asymptotic.
> A row is promoted from “under audit” only after the displayed convergence,
> contour-shift, and reindexing arguments have all been supplied.

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

Thus the exact correction is negligible for the later conditional estimate,
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

This gate is unproved.  The exponent \(1/1000\) is fixed merely to make the
global target unambiguous; any fixed positive power saving, or a fully
accounted logarithmic saving exceeding \(C_{\rm sep}+7\), would suffice.
The former \(RS T^\varepsilon\) gate proves only a
\(T^{1+\varepsilon}\) bound and is not sufficient for the asymptotic.
The second required local statement is the polylogarithmic-tail estimate

\[
 \boxed{\mathrm{TAIL}_{B,D}:\qquad
 |\mathcal R_{\rm tail}^{(B)}|\ll_W T\mathscr L^{-D}.}
\tag{6.6a}
\]

It too is unproved; (5.8d) explains why it cannot be replaced by an
absolute-value argument.

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
TAIL\(_{B,D}\) prove the precise conditional implication

\[
 \boxed{\mathrm{CK}_{1/1000}+\mathrm{TAIL}_{B,D}
 \quad\Longrightarrow\quad
 \mathcal R_{T^3,T}
 \ll_W T^{1-1/1000}\mathscr L^7+T\mathscr L^{-D}=o_W(T).}
\tag{6.9}
\]

No separated supremum is used in this implication.

### 6.3 The genuinely weakest gate for the upper-bound target

The original target of this project is the upper bound

\[
 I_{T^3,W}(T)\ll_{\varepsilon,W}T^{1+\varepsilon},
\tag{6.10}
\]

not an asymptotic with an \(o(T)\) remainder.  The fixed saving in
CK\(_{1/1000}\) is therefore stronger than the weakest sufficient input.
For (6.10), fix a target \(\varepsilon_0>0\), put
\(\eta=\varepsilon_0/100\), and replace every factor
\(\mathscr L^B\) in (5.6) and (5.8) by \(T^\eta\).  Call the result the
**power-enlarged upper-bound core**.  Its zero-slack inequalities are still
(5.12b); before suppressing slack they read

\[
 k+m\leq1+\eta,\qquad
 \ell\leq m+\rho-1+\eta,\qquad
 h\leq\sigma-m+\eta,qquad
 a\leq\rho+\sigma-1+2\eta.
\tag{6.11}
\]

This enlargement removes the separate tail conjecture for the upper-bound
problem.  Indeed, outside the enlarged \(\delta\)-range, (5.8b) gives

\[
 \bigl(T|\log(1+\delta/(xr))|\bigr)^{-J}\ll_J T^{-J\eta};
\]

outside the enlarged \(h\)-range, (5.8c) gives

\[
 \left(\frac{s}{|h|M}\right)^J\ll_JT^{-J\eta}.
\]

The Mellin decay used for (5.6) gives the same factor outside
\(KM\leq T^{1+\eta}\).  The absolute majorant (5.8d), including the
\(t\)-integration, is \(O_W(T^{9/2+\varepsilon_0/4})\).  Since all
amplitudes are smooth to arbitrary fixed order, choose the fixed integer
\(J\) so that

\[
 J\eta>\frac72+\frac{\varepsilon_0}{2}.
\]

A union bound over the three complements then proves

\[
 \mathcal R_{\rm tail}^{(\eta)}
 \ll_{\varepsilon_0,W}T^{1-\varepsilon_0/4}.
\tag{6.12}
\]

This does not prove the polylogarithmic tail statement
TAIL\(_{B,D}\), and hence does not prove an asymptotic.  It does prove all
tail control required by (6.10).

The accepted weakest local interface for the upper-bound problem is now

> **Upper-bound coupled-kernel gate \(\mathrm{CK}_{\rm ub}(3)\).** For
> every \(\varepsilon>0\), uniformly in the power-enlarged boxes (6.11)
> and the actual coupled weights, prove
> \[
>  |\mathfrak S_{q;R,S,K,M,L,H}[\Psi]|
>  \ll_{\varepsilon,W}RS T^\varepsilon.
> \tag{CK\(_{\rm ub}(3)\)}
> \]

By (5.15), each core box is then
\(O_{\varepsilon,W}(T^{1+\varepsilon}/q)\).  There are
\(O(\mathscr L^6)\) dyadic choices and (6.8) supplies one more logarithm.
After allocating \(\varepsilon_0/4\) to the local estimate and absorbing
all seven logarithms, (6.12) gives the exact implication

\[
 \boxed{
 \mathrm{CK}_{\rm ub}(3)
 \quad\Longrightarrow\quad
 \mathcal R_{T^3,T}\ll_{\varepsilon_0,W}T^{1+\varepsilon_0}.}
\tag{6.13}
\]

Thus CK\(_{\rm ub}(3)\), not CK\(_{1/1000}\) plus
TAIL\(_{B,D}\), is the weakest sufficient gate presently isolated for the
user's stated upper-bound target.  It remains unproved.

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

## 8. Exact published-estimate coverage for the upper-bound gate

This section audits Regions A--C against CK\(_{\rm ub}(3)\). It uses the
separated family only as a sufficient route to the coupled estimate: the
Fourier--Mellin \(L^1\) loss in (6.5) is polylogarithmic and is absorbed by
the \(T^\varepsilon\) allowance. Failure of a separated theorem is not a
counterexample to the coupled gate.

### 8.1 Region A: Bettin--Chandee

Bettin--Chandee, Theorem 1, applies to

\[
 \mathcal B(X,Y,A)=
 \sum_{a\asymp A}\sum_{r\asymp X}\sum_{s\asymp Y\atop(r,s)=1}
 \alpha_r\beta_s\nu_a e\left(-\frac{a\bar r}{s}\right)
\]

with arbitrary complex coefficients and gives

\[
 \begin{aligned}
 |\mathcal B(X,Y,A)|\ll_\varepsilon{}
 &\|\alpha\|_2\|\beta\|_2\|\nu\|_2
 \left(1+\frac{A}{XY}\right)^{1/2}\\
 &\times\left((AXY)^{7/20+\varepsilon}(X+Y)^{1/4}
 +(AXY)^{3/8+\varepsilon}(AX+AY)^{1/8}\right).
 \end{aligned}
\tag{8.1}
\]

The exact hypothesis ledger in the present application is:

| BC datum | present datum | verification |
|---|---|---|
| \(X,Y,A\geq1\), dyadic support | \(R,S,LH\) | (5.4), (5.9) |
| \((r,s)=1\) | same | (5.1) |
| nonzero phase parameter | \(\vartheta=-1\) | (5.12) |
| arbitrary coefficient sequences | the two Möbius weights and \(\nu_{x,y}\) | arbitrary coefficients are allowed |
| finite \(L^2\) norms | \(\|\alpha\|_2\ll R^{1/2}\), \(\|\beta\|_2\ll S^{1/2}\), \(\|\nu\|_2\ll_\varepsilon A^{1/2+\varepsilon}\) | (6.4) and \(|p_N|\leq1\) |
| archimedean prefactor | \(1+A/(RS)\ll1+T^{-1+2\eta}\) | (6.11), for fixed \(\eta<1/4\) |

Put \(u=\max(\rho,\sigma)\), \(v=\min(\rho,\sigma)\), and
\(a=\ell+h\). After inserting the three exact norm bounds, the two terms
in (8.1) have exponents

\[
 E_1=\frac{17}{20}(a+\rho+\sigma)+\frac14u,
 \qquad
 E_2=\frac78(\rho+\sigma)+a+\frac18u.
\tag{8.2}
\]

Consequently Region A covers a box for CK\(_{\rm ub}(3)\) if and only if
both savings

\[
 \boxed{
 \Delta_1=\frac3{20}(\rho+\sigma)-\frac{17}{20}a-\frac14u\geq0,
 \qquad
 \Delta_2=\frac18v-a\geq0 }
\tag{8.3}
\]

hold, up to the allocated \(O(\eta+\varepsilon)\) slack. These are the
two exact rational inequalities implemented by the coverage checker.

### 8.2 Region B: completing one factor of \(a=h\delta\)

Fix \(r,s,\delta\). The derivative bounds (5.14), partial summation, and
the standard smooth geometric-sum estimate give, for \(J>2\),

\[
 \sum_{h\asymp H}F_{r,s,\delta}(h/H)
 e\left(-\frac{h\delta\bar r}{s}\right)
 \ll_{J,\varepsilon}HT^\varepsilon
 \left(1+H\left\|\frac{\delta\bar r}{s}\right\|\right)^{-J}.
\tag{8.4}
\]

Multiplication by \(\bar r\) permutes the residue classes modulo \(s\).
On a complete residue block,

\[
 \sum_{b\bmod s}H(1+H\|b/s\|)^{-J}\ll_J H+s.
\]

Splitting the \(\delta\)-interval into at most \(1+L/s\) such blocks
retains both the incomplete boundary and the zero residue \(s\mid\delta\):

\[
 \sum_{\delta\asymp L}\left|
 \sum_{h\asymp H}F_{r,s,\delta}(h/H)
 e\left(-\frac{h\delta\bar r}{s}\right)\right|
 \ll_{J,\varepsilon}T^\varepsilon(1+L/s)(H+s).
\tag{8.5}
\]

The symmetric completion in \(\delta\) gives
\(T^\varepsilon(1+H/s)(L+s)\). The admissible polytope implies

\[
 h\leq\sigma,\qquad
 \ell\leq m+\rho-1=k+\sigma-1\leq\sigma.
\tag{8.6}
\]

Thus, after removing the outer \(RS\) scale, the trivial bound and the two
completion bounds have respective exponent losses

\[
 a,\qquad \sigma,\qquad \sigma.
\tag{8.7}
\]

Completion with both \(r,s\) fixed therefore reaches
CK\(_{\rm ub}(3)\) only on the exponent-zero face \(a=0\).  Formula (8.5),
rather than a claimed square-root cancellation, is the boundary-safe
fixed-modulus result.  The following additional modulus average sharpens
Region B.

There is, however, a sharper joint use of completion and the outer reduced
modulus variable.  Fix \(s,\delta\), put \(g=(\delta,s)\), and sum the
pointwise geometric bound over \(r\).  Inversion permutes the reduced
residue classes, while multiplication by \(\delta\) has multiplicity at
most \(g\) and leaves a grid of spacing \(g/s\).  Therefore

\[
 \sum_{r\asymp R\atop(r,s)=1}
 \left|\sum_{h\asymp H}F_{r,s,\delta}(h/H)
 e\left(-\frac{h\delta\bar r}{s}\right)\right|
 \ll_{J,\varepsilon}T^\varepsilon(1+R/s)(gH+s).
\tag{8.5a}
\]

This includes the resonant case \(s\mid\delta\), where the term \(gH\)
is necessary.  For a dyadic interval \(L\leq|\delta|\leq2L\), the exact
divisor identity \((n,s)=\sum_{d\mid(n,s)}\varphi(d)\) gives

\[
 \sum_{\delta\asymp L}(\delta,s)
 \ll L\tau(s).
\tag{8.5b}
\]

Indeed, only divisors \(d\leq2L\) occur; the count of their multiples in
the interval is at most \(L/d+1\), and
\(\sum_{d\mid s,d\leq2L}\varphi(d)\leq2L\tau(s)\).  Since \(H\leq
sT^\varepsilon\) by (8.6), summing (8.5a) over \(\delta\) and then
\(s\asymp S\) gives \(O(RSLT^\varepsilon)\) when \(R\geq S\).  When
\(S>R\), reciprocity swaps \(r,s\); its extra factor
\(e(-h\delta/(rs))\) merely translates the geometric frequency.  Hence
the same bound holds in every orientation.  Interchanging \(h,\delta\)
in this argument is legitimate by the joint seminorm bounds (5.14), and
gives the second estimate

\[
 \boxed{
 |\mathfrak S_q[\Psi]|\ll_\varepsilon
 RS\min(L,H)T^\varepsilon.}
\tag{8.5c}
\]

Thus the joint-completion loss is
\(\min(\ell,h)\), not merely the three fixed-\((r,s)\) losses in (8.7).
Region B consequently covers every admissible box with \(\ell=0\) or
\(h=0\), including boxes with positive \(a=\ell+h\).  It still misses
the interior \(\ell,h>0\); the balanced maximal box loses \(T^{5/2}\).
The finite checker separately enumerates the unit-group fibre
multiplicities in (8.5a) and the two-sign dyadic gcd sum in (8.5b).

### 8.3 Region C: Wright's partially fixed denominator

Wright, Theorem 2.1, concerns

\[
 \mathcal B(X,Y,A;R_0)=
 \sum_{a,r,n\atop(r,nR_0)=1}\alpha_r\beta_n\nu_a
 e\left(\vartheta\frac{a\bar r}{nR_0}\right),
\tag{8.8}
\]

under \(X\ll Y^2\) and \(R_0\ll X^C\) for a fixed large \(C\). Its stated
bound is

\[
 \begin{aligned}
 \mathcal B(X,Y,A;R_0)\ll{}&X^\varepsilon
 \|\alpha\|_2\|\beta\|_2\|\nu\|_2(AXY)^{1/2}R_0^{1/4}
 \left(1+\frac{|\vartheta|A}{XY}\right)^{1/4}\\
 &\times\left(
 Y^{-1/8}+R_0^{1/8}Y^{1/8}X^{-1/4}
 +\frac{X^{1/10}}{R_0^{3/20}A^{1/20}Y^{3/20}}
 +\frac{Y^{3/20}}{A^{3/20}X^{1/5}}
 +\frac{Y^{3/8}}{X^{1/2}}
 \right).
 \end{aligned}
\tag{8.9}
\]

There are two independent reasons that (8.9) supplies no direct new box in
the current sum.

First, before factorizing \(s\), (6.0) has denominator \(s\), so the only
direct identification is \(R_0=1,n=s\). Wright explicitly states that
\(R_0=1\) recovers Bettin--Chandee equation (7.2); it is not a new
fixed-factor saving. Taking \(R_0>1\) requires an exact factorization
\(s=R_0n\), a rule assigning every \(s\) to such a factor, and the retained
coefficient \(\mu(R_0n)\). That is a structured Type-I/II operation and is
assigned to Region D, not to direct Region C.

Second, the arXiv v2 source is internally inconsistent in the third term of
(8.9): the theorem statement has \(A^{-1/20}\), whereas the last displayed
line of its proof has \(A^{-3/10}\). No exponent depending on that term is
used here without a corrected statement. The coverage checker therefore
records Region C as giving no direct improvement, rather than silently
choosing one of the two exponents.

### 8.4 Coverage table and residual witnesses

The direct published-and-elementary coverage is exactly:

| primary route | exact covered set | result |
|---|---|---|
| A: Bettin--Chandee | admissible boxes satisfying both inequalities (8.3) | proved from (8.1) |
| B: joint completion | admissible boxes with \(\min(\ell,h)=0\) not already assigned to A | proved by (8.4)--(8.7), sharpened by (8.5a)--(8.5c) |
| C: Wright direct | no additional boxes | \(R_0=1\) gives BC; \(R_0>1\) requires Region D |
| D: structured residual | every other admissible box | **unproved** |

The deterministic boundary ledger is:

| witness | \((\rho,\sigma,\ell,h)\) | \((\Delta_1,\Delta_2)\) | joint-completion loss | route |
|---|---:|---:|---:|---|
| balanced maximal \(a\) | \((3,3,5/2,5/2)\) | \((-41/10,-37/8)\) | \(5/2\) | D |
| \(r\)-long | \((3,2,2,2)\) | \((-17/5,-15/4)\) | \(2\) | D |
| \(s\)-long | \((2,3,2,2)\) | \((-17/5,-15/4)\) | \(2\) | D |
| large-\(q\) endpoint | \((1,1,0,1)\) | \((-4/5,-7/8)\) | \(0\) | B |

Hence published arbitrary-coefficient estimates, sharpened joint
completion, and the direct fixed-factor theorem do not prove
CK\(_{\rm ub}(3)\) in the interior \(\ell,h>0\). The remaining work is
precisely an estimate that first factorizes one Möbius variable while
retaining the other Möbius weight, the product \(a=h\delta\), and the
coupled kernel.

## 9. Exact Möbius decomposition and the residual Type-II gate

This section performs the factorization demanded by Region D. It does not
claim the resulting Type-II estimate.

### 9.1 A finite convolution identity

For a real cutoff \(U\geq2\), define the finitely supported sequence

\[
 \mu_U(n)=\mu(n)\mathbf1_{n\leq U},\qquad
 c_U=\mathbf1*\mu_U-\delta_1,
\tag{9.1}
\]

where \(\mathbf1(n)=1\), \(\delta_1(1)=1\), and \(*\) is Dirichlet
convolution. Since \(\mu*\mathbf1=\delta_1\),

\[
 \mu*(\delta_1+c_U)
 =\mu*\mathbf1*\mu_U=\mu_U,
\]

and hence

\[
 \mu=\mu_U-\mu*c_U.
\tag{9.2}
\]

Iterating (9.2) \(J\) times gives the exact sequence identity

\[
 \boxed{
 \mu=\sum_{j=0}^{J-1}(-1)^j\mu_U*c_U^{*j}
      +(-1)^J\mu*c_U^{*J}.}
\tag{9.3}
\]

There is no analytic truncation in (9.3). For \(n\leq U\), every divisor
of \(n\) is at most \(U\), so

\[
 c_U(n)=\sum_{d\mid n}\mu(d)-\delta_1(n)=0.
\tag{9.4}
\]

It follows that \(c_U^{*J}(n)=0\) for \(n\leq U^J\). Therefore

\[
 \boxed{
 \mu(n)=\sum_{j=0}^{J-1}(-1)^j
 (\mu_U*c_U^{*j})(n)\qquad(n\leq U^J).}
\tag{9.5}
\]

The finite checker verifies (9.5) directly on integers and separately
checks the support gap (9.4). This is a regression check for the algebra,
not a proof of an exponential-sum estimate.

### 9.2 Substitution without discarding either arithmetic structure

Choose \(U^J\geq2S\) and substitute (9.5) only for the \(s\)-weight in
(6.0). For each \(j\), put

\[
 C_{j,U}(n)=c_U^{*j}(n).
\tag{9.6}
\]

Before any absolute value, the corresponding contribution is exactly a
finite linear combination of

\[
 \begin{aligned}
 \mathfrak D_{j,q}[\Psi]
 ={}&\sum_{u\leq U}\mu(u)
 \sum_{\substack{r,n,h,\delta\\
                  r\asymp R,\ un\asymp S\\
                  h\asymp H,\ \delta\asymp L\\
                  \mu(un)^2=1\\
                  (r,un)=(q,run)=1}}
 \mu(r)C_{j,U}(n)\,p_N(qr)p_N(qun)\\
 &\qquad\times
 \Psi\left(\frac rR,\frac{un}{S},\frac\delta L,\frac hH\right)
 e\left(-\frac{h\delta\bar r}{un}\right).
 \end{aligned}
\tag{9.7}
\]

Thus the other Möbius weight \(\mu(r)\), every short Möbius sign
\(\mu(u)\), the factorization \(a=h\delta\), the coprimality conditions,
and the coupled kernel all remain present.  The squarefree indicator is
legitimate term by term: insert \(\mu(s)^2\) before applying (9.5), which
does not change \(\mu(s)\), and then write \(s=un\).  In particular
\((u,n)=1\); this condition must not be inferred from the convolution
without the indicator.  Moreover,
\(|c_U(n)|\leq\tau(n)\), so for fixed \(J\),
\(|C_{j,U}(n)|\leq\tau_{O_J(1)}(n)\). This supplies the required
divisor-bounded \(L^2\) norm after \(u\) is fixed, but it does not justify
summing absolute values over \(u\).

### 9.3 The termwise fixed-factor route

To audit precisely what is lost by doing just that, dyadically take
\(u\asymp U_0=T^\tau\) in (9.7), fix \(u\), and apply Wright's theorem with

\[
 X=R,\qquad Y=S/U_0,\qquad A=LH,\qquad R_0=u.
\tag{9.8}
\]

The theorem requires

\[
 \rho\leq2(\sigma-\tau),\qquad \tau\leq\sigma,
\tag{9.9}
\]

besides the polynomial-size fixed-factor condition. The norm product is
\(T^{(\rho+\sigma-\tau+a)/2+\varepsilon}\). Multiplying by Wright's
\((AXY)^{1/2}R_0^{1/4}\), and then paying the full
\(T^\tau\) cost for the termwise \(u\)-sum, gives the common exponent
\(\rho+\sigma+a+\tau/4\) before the five parenthetical terms in (8.9).
Subtracting from the target \(\rho+\sigma\) gives the exact savings

\[
 \begin{aligned}
 d_1&=\frac{\sigma}{8}-a-\frac{3\tau}{8},\\
 d_2&=\frac{\rho}{4}-\frac{\sigma}{8}-a-\frac{\tau}{4},\\
 d_3&=\frac{3\sigma}{20}-\frac{\rho}{10}
      -\frac{19a}{20}-\frac{\tau}{4},\\
 d_4&=\frac{\rho}{5}-\frac{3\sigma}{20}
      -\frac{17a}{20}-\frac{\tau}{10},\\
 d_5&=\frac{\rho}{2}-\frac{3\sigma}{8}-a+\frac{\tau}{8}.
 \end{aligned}
\tag{9.10}
\]

All five must be nonnegative. In particular,

\[
 d_1=\frac{\sigma}{8}-a-\frac{3\tau}{8}
 \leq\frac{\sigma}{8}-a.
\tag{9.11}
\]

Thus the fixed factor does not relax the decisive arbitrary-\(a\)
condition; after termwise summation it makes that condition strictly worse.
For the balanced maximal box

\[
 (\rho,\sigma,a)=(3,3,5),\qquad 0\leq\tau\leq\frac32,
\]

condition (9.9) permits the displayed interval, but

\[
 d_1=-\frac{37}{8}-\frac{3\tau}{8}<0.
\tag{9.12}
\]

Even as \(\tau\to0\), the first Wright term is larger than the local
\(RS\) target by \(T^{37/8-o(1)}\). This obstruction is independent of
the discrepant third \(A\)-exponent noted after (8.9).

### 9.4 The residual averaged Type-II statement

The only legitimate next object is (9.7) with the \(u\)-sum still inside.
After dyadic localization it has the form

\[
 \boxed{
 \sum_{u\asymp U_0}\lambda_u
 \sum_{r,n,h,\delta}
 \mu(r)\beta_u(n)
 \Psi\left(\frac rR,\frac{un}{S},\frac\delta L,\frac hH\right)
 e\left(-\frac{h\delta\bar r}{un}\right),}
\tag{9.13}
\]

with the coprimalities from (9.7),
\(\lambda_u=\mu(u)\), and divisor-bounded \(\beta_u\). A proof of
CK\(_{\rm ub}(3)\) must bound the sum (9.13) before taking absolute values
over \(u\), and must also exploit that \(h,\delta\) remain separate.
Neither Bettin--Chandee Theorem 1 nor Wright Theorem 2.1 contains this
simultaneous fixed-factor average.

Accordingly, the exact residual gate is:

> **Averaged Möbius Type-II gate.** Prove that the sum (9.13), summed over
> the finitely many \(j<J\) in (9.5), is
> \(O_{\varepsilon,W}(RS T^\varepsilon)\) throughout the residual Region D.

This gate is no longer an arbitrary MWKF placeholder: its variables,
coefficients, factorization identity, coprimalities, and the failure of the
termwise published estimate are explicit. It remains unproved.

### 9.5 Audit of the August 2026 Pascadi bilinear theorem

Pascadi's Theorem 7.8, published online on 21 August 2026, gives power
savings for fixed-modulus bilinear forms of classical Kloosterman sums

\[
 \sum_{m\leq M}\sum_{n\leq N}\alpha_m\beta_n S(am,n;c).
\tag{9.14}
\]

This is not the Kloosterman fraction in (9.13). The exact bridge is finite
Fourier inversion in \(r\bmod s\). For a separated weight, define

\[
 \widehat\alpha_s(m)=\sum_{r\bmod s}\alpha_s(r)e(-mr/s),
 \qquad
 \beta_s(b)=\sum_{a\equiv b\;({\rm mod}\ s)}\nu(a).
\tag{9.15}
\]

Then, on the coprime component,

\[
 \sum_{r\bmod s}^{*}\alpha_s(r)
 \sum_a\nu(a)e(-a\bar r/s)
 =\frac1s\sum_{m,b\bmod s}
 \widehat\alpha_s(m)\beta_s(b)S(m,-b;s).
\tag{9.16}
\]

Components with \(g=(m,b,s)>1\) require a further exact gcd decomposition;
discarding that obligation would be invalid. To test the strongest possible
direct consequence of the new theorem, it is already enough to audit the
most favorable full-residue coprime component of (9.16).

At \(M=N=c\), the four factors in Pascadi Theorem 7.8(i) save respectively

\[
 \frac{13-53\delta}{64},\qquad
 \frac{1+\delta}{6},\qquad
 \frac{4+\delta}{12},\qquad
 \frac{13}{24}
\tag{9.17}
\]

powers of \(c\), where \(0\leq\delta\leq1/24\). The optimum of the minimum
is attained when the first two are equal:

\[
 \delta=\frac7{191},\qquad
 \min(9.17)=\frac{33}{191}.
\tag{9.18}
\]

In the balanced maximal box, Plancherel and residue aggregation give the
optimistic norm scales

\[
 \|\widehat\alpha_s\|_2\ll s,\qquad
 \|\beta_s\|_2^2
 \ll_\varepsilon(1+A/s)A\,T^\varepsilon
 \asymp A^2s^{-1}T^\varepsilon.
\tag{9.19}
\]

After the factor \(1/s\) in (9.16), the trivial fixed-\(s\) scale is
\(As\). Summing \(s\asymp S\) termwise gives \(AS^2\). Thus for
\(A=T^5\), \(S=T^3\), the best exponent certified by this direct
Pascadi route is

\[
 T^{11-99/191+o(1)}.
\tag{9.20}
\]

Relative to the required \(RS=T^6\), the residual gap is

\[
 \boxed{T^{856/191-o(1)}}.
\tag{9.21}
\]

The checker verifies (9.17)--(9.21) with exact rational arithmetic.
Pascadi's result improves the published fixed-modulus diagnostic, but it
does not average the fraction moduli together with the two Möbius weights
and does not close (9.13).

### 9.6 Audit of Milićević--Qin--Wu

Theorem 1.1 of Milićević--Qin--Wu concerns the normalized fixed-modulus
kernel

\[
 \mathrm{Kl}_2(cmn;q)=q^{-1/2}
 \sum_{x\bmod q}^{*}e\left(\frac{cmnx+\bar x}{q}\right).
\]

If the coefficient supports are contained in \([1,M]\) and \([1,N]\),
and

\[
 1\leq M\leq Nq^{1/4},\qquad
 M^{7/5}N<q^{3/2},\qquad MN\leq q^{5/4},
\tag{9.22}
\]

their stated estimate is

\[
\begin{aligned}
 \sum_{m\leq M}\sum_{n\leq N}\alpha_m\beta_n
 \mathrm{Kl}_2(cmn;q)
 \ll{}&q^\varepsilon\|\alpha\|_2\|\beta\|_2(MN)^{1/2}\\
 &\times\left(
 M^{-1/2}q^{1/6}
 +M^{-3/25}N^{-3/10}q^{1/5}
 +(MN)^{-3/16}q^{11/64}
 \right).
\end{aligned}
\tag{9.23}
\]

For \(M=q^x,N=q^y\), the three exact savings over the norm-scale
baseline are

\[
 d_1=\frac x2-\frac16,\qquad
 d_2=\frac{3x}{25}+\frac{3y}{10}-\frac15,\qquad
 d_3=\frac{3(x+y)}{16}-\frac{11}{64}.
\tag{9.24}
\]

The last condition in (9.22) forces \(d_3\leq1/16\).  The boundary point
\(x=y=5/8\) has

\[
 (d_1,d_2,d_3)=\left(\frac7{48},\frac1{16},\frac1{16}\right),
\tag{9.25}
\]

so \(1/16\) is the exact supremal saving on the theorem's admissible
initial rectangles; it is approached with an arbitrarily small inward
shift because the middle condition in (9.22) is strict.

This does not produce a partition of the full-residue sum (9.16).
On the coprime \(b\)-component,
\(S(m,-b;s)=s^{1/2}\mathrm{Kl}_2(-bm;s)\), but the Fourier variables
there range through representatives of size \(s\).  Thus the top box has
\(M=N=s\), which violates \(MN\leq s^{5/4}\).  Cutting
\([1,s]\) into additively translated intervals does not repair the
hypothesis: translating either variable changes the product kernel
\(\mathrm{Kl}_2(-bm;s)\), while (9.23) is an initial-support theorem, not
an arbitrary short-interval theorem.  Consequently this result gives no
direct bound for the full Fourier bridge and no new Region-D box.  The
checker verifies (9.24)--(9.25) using exact fractions.

### 9.7 Exact reverse-Poisson identity

It remains natural to ask whether summing the separated \(h\)-oscillation
first creates a shorter shifted relation.  For fixed \(r,s,\delta\), let
\(F_{r,s,\delta}(x)\) denote the complete smooth integrand in (4.4), before
the factor \(e(-hx/s)\), extended by zero to the real line.  With the
Fourier convention (4.3b), Poisson summation gives the exact identity

\[
\begin{aligned}
 &\sum_{h\ne0}e\left(-\frac{h\delta\bar r}{s}\right)
 \widehat F_{r,s,\delta}(h/s)\\
 &\quad=s\sum_{m\equiv-\delta\bar r\;({\rm mod}\ s)}
 F_{r,s,\delta}(m)-\widehat F_{r,s,\delta}(0).
\end{aligned}
\tag{9.26}
\]

The congruence on the right is exactly (4.3a); putting
\(m_1=(mr+\delta)/s\) recovers \(m_1s-mr=\delta\).  Thus reverse Poisson
does not create an additional short variable or an independent congruence:
it returns the original shifted-divisor sum and subtracts the already
isolated zero mode.  Formula (9.26) is useful as a normalization check, but
it supplies no cancellation toward (9.13).  Any successful next step must
therefore estimate the averaged Möbius Type-II sum before either the
\(u\)-average or the coupled \((h,\delta)\)-kernel is discarded.

### 9.8 Direct Möbius--inverse-phase estimates

There are published estimates tailored to one of the two Möbius weights.
Korolev writes

\[
 S_q(x;f)=\sum_{n\leq x\atop(n,q)=1}
 f(n)e_q(an^*+bn).
\tag{9.27}
\]

For every sufficiently large integer \(q\), in particular for composite
\(q\), Theorem 1 gives, when
\(q^{1/2+\varepsilon_0}\ll x\leq q\),

\[
 |S_q(x;f)|\leq
 562x\frac{\log\log q}{\varepsilon_0\log q}
\tag{9.28}
\]

for every multiplicative \(|f|\leq1\).  Theorem 5 gives the stronger
\(xq^{-c\varepsilon_0^4}\) for \(f=\mu\), but only when \(q\) is prime.

On the ordered half \(r\leq s\), apply the most favorable composite
estimate (9.28) to the \(r\)-sum with \(q=s\), \(x\asymp R\), and
\(a=-h\delta\), temporarily assuming \((h\delta,s)=1\) and that partial
summation has absorbed the smooth weight.  On the other half, the exact
reciprocity formula
\(\bar r/s+\bar s/r\equiv1/(rs)\pmod1\) swaps \(r,s\); its extra smooth
factor \(e(-h\delta/(rs))\) is retained in the kernel.  Thus the prefix
condition \(x\leq q\) is respected on both ordered halves.  In the
balanced box \(R=S=T^3\), the result replaces one trivial length only by

\[
 R\frac{\log\log S}{\log S}.
\tag{9.29}
\]

After summing \(s\) and the \(A=LH=T^5\) pairs \((h,\delta)\), this is
still

\[
 RSA\frac{\log\log S}{\log S}
 =T^{11}\frac{\log\log T}{\log T},
\tag{9.30}
\]

against the local target \(RS=T^6\).  Thus the power gap remains exactly
\(T^{5-o(1)}\).  The omitted components \((h\delta,s)>1\) require an exact
gcd split and must be added; a componentwise upper-bound argument cannot
use them to supply the missing power.  The prime-modulus
theorem does not apply to the squarefree composite moduli carrying
\(\mu(s)\), and discarding those moduli would discard the original sum.

Hence the strongest directly matching one-variable theorem does not close
even a positive-length portion of the maximal \(a\)-range.  A viable use of
Möbius cancellation has to be simultaneous with the outer modulus or
\((h,\delta)\) averages, precisely as required in (9.13).

### 9.9 A two-orientation elementary Farey large-sieve bound

For completeness, one can improve the elementary completion diagnostic
without using Möbius cancellation.  After the separation justified in
Section 6.1, consider

\[
 \mathfrak T=
 \sum_{a\asymp A}\nu_a
 \sum_{r\asymp R}\sum_{s\asymp S\atop(r,s)=1}
 \alpha_r\beta_s e\left(-\frac{a\bar r}{s}\right).
\tag{9.31}
\]

For \((c,s)=1\), aggregate the repeated residue classes as

\[
 \gamma_{c,s}=\beta_s
 \sum_{r\asymp R\atop\bar r\equiv c\;({\rm mod}\ s)}\alpha_r.
\tag{9.32}
\]

The distinct reduced fractions \(c/s\), with \(s\asymp S\), are separated
by \(\gg S^{-2}\).  The additive large sieve and Cauchy--Schwarz give

\[
 |\mathfrak T|ll
 (A+S^2)^{1/2}\|\nu\|_2
 \left(\sum_{s,c}|\gamma_{c,s}|^2\right)^{1/2}.
\tag{9.33}
\]

Each residue class contains \(O(1+R/S)\) integers in the \(r\)-interval,
including its two incomplete endpoints.  Hence

\[
 \sum_{s,c}|\gamma_{c,s}|^2
 \ll(1+R/S)\|\alpha\|_2^2\|\beta\|_2^2,
\tag{9.34}
\]

and therefore

\[
 |\mathfrak T|ll_\varepsilon
 (A+S^2)^{1/2}(1+R/S)^{1/2}(RSA)^{1/2}T^\varepsilon.
\tag{9.35}
\]

Reciprocity supplies (9.35) with \(R,S\) interchanged.  The additional
factor \(e(-a/(rs))\) has derivatives controlled by
\(A/(RS)\ll T^{-1+\eta}\), so the same Fourier--Mellin separation costs
only \(T^\varepsilon\).

The polytope itself gives the exact simplification.  From
\(\rho-\sigma=k-m\) and \(k+m\leq1\),
\(|\rho-\sigma|\leq1\); combined with
\(a\leq\rho+\sigma-1\), this yields
\(a\leq2\min(\rho,\sigma)\), or
\(A\leq\min(R^2,S^2)T^\varepsilon\).  Choose the original orientation
when \(R\geq S\) and the reciprocal orientation when \(S\geq R\).  Then

\[
 \boxed{|\mathfrak T|\ll_\varepsilon RS\,A^{1/2}T^\varepsilon.}
\tag{9.36}
\]

Thus this two-orientation elementary large-sieve route loses exactly
\(T^{a/2}\) over the local target.  It covers the face \(a=0\), but no
positive \(a\)-box; at \((\rho,\sigma,a)=(3,3,5)\) its remaining gap is
\(T^{5/2+\varepsilon}\).  The exact-rational checker records this loss.
This sharper elementary diagnostic still confirms that this route cannot
provide the missing ingredient, which must
exploit the Möbius weights together with the coupled product
\(a=h\delta\), not merely Farey spacing or Euler products.

### 9.10 Two-sided finite Möbius decomposition and a dispersion interface

The one-sided sum (9.13) still treats \(\mu(r)\) as a single long
coefficient.  Fix depths \(I,J\geq1\), and apply (9.5) independently with
cutoffs \(V,U\), chosen so that

\[
 V^I\geq2R,\qquad U^J\geq2S,
\]

and put \(C_{i,V}=c_V^{*i}\), \(C_{j,U}=c_U^{*j}\).  Before expanding,
insert the harmless squarefree indicators \(\mu(r)^2\mu(s)^2\).  The
original coupled sum is then exactly

\[
 \boxed{
 \mathfrak S_q[\Psi]
 =\sum_{i<I}\sum_{j<J}(-1)^{i+j}
 \mathfrak E_{i,j,q}[\Psi],}
\tag{9.37}
\]

where

\[
\begin{aligned}
 \mathfrak E_{i,j,q}[\Psi]
 ={}&\sum_{v\leq V}\sum_{u\leq U}\mu(v)\mu(u)
 \sum_{\substack{w,n,h,\delta\\
                  vw\asymp R,\ un\asymp S\\
                  h\asymp H,\ \delta\asymp L\\
                  \mu(vw)^2=\mu(un)^2=1\\
                  (vw,un)=(q,vwun)=1}}
 C_{i,V}(w)C_{j,U}(n)\\
 &\quad\times p_N(qvw)p_N(qun)
 \Psi\left(\frac{vw}{R},\frac{un}{S},
           \frac{\delta}{L},\frac hH\right)
 e\left(-\frac{h\delta\overline{vw}}{un}\right).
\end{aligned}
\tag{9.38}
\]

This is a finite identity, not a Vaughan-identity asymptotic.  The
squarefree indicators imply

\[
 (v,w)=(u,n)=1,
\]

and the remaining coprimality in (9.38) makes the four factors across the
two sides pairwise coprime.  Consequently CRT gives the termwise identity

\[
 e_{un}\!\left(-a\overline{vw}\right)
 =
 e_u\!\left(-a\,\bar n\,\bar v\,\bar w\right)
 e_n\!\left(-a\,\bar u\,\bar v\,\bar w\right),
 \qquad a=h\delta.
\tag{9.39}
\]

All inverses in the first factor are taken modulo \(u\), and those in the
second modulo \(n\).  Formula (9.39) shows both the gain and the
obstruction of the double decomposition: two short Möbius averages are
now explicit, but neither is an independent coefficient because each
inverse phase still contains the variables from the other side.

There is a precise dispersion interface for the remaining cancellation.
Let

\[
 Z=\min(L,H),\qquad Y=\max(L,H),
\]

write \(z\) for the shorter of \(\delta,h\), and \(y\) for the other
variable.  After dyadically localizing \(u,v\), let
\(\mathcal B_{i,j;u,v}(z)\) denote the inner \(w,n,y\)-sum in (9.38) for
fixed \(u,v\); the displayed \(u,v\) sums below remain inside the absolute
value.  Cauchy--Schwarz shows
that the following mean-square statement is sufficient:

\[
 \boxed{
 \sum_{z\asymp Z}
 \left|
 \sum_{u\asymp U_0}\sum_{v\asymp V_0}
 \mu(u)\mu(v)\mathcal B_{i,j;u,v}(z)
 \right|^2
 \ll_{\varepsilon,W}
 \frac{R^2S^2}{Z}\,T^\varepsilon.}
\tag{9.40}
\]

Indeed, multiplication by \(Z^{1/2}\) after Cauchy gives
\(RS T^\varepsilon\); the fixed numbers of \(i,j\) and the logarithmically
many \(u,v\) boxes are absorbed into \(T^\varepsilon\).  Thus (9.40) for
all two-sided pieces implies CK\(_{\rm ub}(3)\) on the residual
\(\ell,h>0\) region.

The scale comparison is now explicit.  Joint completion gives only the
pointwise bound \(RS T^\varepsilon\) for each \(z\), hence the left side of
(9.40) is currently bounded by

\[
 ZR^2S^2T^\varepsilon,
\tag{9.41}
\]

which misses (9.40) by \(Z^2=T^{2\min(\ell,h)}\).  A random-term
square-root benchmark for the expanded \(w,n,y\)-sum is
\(ZRSY\); compared with the target in (9.40), it would still require the
additional power

\[
 T^{\max(0,\,2\min(\ell,h)+\max(\ell,h)-\rho-\sigma)}.
\tag{9.42}
\]

For the balanced maximal box, (9.41) misses by \(T^5\), while the
random-term benchmark (9.42) misses by \(T^{3/2}\).  Neither estimate is
claimed here.  Equations (9.37)--(9.40) identify one exact sufficient
mean-square theorem that a dispersion, spectral, or trace-function
argument could prove while retaining both Möbius averages and the product
\(h\delta\).  It is not asserted to be the weakest possible interface.
The finite checker verifies the two-sided convolution identity on every
integer pair in its test range; it does not certify (9.40).

### 9.11 Pascadi's 2024 spectral-dispersion corollary

Pascadi's Corollary 18 gives an incomplete Kloosterman bound with
simultaneous averages over variables \(r_{\rm P},s_{\rm P},n_{\rm P},
c_{\rm P},d_{\rm P}\):

\[
 \sum_{r_{\rm P},s_{\rm P}}w_{r_{\rm P},s_{\rm P}}
 \sum_{n_{\rm P}}a_{n_{\rm P},r_{\rm P},s_{\rm P}}
 \sum_{c_{\rm P},d_{\rm P}}
 \Phi\,e\left(\pm n_{\rm P}
 \frac{\overline{r_{\rm P}d_{\rm P}}}
 {s_{\rm P}c_{\rm P}}\right).
\tag{9.43}
\]

There is a direct, fully legitimate specialization to (6.3).  Split the
two signs of \(a\), take

\[
 R_{\rm P}=R,\quad S_{\rm P}=S,\quad N_{\rm P}=A,\quad
 C_{\rm P}=D_{\rm P}=1,
\tag{9.44}
\]

choose the smooth \(c_{\rm P},d_{\rm P}\) cutoffs to contain only the
integer 1, put \(a_{n_{\rm P},r_{\rm P},s_{\rm P}}=\nu(n_{\rm P})\),
and absorb the Möbius and Selberg weights into \(w_{r_{\rm P},s_{\rm P}}\).
The arbitrary-sequence large sieve hypothesis is available with
\(Y_{N_{\rm P}}=1\) and
\(A_{N_{\rm P},r_{\rm P},s_{\rm P}}\ll A^{1/2+\varepsilon}\).

Under (9.44), the corollary gives

\[
 |\mathfrak T_q|
 \ll_\varepsilon
 (RSA)^{1/2}
 \left\{
 AR+S(1+R)(RS+A)
 \right\}^{1/2}T^\varepsilon.
\tag{9.45}
\]

The admissible relation \(A\ll RS/T\) makes the expression in braces
\(\asymp R^2S^2\), up to endpoint constants and \(T^\varepsilon\).
Consequently the resulting scale is

\[
 |\mathfrak T_q|
 \ll_\varepsilon (RS)^{3/2}A^{1/2}T^\varepsilon,
\tag{9.46}
\]

whose loss over the local target has exponent
\((\rho+\sigma+a)/2\).  It is \(11/2\) in the balanced maximal box.
The frequency-concentration parameter in Pascadi's theorem modifies the
exceptional-spectrum multiplier, but the regular-spectrum term
\(S(1+R)(RS+A)\) already dominates here.  Thus even a stronger value of
that parameter does not create a covered box through this direct
specialization.

One can instead try to map \(v,w,u,n\) from (9.38) to
\(r_{\rm P},d_{\rm P},s_{\rm P},c_{\rm P}\).  That is not a direct
application of Corollary 18 because the \(c_{\rm P},d_{\rm P}\) variables
then carry the rough coefficients \(C_{i,V}(w)C_{j,U}(n)\), whereas the
corollary permits smooth weights there.  Removing those coefficients by
absolute values would discard the two-sided Type-II structure.  The
spectral-dispersion result is therefore recorded as a valid but
insufficient direct route, not as a proof of (9.40).

### 9.12 The direct fourfold scale and an exact gcd--character stratification

The mean-square interface (9.40) pays Cauchy--Schwarz in the shorter of
\(h,\delta\) before exploiting cancellation in the full sum.  This can be
substantially stronger than the original coupled-kernel target.  The
formal square-root scale of the uncut fourfold sum is

\[
 (RSLH)^{1/2}=(RSA)^{1/2}.
\tag{9.47}
\]

Since every retained box satisfies \(A\ll RS/T\),

\[
 \frac{RS}{(RSA)^{1/2}}
 =\left(\frac{RS}{A}\right)^{1/2}
 \gg T^{1/2-O(\eta)}.
\tag{9.48}
\]

Thus a genuine square-root estimate for the original \(r,s,h,\delta\)
sum would have a half-power margin everywhere in the polytope.  At the
balanced maximal box its diagnostic scale is \(T^{11/2}\), below the
\(T^6\) local target.  This is only a scale calculation; it does not
assert random cancellation.  It does show that the additional
\(T^{3/2}\) demanded by the random benchmark for (9.40) is a loss of that
particular Cauchy interface, not an intrinsic requirement of (6.0).

There is an exact way to expose all resonances before applying any
inequality.  Because \(\mu(s)\ne0\), \(s\) is squarefree.  For each term put

\[
 d=(|h|,s),\qquad e=(|\delta|,s/d),\qquad
 c=\frac{s}{de},\qquad h=dh_1,\quad \delta=e\delta_1.
\tag{9.49}
\]

Then \(d,e,c\) are pairwise coprime,
\((h_1,ec)=(\delta_1,c)=1\), and reduction of the inverse modulo every
divisor of \(s\) gives the termwise identity

\[
 \boxed{
 e_s(-h\delta\bar r)
 =e_c(-h_1\delta_1\bar r).}
\tag{9.50}
\]

Here the right side is \(1\) when \(c=1\).  For \(c>1\), define
\(\tau_c(\chi)=\sum_{x\bmod c}\chi(x)e_c(x)\).  Multiplicative
orthogonality on \((\mathbb Z/c\mathbb Z)^\times\) now separates the
three variables exactly:

\[
 \boxed{
 e_c(-h_1\delta_1\bar r)
 =\frac1{\varphi(c)}\sum_{\chi\ ({\rm mod}\ c)}
 \tau_c(\chi)\,\overline{\chi(-1)}
 \overline{\chi(h_1)}\overline{\chi(\delta_1)}\chi(r).}
\tag{9.51}
\]

After the already justified Fourier--Mellin separation (6.5), each
piece of (6.0) is therefore a finite linear combination of expressions
of the exact shape

\[
 \sum_{\substack{d,e,c\\dec\asymp S}}
 \frac{\mu(d)\mu(e)\mu(c)}{\varphi(c)}
 \sum_{\chi\ ({\rm mod}\ c)}\tau_c(\chi)\overline{\chi(-1)}
 \mathcal R_{d,e,c}(\chi)
 \mathcal H_{d,e,c}(\bar\chi)
 \mathcal D_{d,e,c}(\bar\chi),
\tag{9.52}
\]

with the pairwise coprimalities and the two exact-gcd conditions from
(9.49) retained in the three factors.  In particular, the fully resonant
part is precisely \(c=1\); it must be estimated together with the
\(\mu(d)\mu(e)\) divisor signs rather than hidden inside an absolute gcd
bound.  For \(c>1\), (9.52) replaces the additive inverse-product phase
by a hybrid character problem in which \(h_1,\delta_1,r\) are genuinely
separated and the modulus average still carries \(\mu(c)\tau_c(\chi)\).

The ordinary multiplicative large sieve does not close this interface.
Already on the unit stratum \(d=e=1\), use
\(|\tau_c(\chi)|\leq c^{1/2}\), the character large sieve for the
\(r\)-second moment, and the same inequality applied to the Dirichlet
convolution of each short sequence with itself for the \(h\)- and
\(\delta\)-fourth moments.  Since \(H,L\ll S T^\varepsilon\), Hölder gives

\[
 |\mathfrak S_{\rm unit}|
 \ll_\varepsilon
 S^{1/2}\bigl((S^2+R)R\bigr)^{1/2}A^{1/2}T^\varepsilon.
\tag{9.53}
\]

Reciprocity supplies (9.53) with \(R,S\) interchanged.  In the balanced
maximal box the right side is \(T^{17/2+\varepsilon}\), still
\(T^{5/2}\) above the \(T^6\) target.  Thus termwise character moments
recover no more than the previously visible balanced joint-completion
scale.

Dualizing the two long character sums explains why a termwise refinement
also stops at a genuine zeta-zero barrier.  For a primitive character and
the Fourier convention of Section 4, character Poisson summation is

\[
 \sum_n\bar\chi(n)W(n/X)
 =\frac{X}{c}\tau_c(\bar\chi)
   \sum_m\chi(m)\widehat W(mX/c).
\tag{9.54}
\]

Apply (9.54) with \(X=H,L\).  The dual lengths are \(c/H,c/L\), and
\(\tau_c(\chi)\tau_c(\bar\chi)=\chi(-1)c\).  After the conductor
decomposition for imprimitive characters, the lowest nonzero dual mode
contains a smooth multiple of

\[
 \frac{A}{S}
 \sum_{r\asymp R}\sum_{c\asymp S}
 \mu(r)\mu(c)e(\pm r/c).
\tag{9.55}
\]

This is a diagnostic component, not a lower bound for the full sum:
different conductors, dual frequencies, and gcd strata can still cancel.
If (9.55) is estimated separately in the balanced maximal box, however,
its double Möbius sum must be \(O(T^{4+\varepsilon})\).  Since
\(R=S=T^3\) and \(e(\pm r/c)\) is a smooth function of the compact ratio
\(r/c\), Mellin separation would require the power bound
\(\sum_{n\asymp X}\mu(n)n^{it}\ll X^{2/3+\varepsilon}\) for each factor.
The classical zero-free region supplies only a subexponential saving from
\(X\), not the required power.  Thus dualizing term by term reaches the
same \(2/3\) zero-free boundary that appears in the long-mollifier
literature; it cannot be used as an unconditional proof.

The new, strictly more faithful interface is therefore to prove (9.52)
before taking absolute values over the gcd strata, conductors, characters,
or moduli.  In particular, one cannot assume that the product
\(\mu(c)\tau_c(\chi)\) itself supplies a Möbius modulus average; the exact
conductor calculation below shows that it generally does not.  The finite checker
verifies (9.49)--(9.50) for all squarefree moduli and variables in its
test range and records both the exact exponent gap in (9.53) and the
\(2/3\) exponent forced by the separated lowest mode.  Formula (9.51) is
the standard finite character orthogonality identity, not an analytic
estimate.

This difficulty is consistent with the known status of long mollifiers.
The mollifier here is exactly the linear mollifier used in Farmer's
all-\(\theta\) conjecture.  Bettin--Gonek show that the stronger hypothesis
\(I_N(0,T)\ll_\varepsilon T^{1+\varepsilon}\), uniformly for every
\(N\le T^\theta\), would exclude zeros with
\(\Re s>1/2+1/(2\theta)\); at \(\theta=3\) that is the zero-free half-plane
\(\Re s>2/3\).  Their dyadic-interval theorem has the weaker boundary
\(1/2+2/\theta\), which is trivial at \(\theta=3\), so it does not turn the
specific present target into a quasi-Riemann-hypothesis claim.  It does,
however, confirm that a polynomial-length \(T^{1+\varepsilon}\) mollified
upper bound belongs to the open long-mollifier problem and is not a
routine consequence of the classical large sieve or an Euler product.

### 9.13 Exact conductor decomposition and mandatory inter-character cancellation

The factor \(\mu(c)\tau_c(\chi)\) in (9.52) does not retain a Möbius
sign on every modulus variable.  Write the squarefree modulus as
\(c=fk\), with \((f,k)=1\), and let the character modulo \(c\) be induced
by the primitive character \(\chi^*\) modulo \(f\).  CRT and the
Ramanujan sum over the \(k\)-component give the exact formula

\[
 \boxed{
 \tau_c(\chi)=\mu(k)\chi^*(k)\tau_f(\chi^*).}
\tag{9.56}
\]

Because \(c\) is squarefree,
\(\mu(c)=\mu(f)\mu(k)\).  Consequently

\[
 \boxed{
 \frac{\mu(c)\tau_c(\chi)}{\varphi(c)}
 =\frac{\mu(f)\tau_f(\chi^*)}{\varphi(f)}
  \frac{\chi^*(k)}{\varphi(k)}.}
\tag{9.57}
\]

The cofactor \(k\) carries no Möbius sign.  At conductor \(f=1\), the
induced character is the principal character \(\chi_{0,c}\), and
\(\tau_c(\chi_{0,c})=\mu(c)\).  Hence

\[
 \boxed{
 \frac{\mu(c)\tau_c(\chi_{0,c})}{\varphi(c)}
 =\frac1{\varphi(c)}.}
\tag{9.58}
\]

In particular, on the unit gcd stratum the principal-character piece is
exactly

\[
 \mathfrak P_{\rm unit}
 =\sum_{c\asymp S\atop \mu(c)^2=1}
   \frac{1}{\varphi(c)}
   \mathcal R_c(\chi_{0,c})
   \mathcal H_c(\chi_{0,c})
   \mathcal D_c(\chi_{0,c}),
\tag{9.59}
\]

with all coprimality cutoffs and smooth weights retained.  Its diagnostic
size is \(A\) times a smooth Möbius sum of length \(R\): the factor
\(1/\varphi(c)\) cancels the number of moduli only after the two principal
short sums contribute size \(HL=A\).  In the balanced maximal box,
estimating (9.59) separately at the \(RS=T^6\) target would require

\[
 \sum_{r\asymp T^3}\mu(r)W(r/T^3)
 \ll T^{1+\varepsilon}
 =(T^3)^{1/3+\varepsilon}.
\tag{9.60}
\]

Such a bound cannot hold uniformly for a dyadic partition of smooth
weights: it would continue \(1/\zeta(s)\) through the critical-line zeros.
Therefore the direct principal-character estimate cannot be closed even
by assuming a standard square-root Mertens bound.  A successful character
method must either extract additional cancellation from the exact
coprimality average in (9.59), or cancel its excess against the
nonprincipal characters in the complete sum (9.51).  This gives the
following strict constraint on the standard moment route:

> **No termwise standard character-moment closure.**  Applying the
> triangle inequality between the principal and nonprincipal characters,
> then replacing their coprimality sums by the standard character-moment
> bounds, cannot prove CK\(_{\rm ub}(3)\) on the balanced maximal box.

Equations (9.56)--(9.60) replace the earlier hope for independent
\(\mu(c)\tau_c(\chi)\) cancellation by the correct requirement: a
centered character or spectral transform must preserve cancellation
between the Ramanujan mean and the entire nonprincipal spectrum.  The
finite checker verifies the squarefree sign identity
\(\mu(fk)\mu(k)=\mu(f)\) and the exact balanced exponent \(1/3\); it does
not prove the required inter-character cancellation.

### 9.14 Global completion of the unit principal spectrum

The obstruction (9.59) arose after dyadically localizing \(h\) and then
estimating its principal-character projection.  For the actual Fourier
coefficients in (4.4), the unit gcd stratum can instead be summed over all
\(h\ne0\) before taking absolute values.  If \(s>1\), Möbius inversion of
the coprimality condition and Poisson summation give the exact identity

\[
\begin{aligned}
 \sum_{h\ne0\atop(h,s)=1}\widehat F(h/s)
 &=\sum_{j\mid s}\mu(j)
   \left\{\sum_{k\in\mathbb Z}\widehat F(jk/s)
                    -\widehat F(0)\right\}\\
 &=\boxed{\sum_{j\mid s}\mu(j)\frac{s}{j}
          \sum_{n\in\mathbb Z}F(ns/j).}
\end{aligned}
\tag{9.61}
\]

The zero-frequency terms cancel exactly because
\(\sum_{j\mid s}\mu(j)=0\).  This is a coprime reverse-Poisson identity,
not an estimate and not the ordinary \(h=0\) mode in Section 4.2.  On the
unit stratum \((h\delta,s)=1\), the principal multiplicative character
has phase average \(\mu(s)/\varphi(s)\).  Multiplication by the original
outer \(\mu(s)\) therefore yields

\[
 \frac1{\varphi(s)}
 \sum_{j\mid s}\mu(j)\frac{s}{j}
 \sum_n F_{r,s,\delta}(ns/j).
\tag{9.62}
\]

Put \(v=s/j\).  The support \(x\asymp M\) of the function in (4.4)
forces \(v\ll M\) and \(n\asymp M/v\); both incomplete endpoints are
included.  The core seminorm bounds (5.14), partial summation in the
smooth outer variables, and
\(\sum_{j\mid s}1\ll_\varepsilon s^\varepsilon\) consequently give the
following bound after summing the unit principal projection globally in
\(h\):

\[
 \boxed{
 |\mathfrak S^{\rm global}_{\rm pr,unit}|
 \ll_{\varepsilon,W} RLM\,T^\varepsilon.}
\tag{9.63}
\]

This intentionally keeps a conservative factor \(M\) for the lattice
sum in (9.61); normalization by the zero-frequency integral can only
improve it.  The exponent polytope proves exactly that this is sufficient.
Indeed, (5.12b)--(5.12c) give

\[
 \ell+m\leq2m+\rho-1\leq\sigma,
 \qquad\boxed{LM\leq S.}
\tag{9.64}
\]

Thus (9.63) is \(O(RS T^\varepsilon)\), including the balanced maximal
box where equality holds in (9.64).  Restoring the box prefactor in
(5.15) gives \(O(T^{1+\varepsilon}/q)\); the dyadic partitions and the
sum over \(q\) cost only \(T^\varepsilon\).  The already established
power-tail truncation permits the all-\(h\) completion before returning
to the retained core.

This proves a strictly weaker replacement for one part of the local CK
gate: the unit principal spectrum need not, and in the balanced box
cannot, be bounded characterwise inside every \(H\)-box.  It is removed
unconditionally by (9.61)--(9.64).  The remaining centered gate consists
of

1. the complete nonprincipal spectrum on the unit gcd stratum, with its
   Ramanujan mean subtracted only after (9.61); and
2. the principal and nonprincipal spectra on the nonunit gcd strata
   \(d e>1\) from (9.49).

No estimate for those two residual pieces is claimed here.  The finite
checker verifies the divisor formula for the coprime indicator and the
polytope margin \(\sigma-\ell-m\geq0\); the analytic identity (9.61)
follows from finite Möbius inversion followed by the stated Schwartz
Poisson formula.

### 9.15 Ramanujan projection of all nonunit principal strata

The complete principal projection can be written without choosing a gcd
stratum.  For every integer \(a\), averaging over the inverse unit group
gives

\[
 \frac1{\varphi(s)}\sum_{r\bmod s}^{*}e_s(-a\bar r)
 =\frac{c_s(a)}{\varphi(s)},
\tag{9.65}
\]

where \(c_s(a)\) is the Ramanujan sum.  Since the outer Möbius weight
forces \(s\) to be squarefree, its divisor formula becomes

\[
 \boxed{
 \mu(s)c_s(a)
 =\sum_{j\mid(s,a)}j\mu(j).}
\tag{9.66}
\]

This identity simultaneously contains the unit principal spectrum from
Section 9.14 and every nonunit principal gcd stratum.

Fix \(s,\delta\), and in a term of (9.66) put
\(w=(j,\delta)\), \(u=j/w\), and \(s=uwc\).  Then the factorization is
unique, \(w\mid\delta\), \((u,\delta)=1\), and
\(j\mid h\delta\) is equivalent to \(u\mid h\).  Writing \(h=uk\),
ordinary reverse Poisson gives

\[
 \boxed{
 \sum_{k\ne0}\widehat F(uk/s)
 =wc\sum_{n\in\mathbb Z}F(nwc)-\widehat F(0).}
\tag{9.67}
\]

The zero-frequency subtractions recombine exactly.  Indeed,

\[
 \sum_{j\mid s}j\mu(j)=\mu(s)\varphi(s),
\tag{9.68}
\]

so the total subtraction in the principal projection is
\(-\mu(s)\widehat F(0)\), the principal copy of the already extracted
Poisson zero mode.  It is therefore controlled by the LCM main form and
its archimedean error from Sections 4.2--4.3; it is not a new Region-D
remainder.

The lattice part of (9.67) is an exact residual Type-II sum.  Suppressing
only the already displayed smooth outer factors, it has the finite shape

\[
\begin{aligned}
 \mathfrak P_{\rm latt}
 ={}&\sum_{\substack{u,w,c\geq1\\uwc\asymp S}}
 \frac{uw\,\mu(u)\mu(w)}{\varphi(uwc)}
 \sum_{\substack{r\asymp R,\ \delta=w\delta_1\\
                  (r,uwc)=(u,\delta)=1}}
 \mu(r)\,\mathcal W(r,uwc,\delta)\\
 &\qquad\times
 \left\{wc\sum_{n\in\mathbb Z}
 F_{r,uwc,\delta}(nwc)\right\}.
\end{aligned}
\tag{9.69}
\]

Every endpoint, sign of \(\delta\), Selberg taper, and \(q\)-coprimality
condition is retained inside \(\mathcal W\).  No absolute value has been
taken over \(u,w,c,r,\delta_1\).  The support \(x\asymp M\) forces
\(wc\ll M T^\eta\).  Moreover \(u\mid h\) and the retained Fourier range
give \(u\ll H T^\eta\).  Since \(uwc\asymp S\),

\[
 \frac{S}{HT^\eta}\ll wc\ll MT^\eta,
 \qquad
 \frac{S}{MT^\eta}\ll u\ll HT^\eta.
\tag{9.70}
\]

But admissibility already gives \(HM\ll ST^\eta\).  Hence (9.70) is
empty by rapid Fourier decay unless

\[
 \boxed{
 HM=S T^{O(\eta)},\qquad
 wc=M T^{O(\eta)},\qquad
 u=H T^{O(\eta)}.}
\tag{9.71}
\]

Thus the nonunit principal remainder is not an arbitrary character sum:
it is a long--short Type-II form with the two required Möbius weights
\(\mu(r)\mu(u)\), an additional short sign \(\mu(w)\), and no inverse
phase left.  It is supported only on the top Fourier face
\(h=\sigma-m\), up to the declared \(O(\eta)\) slack.  In the balanced
maximal box,

\[
 wc=T^{1/2+O(\eta)},\qquad
 u=T^{5/2+O(\eta)}.
\tag{9.72}
\]

At this support, the elementary length count in (9.69) loses only
\(L/M\) over the \(RS\) target.  Its exponent is

\[
 |\mathfrak P_{\rm latt}|_{\rm trivial}
 \ll_{\varepsilon,W}RS\frac{L}{M}T^\varepsilon,
\]

and hence its exponent loss is

\[
 \boxed{\max(0,\ell-m),}
\tag{9.73}
\]

equal to \(2\) in the balanced box.  Consequently the full nonunit
principal spectrum is already proved outside the face
\(h=\sigma-m+O(\eta)\), and it is also proved on that face whenever
\(\ell\leq m\).  Its only residual polytope is therefore

\[
 h=\sigma-m+O(\eta),\qquad \ell>m.
\]

If the two separated smooth Möbius
sums of lengths \(R\) and \(S/M\) were both bounded by \(X^\beta\), the
largest common exponent sufficient for (9.69) would be

\[
 \beta\leq
 1-\frac{\max(0,\ell-m)}{\rho+\sigma-m};
 \qquad \beta\leq\frac7{11}
 \quad\hbox{in the balanced box}.
\tag{9.74}
\]

The classical zero-free region supplies only subexponential savings from
the trivial exponent \(1\), not the fixed \(7/11\) power.  Consequently
Mellin-separating the \(r,u\) sums is not an unconditional closure; their
cancellation must remain coupled to the centered nonprincipal spectrum.
Thus (9.69) remains unproved, but it is supported on a single parameter
face and has an exact residual loss rather than an arbitrary Region-D
gap.  The finite checker verifies (9.66), the face slack
\(\sigma-m-h\), the loss (9.73), and the exact \(7/11\) diagnostic in
(9.74).

### 9.16 Reverse completion of the unit spectrum and the affine-correlation gate

The remaining unit nonprincipal spectrum also has an exact global
description.  Keep the Fourier convention
\(\widehat F(y)=\int_{\mathbb R}F(x)e(-xy)\,dx\), fix \(s>1\), and assume
\((\delta,s)=1\).  Splitting \(h\) into reduced residue classes modulo
\(s\), followed by shifted Poisson summation, gives

\[
 \boxed{
 \sum_{h\in\mathbb Z\atop(h,s)=1}
 e_s(-h\delta\bar r)\widehat F(h/s)
 =\sum_{n\in\mathbb Z}F(n)c_s(n+\delta\bar r).}
\tag{9.75}
\]

The plus sign is forced by the stated Fourier convention:
\(\sum_{j\in\mathbb Z}\widehat F(j+b/s)
=\sum_nF(n)e_s(-bn)\).  Thus (9.75) reconstructs the original residue
class \(n\equiv-\delta\bar r\pmod s\).  The endpoint \(s=1\) is a finite
degenerate modulus and is kept separately; it creates no long box.

Use

\[
 c_s(x)=\sum_{d\mid(s,x)}d\,\mu(s/d).
\tag{9.76}
\]

The highest-divisor term \(d=s\) in (9.76) is
\(s\mathbf1_{s\mid x}\).  After multiplication by the outer
\(\mu(s)\), it produces the exact congruence

\[
 n+\delta\bar r\equiv0\pmod s
 \quad\Longleftrightarrow\quad
 rn+\delta=ks
\tag{9.77}
\]

for an integer \(k\asymp K\).  Equivalently, after the explicit rename
\(\Delta=-\delta\), the equation is \(rn-ks=\Delta\).  For fixed
\(n,k,\Delta\), put \(g=(n,k)\).  Solutions exist only if
\(g\mid\Delta\); if \((r_0,s_0)\) is one solution, every integral
solution is

\[
 \boxed{
 r=r_0+\frac{k}{g}t,\qquad
 s=s_0+\frac{n}{g}t,\qquad t\in\mathbb Z.}
\tag{9.78}
\]

The dyadic restrictions cut (9.78) to an interval
\(I_{n,k,\Delta}\) of length
\(O(1+Rg/K)=O(1+Sg/M)\); both incomplete endpoints are included.  Hence
the highest-divisor term is a weighted average of the binary affine
Möbius correlations

\[
 \sum_{t\in I_{n,k,\Delta}}
 \mu\left(r_0+\frac{k}{g}t\right)
 \mu\left(s_0+\frac{n}{g}t\right)
 \mathcal W_{n,k,\Delta}(t).
\tag{9.79}
\]

This is still a finite identity: \(n,k,\Delta,t\) range over bounded
sets fixed by the dyadic cutoffs, and the original Selberg tapers,
coprimalities, signs, exact logarithmic phase, and endpoint weights are
all retained in \(\mathcal W\).

The normalization can be read directly from (4.4)--(4.5).  In the
highest-divisor term the factor \(s\) in (9.76) cancels the Poisson
factor \(1/s\).  On (9.77), the remaining square-root denominator is
\(\sqrt{rsnk}\), while the \(t\)-integral has scale \(T\).  Therefore a
sufficient weighted affine-correlation estimate is

\[
 \boxed{
 |\mathcal C_\mu(R,S,M,K,L)|
 \ll_{\varepsilon,W}(RSMK)^{1/2}T^\varepsilon,}
\tag{9.80}
\]

where \(\mathcal C_\mu\) denotes the complete signed sum in
(9.79), before the factor \(T/(q\sqrt{RSMK})\) is restored.  Formula
(9.80) would give \(O(T^{1+\varepsilon}/q)\) for this Ramanujan component.

For comparison, an elementary solution count gives

\[
 \begin{aligned}
 \#\mathcal C
 &\ll_\varepsilon
 \sum_{n\asymp M}\sum_{k\asymp K}
 \left(\frac Lg+1\right)
 \left(1+\frac{Rg}{K}\right)T^\varepsilon\\
 &\ll_\varepsilon (MKL+MRL)T^\varepsilon
 \ll_\varepsilon RS T^\varepsilon.
 \end{aligned}
\tag{9.81}
\]

Here the last line uses the finite divisor count
\(\sum_{n\asymp M,k\asymp K}(n,k)\ll MK T^\varepsilon\), together with
\(MK\ll T\), \(L\ll MR/T\), and \(LM\ll S\) from (9.64).  No
cancellation is used in (9.81).

At exponent level, the gap between (9.81) and (9.80) is

\[
 \boxed{
 \max\left(0,
 \max(m+k+\ell,\,m+\rho+\ell)
 -\frac{\rho+\sigma+m+k}{2}\right).}
\tag{9.82}
\]

It equals \(5/2\) in the balanced maximal box.  The generic affine
parameter interval there also has length exponent
\(\rho-k=5/2\).  Thus a termwise treatment of (9.79) would need, on
average over \(n,k,\Delta\), essentially the entire length of the
binary Möbius progression as cancellation.  This is an averaged
two-linear-forms Chowla-type estimate with coefficients and endpoints
varying through the full dyadic family; no theorem cited in Sections
8--9 supplies (9.80).

The highest-divisor term is a diagnostic sufficient subproblem, not a
claim that it must be bounded separately.  The lower divisors in (9.76),
the globally completed principal mean (9.61)--(9.64), and (9.79) may
cancel only when kept together.  Accordingly the genuinely weakest
remaining unit gate is the centered full Ramanujan-weighted sum obtained
from (9.75) after subtracting the proved global principal contribution.
Equations (9.77)--(9.82) show exactly why isolating its top congruence by
the triangle inequality reaches an unproved averaged affine Möbius
correlation rather than an unconditional closure.

### 9.17 Exact audit of averaged Chowla on the affine family

The averaged Chowla theorem of Matomäki--Radziwiłł--Tao does apply to a
specific absolute-value relaxation of (9.79), so its quantitative effect
can be evaluated exactly.  In (9.78) write

\[
 a_0=k/g,\qquad b_0=n/g,\qquad D=\Delta/g,
 \qquad (a_0,b_0)=1.
\tag{9.83}
\]

Fix a residue class \(D_0\pmod {a_0}\), choose \(r_0\) with
\(b_0r_0\equiv D_0\pmod {a_0}\), and put
\(s_0=(b_0r_0-D_0)/a_0\).  Then the family
\(D=D_0+a_0j\) is represented exactly by

\[
 b_0r_0-a_0(s_0-j)=D_0+a_0j.
\tag{9.84}
\]

Thus, after translating the \(t\)-interval and applying partial
summation to the smooth weights, varying \(\Delta\) in one residue class
is an additive-shift average of two linear-form Möbius correlations.
There are \(a_0\) residue classes, each containing
\(H_0\asymp L/(ga_0)=L/k\) shifts, and the \(t\)-length is
\(X_0\asymp R/a_0\).

Theorem 1.6 of Matomäki--Radziwiłł--Tao bounds such a shift average by

\[
 \ll A_0^2
 \left(
 e^{-\mathcal M/80}
 +\frac{\log\log H_0}{\log H_0}
 +\frac1{\log^{1/3000}X_0}
 \right)H_0X_0,
 \qquad A_0=\max(a_0,b_0),
\tag{9.85}
\]

under its stated size conditions.  The theorem applies directly with
\(g_1=g_2=\mu\), since \(\mu\) is 1-bounded and multiplicative; its
pretentiousness input has the same prime values as Liouville.  This does
not improve the displayed rate.  The factor \(A_0^2\) is part of the
theorem, not a suppressed constant.

In the balanced maximal box, generically

\[
 A_0=T^{1/2+o(1)},\qquad
 H_0=T^{2+o(1)},\qquad
 X_0=T^{5/2+o(1)}.
\tag{9.86}
\]

Consequently (9.85) is worse than the trivial shift average by the
factor \(T^{1-o(1)}\).  Even deleting \(A_0^2\) hypothetically would
leave only a logarithmic saving, whereas (9.80) requires the power
\(T^{5/2}\) at this box.  The exceptional-shift refinement in the same
paper gives a power saving only in the number of exceptional shifts
while retaining a weak individual correlation bound; it likewise does
not reach (9.80).

This is a genuine applicability calculation rather than a keyword
comparison: (9.84) supplies the exact bridge to the published theorem,
and (9.85)--(9.86) show that its quantitative output covers no part of
the balanced polynomial-slope face.  The centered full Ramanujan sum
could still exploit cancellation lost by the absolute values in
(9.85), but that would require a new coupled estimate.

### 9.18 The centered divisor--dual identity

There is a weaker exact interface which does not isolate the
highest-divisor term.  Averaging (9.75) over \(r\bmod s\) first gives the
finite identity

\[
 \sum_{r\bmod s}^{*}c_s(n+\delta\bar r)
 =\mu(s)c_s(n),\qquad (\delta,s)=1.
\tag{9.87}
\]

Indeed, expand the left side as a sum over \(h\bmod s\) with
\((h,s)=1\); the inner \(r\)-sum is
\(c_s(h\delta)=\mu(s)\).  Consequently the exact centered kernel after
the outer \(\mu(s)\) is

\[
 \boxed{
 \mathscr C_s(n,r,\delta)
 =\mu(s)c_s(n+\delta\bar r)-\frac{c_s(n)}{\varphi(s)},
 \qquad
 \sum_{r\bmod s}^{*}\mathscr C_s(n,r,\delta)=0.}
\tag{9.88}
\]

The second term in (9.88) is exactly the globally completed principal
projection from (9.61)--(9.64), now written after the reverse transform.
Thus no boxwise principal/nonprincipal triangle inequality has been
inserted.

Next apply (9.76) before summing \(n\).  For \(j\mid s\), lattice Poisson
with residue \(-\delta\bar r\pmod j\) gives

\[
 j\sum_{n\equiv-\delta\bar r\ ({\rm mod}\ j)}F(n)
 =\sum_{v\in\mathbb Z}e_j(-v\delta\bar r)\widehat F(v/j).
\tag{9.89}
\]

Both continuous zero frequencies cancel exactly.  More precisely, for
\(s>1\),

\[
\boxed{
\begin{aligned}
 \sum_nF(n)\mathscr C_s(n,r,\delta)
 ={}&\sum_{j\mid s}\mu(j)
       \sum_{v\ne0}e_j(-v\delta\bar r)\widehat F(v/j)\\
 &-\frac1{\varphi(s)}
   \sum_{j\mid s}\mu(s/j)
       \sum_{v\ne0}\widehat F(v/j).
\end{aligned}}
\tag{9.90}
\]

The \(v=0\) coefficient in the first line is
\(\sum_{j\mid s}\mu(j)=0\), and in the second it is
\(\varphi(s)^{-1}\sum_{j\mid s}\mu(s/j)=0\).  These are exact finite
divisor cancellations; no decay estimate is used.

In fact every common integral dual frequency cancels before localizing
\(j\).  For fixed \(q\in\mathbb Z\), the terms \(v=qj\) have phase 1
and Fourier argument \(v/j=q\), so their coefficients are respectively

\[
 \widehat F(q)\sum_{j\mid s}\mu(j)=0,
 \qquad
 \frac{\widehat F(q)}{\varphi(s)}
 \sum_{j\mid s}\mu(s/j)=0.
\tag{9.90a}
\]

Thus the remaining divisor-dual sum may be restricted to \(j\nmid v\).
This removes the otherwise exceptional nonoscillating modes when
\(M\asymp1\).

The core seminorms imply that a nonzero term in (9.90) is rapidly small
unless

\[
 j\gg MT^{-O(\eta)},\qquad
 1\leq |v|\ll \frac jM T^{O(\eta)}.
\tag{9.91}
\]

Writing \(s=jc\), the full lower-divisor family is therefore confined to

\[
 c\ll\frac SM T^{O(\eta)}.
\tag{9.92}
\]

The top affine correlation of Section 9.16 is the endpoint \(c=1\),
whereas every \(c>1\) lower Ramanujan divisor remains in the same signed
sum.  Notice again that the cofactor \(c\) has no Möbius sign: the only
long signs in the first line of (9.90) are \(\mu(r)\mu(j)\).  Hence
(9.90) is not closed by an Euler-product estimate, but it is strictly
weaker than (9.80) because it preserves cancellation among every divisor
and the proved principal subtraction.

This centered divisor--dual sum is the current sharpest residual unit
gate.  A proof would require a two-Möbius dispersion estimate, averaged
simultaneously over \(j,c,v,\delta\), at the exact support (9.91)--(9.92).
The identity itself is unconditional and directly formalizable; the
estimate is not proved here.

### 9.19 Delta completion and the self-dual affine obstruction

The first line of (9.90) still retains the product phase
\(e_j(-v\delta\bar r)\), so one should next exploit the full smooth
\(\delta\)-sum rather than replace it by its length.  Localize
\(j\asymp J\).  Poisson summation, or repeated summation by parts with
the core seminorms, shows that the signed least residue \(b\) defined by

\[
 b\equiv v\bar r\pmod j,qquad |b|\leq j/2,
\tag{9.93}
\]

is negligible unless

\[
 |b|\ll \frac JL T^{O(\eta)}.
\tag{9.94}
\]

The exact logarithmic phase is part of the smooth \(\delta\)-weight.
Its normalized derivatives are \(T^{O(\eta)}\), so it enlarges the dual
window only by the displayed slack in (9.94).  All dual endpoints and
the two signs are included.  By (9.90a), the surviving residue \(b\) is
nonzero; hence (9.94) also forces \(J\gg LT^{-O(\eta)}\).

Multiplying (9.93) by \(r\) gives an integer \(z\) such that

\[
 \boxed{br-v=zj.}
\tag{9.95}
\]

On the effective support (9.91), the four new lengths are

\[
 |b|\ll B:=J/L,qquad |v|\ll V:=J/M,qquad
 |z|\ll Z:=R/L,qquad j\asymp J.
\tag{9.96}
\]

For fixed \(b,z,v\), put \(g=(b,z)\).  Equation (9.95) has solutions
only if \(g\mid v\), and every solution is

\[
 \boxed{
 r=r_0+\frac zg t,qquad
 j=j_0+\frac bg t,qquad t\in\mathbb Z.}
\tag{9.97}
\]

The dyadic restrictions cut (9.97) to length

\[
 O\left(1+\min\left(\frac{Rg}{Z},\frac{Jg}{B}\right)\right)
 =O(1+Lg),
\tag{9.98}
\]

with the equality interpreted up to the fixed dyadic and
\(T^{O(\eta)}\) slack.  The Möbius signs along this progression are
exactly \(\mu(r)\mu(j)\); the cofactor \(c=s/j\) remains signless.

At the balanced endpoint \(J=S=T^3\),

\[
 B=Z=T^{1/2},\qquad V=L=T^{5/2},
\tag{9.99}
\]

and a generic progression (9.97) again has length \(T^{5/2}\).  Thus
smooth \(\delta\)-completion supplies the full \(L\)-saving, but the
remaining congruence reconstitutes the same polynomial-slope binary
Möbius correlation as (9.79), with the roles of the short variables
dualized.  Applying the averaged-Chowla relaxation of Section 9.17 to
(9.97) again gives only logarithmic cancellation and incurs a generic
\(T\) slope loss.

This self-duality rules out the proposed elementary closure
``reverse \(n\), then complete \(\delta\)''.  It does not rule out a
joint dispersion argument which keeps \(b,z,v,j,c\) inside one signed
mean square; such an argument is precisely the remaining analytic
problem.

### 9.20 One-dimensional coverage certificate after centering

Write \(J=T^{\jmath}\).  Equations (9.91)--(9.98) reduce every scale in
the centered unit problem to

\[
 \max(m,\ell)\leq\jmath\leq\sigma,qquad
 \begin{array}{c|ccccc}
  \text{variable}&c&v&b&z&t\text{-interval}\\ \hline
  \text{exponent}&\sigma-\jmath&\jmath-m&
  \jmath-\ell&\rho-\ell&\ell.
 \end{array}
\tag{9.100}
\]

This is checked by exact rational arithmetic.  It gives three immediate
coverage certificates.

First, completing \(\delta\) and then counting the surviving \(v\)'s
loses exactly \(T^{\jmath-m}\).  Second, applying the averaged-Chowla
theorem termwise to (9.97) carries the polynomial-slope factor

\[
 T^{2\max(\jmath-\ell,\,\rho-\ell)}.
\tag{9.101}
\]

Third, the direct spectral-dispersion specialization (9.45)--(9.46), now
with modulus length \(J\) and product length
\(A'=VL=T^{\jmath-m+\ell}\), loses over the \(RJ\) target the exponent

\[
 \frac{\rho+\jmath+(\jmath-m+\ell)}2.
\tag{9.102}
\]

The signless cofactor sum of length \(C=S/J\) multiplies both the bound
and its target and therefore does not change (9.102).

For the balanced maximal box,
\(\jmath\in[5/2,3]\).  Across this entire interval,

\[
 \jmath-m\in[2,5/2],\qquad
 2\max(\jmath-\ell,\rho-\ell)=1,
\]

and (9.102) ranges from \(5\) to \(11/2\).  Hence none of the three
termwise routes covers even a subinterval of the new \(J\)-range.  Any
improvement must average the two Möbius signs jointly with at least one
of \(b,z,v,c\); the support reduction alone is not the missing estimate.

### 9.21 Re-audit of Wright's unbalanced-convolution corollary

Equation (9.95) does admit a direct convolution interpretation:
\(br\equiv v\pmod j\).  For fixed \(v\), the product sequence has total
length

\[
 X_0=BR=T^{\rho+\jmath-\ell},qquad
 Q=J=T^\jmath,qquad N_0=B=T^{\jmath-\ell}.
\tag{9.103}
\]

The long coefficient \(\mu(r)\) satisfies the fixed-small-modulus
Siegel--Walfisz hypothesis required in Wright's convolution application,
so coefficient type is not the obstruction.  The modulus range is.
The two advertised modulus regimes require respectively

\[
 Q\leq X_0^{17/33-\varepsilon},qquad
 Q\leq X_0^{45/89-\varepsilon}.
\tag{9.104}
\]

For the balanced maximal box, \(X_0=T^{\jmath+1/2}\) and
\(5/2\leq\jmath\leq3\).  The exact endpoint margins
\(\gamma(\jmath+1/2)-\jmath\) are

\[
\begin{array}{c|cc}
 \gamma&\jmath=5/2&\jmath=3\\ \hline
 17/33&-21/22&-79/66\\
 45/89&-175/178&-219/178.
\end{array}
\tag{9.105}
\]

They are affine and negative at both endpoints, hence negative throughout
the interval.  Thus the corollary does not apply to any balanced
post-centering \(J\)-box.  Moreover its discrepancy is stated for a fixed
residue \(v\); summing it termwise over the present
\(V=J/M\) residues would retain exactly the loss identified in
Section 9.20.  The newer partially fixed-modulus theorem therefore gives
no hidden closure after the centered transform.

### 9.22 Fourier-energy form and the central-arc barrier

The self-dual equation also admits a useful additive-energy formulation.
For one separated smooth piece, define the convolution coefficients

\[
 A_x=\sum_{br=x}\alpha_b\mu(r),\qquad
 B_y=\sum_{zj=y}\beta_z\mu(j),
\tag{9.106}
\]

with the dyadic and coprimality restrictions retained in the coefficients.
Both sequences have the same ambient length

\[
 X_0=BR=ZJ=T^{\rho+\jmath-\ell},
 \qquad V=J/M=T^{\jmath-m}.
\tag{9.107}
\]

After delta completion, a typical difference kernel has the exact Fourier
form

\[
\begin{aligned}
 \sum_{x,y}A_x\overline{B_y}
 W_0\left(\frac{x-y}{V}\right)
 =V\int_{\mathbb R}\widehat W_0(V\alpha)
 \mathcal A(\alpha)\overline{\mathcal B(\alpha)}\,d\alpha,
\end{aligned}
\tag{9.108}
\]

where \(\mathcal A(\alpha)=\sum_xA_xe(\alpha x)\), and similarly for
\(\mathcal B\).  Periodizing the rapidly decaying multiplier and applying
Parseval with only divisor-bounded coefficients gives

\[
 |(9.108)|\ll_\varepsilon
 V\|A\|_2\|B\|_2T^\varepsilon
 \ll_\varepsilon VX_0T^\varepsilon.
\tag{9.109}
\]

Thus the general-coefficient Fourier route loses exactly the same
\(V=J/M\) found in Section 9.20.

This also gives a genuine unconditional boundary box which should not be
left inside the residual gate.  If

\[
 \boxed{J\leq M T^{O(\eta)},}
\tag{9.109a}
\]

then \(V\ll T^{O(\eta)}\), so (9.109) is already
\(O(X_0T^\varepsilon)\).  At zero slack this is exactly
\(\jmath=m\).  Since (9.100) requires
\(\jmath\geq\max(m,\ell)\), this face can occur only when
\(\ell\leq m\).  Therefore the centered unit nonprincipal spectrum is
proved on every divisor-dual box with \(J/M=T^{O(\eta)}\); only

\[
 J/M=T^{\Omega(1)}
\tag{9.109b}
\]

can contribute to the polynomial residual.  This does not meet the
balanced box, where \(J/M\in[T^2,T^{5/2}]\), but it removes the complete
low-divisor face without a Möbius estimate.  The exact-rational checker
records the loss \(\jmath-m\) and the forced inequality
\(\ell\leq m\) when that loss vanishes.

The central arc explains why a separated Euler-product estimate does not
remove this loss.  Suppose, only for this diagnostic, that the two smooth
Möbius sums of lengths \(R\) and \(J\) are bounded by
\(R^{\beta+\varepsilon}\) and \(J^{\beta+\varepsilon}\).  On an arc of
width \(X_0^{-1}\), absolute estimation of (9.108) has scale

\[
 \frac V{X_0}\,BZ R^\beta J^\beta
 =VX_0(RJ)^{\beta-1}.
\]

For this to be at most the target \(X_0T^\varepsilon\), one needs

\[
 \boxed{
 \beta\leq1-\frac{\jmath-m}{\rho+\jmath}.}
\tag{9.110}
\]

In the balanced maximal box, (9.110) equals \(7/11\) at
\(\jmath=5/2\) and decreases to \(7/12\) at \(\jmath=3\).  The
classical zero-free region gives no fixed exponent below 1, so it cannot
prove this central-arc estimate.

Equation (9.110) is a limitation of the separated absolute Fourier route,
not a necessary condition for the original coupled kernel.  There are
exactly two possible ways past it: prove genuinely joint two-Möbius
Fourier flatness on arcs of width \(1/V\), or exploit a vanishing moment
of the complete coupled archimedean multiplier before separation.  No
such flatness or vanishing moment has been established above.

### 9.23 Global reverse completion of every nonprincipal gcd stratum

The unit centered identity extends exactly to the full gcd decomposition
(9.49).  Fix pairwise coprime squarefree \(d,e,c\), put
\(s=dec\), \(h=dh_1\), \(\delta=e\delta_1\), and set
\(\alpha=\delta_1\bar r\pmod c\).  Then
\((h_1,ec)=1\) and \((\alpha,c)=1\).  Since
\(dh_1/s=h_1/(ec)\), finite Möbius inversion of the condition
\((h_1,e)=1\), followed by shifted Poisson summation, gives

\[
\begin{aligned}
 &\sum_{h_1\in\mathbb Z\atop(h_1,ec)=1}
 e_c(-h_1\alpha)\widehat F(h_1/(ec))\\
 &\quad=\sum_{k\mid e}\mu(k)
 \sum_{y\in\mathbb Z\atop(y,c)=1}
 e_c(-ky\alpha)\widehat F\left(\frac{ky}{ec}\right)\\
 &\quad=\boxed{
 \sum_{k\mid e}\mu(k)\frac ek
 \sum_{n\in\mathbb Z}F((e/k)n)c_c(n+k\alpha).}
\end{aligned}
\tag{9.111}
\]

The sign in the last Ramanujan sum again follows from the Fourier
convention: for \(E=e/k\),

\[
 \sum_{\ell\in\mathbb Z}
 \widehat F((\ell+b/c)/E)
 =E\sum_nF(En)e_c(-nb).
\tag{9.112}
\]

Formula (9.111) retains every divisor \(k\mid e\), both incomplete
endpoints, and the dilation \(e/k\); none may be absorbed into a generic
divisor-bounded coefficient before estimating the gcd strata jointly.

The principal character modulo \(c\) has phase average
\(\mu(c)/\varphi(c)\).  Multiplying (9.111) by the original
\(\mu(s)=\mu(d)\mu(e)\mu(c)\) and subtracting this principal mean yields
the exact nonprincipal kernel

\[
\boxed{
\begin{aligned}
 \mathfrak N_{d,e,c}(r,\delta_1)
 ={}&\mu(d)\mu(e)
 \sum_{k\mid e}\mu(k)\frac ek
 \sum_nF((e/k)n)\\
 &\times\left\{
 \mu(c)c_c(n+k\delta_1\bar r)
 -\frac{c_c(n)}{\varphi(c)}\right\}.
\end{aligned}}
\tag{9.113}
\]

For every \(k\mid e\), the shift \(k\delta_1\) is a unit modulo \(c\).
Therefore (9.87) gives

\[
 \boxed{
 \sum_{r\bmod c}^{*}
 \left\{\mu(c)c_c(n+k\delta_1\bar r)
 -\frac{c_c(n)}{\varphi(c)}\right\}=0.}
\tag{9.114}
\]

When \(c=1\), the bracket in (9.113) is identically zero, exactly as it
must be: the fully resonant stratum has no nonprincipal character.  The
possible omitted \(h_1=0\) endpoint when \(e=c=1\) belongs to the already
extracted Poisson zero mode and disappears from (9.113) as well.

Thus there is no third, unrelated ``nonunit nonprincipal character
gate''.  Every nonprincipal gcd stratum is a dilated centered Ramanujan
kernel of the same type as (9.88), with the additional exact signs
\(\mu(d)\mu(e)\mu(k)\) and lattice scale \(e/k\).  The remaining full
nonprincipal estimate can be stated as the single family

\[
 \boxed{
 \sum_{\substack{d,e,c\ {\rm pairwise\ coprime}\\dec\asymp S}}
 \sum_{r,\delta_1}
 \mu(r)\,\mathfrak N_{d,e,c}(r,\delta_1)
 \mathcal W_{d,e,c}(r,\delta_1)
 \ll_{\varepsilon,W}RS T^\varepsilon.}
\tag{9.115}
\]

All original Selberg tapers, \(q\)-coprimalities, dyadic endpoints, and
coupled archimedean factors remain in \(\mathcal W\).  Equation (9.115)
is still unproved, but it is strictly more faithful than estimating the
characters in (9.52) separately and it now covers every nonprincipal gcd
stratum with one exact centered interface.

### 9.24 Exact recombination and the weakest residual interface

It would still be stronger than the original problem to demand separate
\(O(RS T^\varepsilon)\) bounds for (9.69) and (9.115).  The subtraction
in (9.113) is the local principal projection, so cancellation between it
and the global principal lattice must remain available.  For fixed
\(d,e,c,r,\delta_1\), define that local projection by

\[
\boxed{
 \mathfrak P_{d,e,c}(r,\delta_1)
 =\mu(d)\mu(e)
 \sum_{k\mid e}\mu(k)\frac ek
 \sum_nF((e/k)n)\frac{c_c(n)}{\varphi(c)}.}
\tag{9.116}
\]

Here \(F\) retains its full dependence on the fixed outer variables; only
the displayed arithmetic factor is independent of the inverse residue.
Adding (9.116) to (9.113) gives the termwise identity

\[
\boxed{
 \mathfrak N_{d,e,c}(r,\delta_1)
 +\mathfrak P_{d,e,c}(r,\delta_1)
 =\mu(d)\mu(e)\mu(c)
 \sum_{k\mid e}\mu(k)\frac ek
 \sum_nF((e/k)n)c_c(n+k\delta_1\bar r).}
\tag{9.117}
\]

Thus the centered and principal pieces recombine exactly to the original
outer-Möbius-weighted phase after the scaled reverse Poisson transform.
For \(c=1\), (9.113) vanishes and (9.116) is the whole expression, as
required.  Summing (9.116) over the unique gcd decomposition (9.49), and
then using (9.66)--(9.68), recovers the lattice part (9.69) together with
its already controlled zero-mode subtraction.  No boundary term is left
between the two descriptions.

Let \(\mathfrak P_{\rm top}\) denote only the residual part of (9.69) on

\[
 HM=S T^{O(\eta)},\qquad \ell>m,
\tag{9.118}
\]

and let \(\mathfrak N_{\rm all}\) denote (9.115), restricted to boxes not
already covered by Sections 8 and 9.14.  All complementary principal
pieces are \(O(RS T^\varepsilon)\) by (9.63)--(9.73), and the tail is
already controlled by (6.12).  Consequently the weakest residual
statement furnished by the exact reductions in this note is the joint
gate

\[
\boxed{
 \left|\mathfrak P_{\rm top}+\mathfrak N_{\rm all}\right|
 \ll_{\varepsilon,W}RS T^\varepsilon.}
\tag{9.119}
\]

Equation (9.119) is strictly weaker than proving (9.69) and (9.115)
separately, and strictly more explicit than CK\(_{\rm ub}(3)\): every
summand is given by (9.69), (9.111), and (9.113), while all proved
complementary pieces have been removed.  It is still unproved.  In
particular, (9.117) also shows why a formal cancellation of the principal
subtraction cannot by itself close the problem: using that cancellation
merely reconstructs the original uncentered coupled kernel.

### 9.25 Divisor duality and self-duality on every gcd stratum

The generalized centered kernel (9.113) admits the same second duality as
the unit kernel, including the dilation.  Fix one \(k\mid e\), put
\(E=e/k\), and suppress the common factor
\(\mu(d)\mu(e)\mu(k)\).  The squarefree divisor formula gives exactly

\[
\begin{aligned}
 &E\sum_nF(En)
 \left\{\mu(c)c_c(n+k\alpha)-\frac{c_c(n)}{\varphi(c)}\right\}\\
 ={}&E\sum_{j\mid c}j\mu(j)
       \sum_{n\equiv-k\alpha\ ({\rm mod}\ j)}F(En)\\
 &-\frac E{\varphi(c)}\sum_{j\mid c}j\mu(c/j)
       \sum_{n\equiv0\ ({\rm mod}\ j)}F(En).
\end{aligned}
\tag{9.120}
\]

Apply lattice Poisson to \(G(x)=F(Ex)\), for which
\(\widehat G(\xi)=E^{-1}\widehat F(\xi/E)\).  The outer factor \(E\)
cancels this Jacobian and yields

\[
\boxed{
\begin{aligned}
 (9.120)={}&\sum_{j\mid c}\mu(j)
       \sum_{v\in\mathbb Z}e_j(-vk\alpha)
       \widehat F\left(\frac v{jE}\right)\\
 &-\frac1{\varphi(c)}\sum_{j\mid c}\mu(c/j)
       \sum_{v\in\mathbb Z}
       \widehat F\left(\frac v{jE}\right).
\end{aligned}}
\tag{9.121}
\]

This identity contains an exact cancellation stronger than the ordinary
zero-frequency cancellation.  For a fixed \(q\in\mathbb Z\), take the
common physical frequency

\[
 v=qjE.
\tag{9.122}
\]

Its phase is \(e_j(-qjEk\alpha)=e_j(-qje\alpha)=1\), and its two
coefficients are respectively
\(\sum_{j\mid c}\mu(j)\) and
\(\varphi(c)^{-1}\sum_{j\mid c}\mu(c/j)\).  Both vanish for \(c>1\);
for \(c=1\) the two lines of (9.121) cancel each other.  Hence every
common frequency (9.122), including \(q=0\), disappears before a
dyadic \(j\)-localization.  This is the exact nonunit analogue of
(9.90a).

The remaining Fourier support satisfies

\[
 1\leq |v|\ll\frac{jE}{M}T^{O(\eta)},
 \qquad jE\gg MT^{-O(\eta)}.
\tag{9.123}
\]

Now \(\delta=e\delta_1\), so the completed \(\delta_1\)-interval has
length \(L/e\).  If \(b\) is the signed least residue

\[
 b\equiv vk\bar r\pmod j,
\tag{9.124}
\]

then repeated summation by parts gives

\[
 |b|\ll\frac{je}{L}T^{O(\eta)},
 \qquad\boxed{br-kv=zj}.
\tag{9.125}
\]

Thus, for \(j\asymp J\), the complete generalized scale ledger is

\[
\boxed{
 |v|\ll\frac{Je}{kM},\quad
 |kv|\ll\widetilde V:=\frac{Je}{M},\quad
 |b|\ll B_e:=\frac{Je}{L},\quad
 |z|\ll Z_e:=\frac{Re}{L},\quad
 |t|\ll\frac Le.}
\tag{9.126}
\]

Indeed, for \(g=(b,z)\), the solutions of (9.125) have steps
\((z/g,b/g)\), so the generic affine interval has length
\((L/e)g\).  The two convolution products again have the identical
ambient length

\[
 X_e=B_eR=Z_eJ=\frac{RJe}{L},
\tag{9.127}
\]

and their difference window has length \(\widetilde V=Je/M\).  Therefore
the general-coefficient Fourier estimate loses exactly \(Je/M\), not an
unspecified gcd factor.  It unconditionally covers the small corner

\[
 Je\leq MT^{O(\eta)}.
\tag{9.128}
\]

Together with the support condition \(Je/k\gg MT^{-O(\eta)}\), this
corner forces \(k\leq T^{O(\eta)}\) and both inequalities to be near
equality.  On the remaining polynomial face, if \(e=T^{\epsilon_e}\),
the separated central-arc diagnostic becomes

\[
 \boxed{
 \beta\leq
 1-\frac{\jmath+\epsilon_e-m}{\rho+\jmath}.}
\tag{9.129}
\]

At \(e=1\), (9.126)--(9.129) reduce to (9.100), (9.109), and
(9.110).  Thus every nonprincipal gcd stratum now has the same exact
self-dual interface.  The polynomial part of (9.129) remains unproved;
the gain here is that neither the dilation \(e/k\), the shortened
progression \(L/e\), nor any common Fourier mode remains hidden in
\(\mathcal W\).

### 9.26 Migration of the Möbius sign to the dilation variable

There is one more exact reindexing which should be made before trying to
estimate the nonunit family.  In a term of (9.113), set

\[
 \boxed{
 E=\frac ek,\qquad \delta'=k\delta_1,\qquad f=kc.}
\tag{9.130}
\]

Because \(d,e,c\) are pairwise coprime and squarefree and \(k\mid e\),
the new factors \(d,E,f\) are pairwise coprime and squarefree.  Moreover

\[
 \boxed{
 s=dEf,\qquad \delta=E\delta',\qquad
 k=(\delta',f),\qquad c=\frac f{(\delta',f)}.}
\tag{9.131}
\]

Indeed, \(\delta'=k\delta_1\), \(f=kc\), and
\((\delta_1,c)=1\), so \((\delta',f)=k\).  Conversely, (9.131)
recovers

\[
 e=kE,\qquad \delta_1=\delta'/k,
\]

and hence (9.130) is a finite bijection, including the endpoint
\(k=e\).  Most importantly, squarefreeness gives the exact sign
migration

\[
 \boxed{\mu(e)\mu(k)=\mu(kE)\mu(k)=\mu(E).}
\tag{9.132}
\]

The dilation and the Ramanujan shift simultaneously simplify:

\[
 \frac ek=E,\qquad k\delta_1=\delta'.
\tag{9.133}
\]

Consequently the full nonprincipal family (9.115) can equivalently be
written, without an absolute value over any of the new factors, in the
finite shape

\[
\boxed{
\begin{aligned}
 \mathfrak N_{\rm all}
 ={}&\sum_{\substack{d,E,f\ {\rm pairwise\ coprime}\\dEf\asymp S}}
 \mu(d)\mu(E)
 \sum_{\substack{r\asymp R,\ \delta'\\E\delta'\asymp L}}
 \mu(r)\,\mathcal W_{d,E,f}(r,\delta')\,E
 \sum_nF_{r,dEf,E\delta'}(En)\\
 &\quad\times
 \left\{
  \mu(c)c_c(n+\delta'\bar r)
  -\frac{c_c(n)}{\varphi(c)}
 \right\},
 \qquad
 c=\frac f{(\delta',f)}.
\end{aligned}}
\tag{9.134}
\]

The bracket vanishes when \(c=1\), so the fully resonant endpoint is
still excluded automatically.  Every Selberg taper, exact gcd condition,
\(q\)-coprimality, dyadic boundary, and dependence on \(f\) remains in
\(\mathcal W_{d,E,f}\).

Formula (9.134) changes the analytic interpretation of the nonunit
problem.  The divisor \(k\) must not be paid for termwise: its Möbius
sign has become a genuine sign \(\mu(E)\) on the dilation, while
\(k=(\delta',f)\) is recovered arithmetically.  After applying
(9.120)--(9.121), the nonunit polynomial family therefore carries at
least the long signs

\[
 \mu(r)\mu(E)\mu(j),
\tag{9.135}
\]

in addition to the gcd sign \(\mu(d)\).  The unit endpoint \(E=d=1\)
still has only \(\mu(r)\mu(j)\), so (9.135) does not by itself close the
balanced unit obstruction.  It does, however, rule out any future proof
which treats the \(k\mid e\) sum as a divisor-bounded absolute
coefficient: that would discard an exact Möbius average which is present
on every nonunit dilation.

### 9.27 The centered fourth-trace route and its exact published boundary

A subsequent paper of Blomer--Pascadi gives a new fourth-moment route for
fixed-modulus bilinear forms in Kloosterman sums.  Since this route is
based on a quadratic character of an \({\rm SL}_2\) trace discriminant,
it is a natural candidate for the centered families above.  Its direct
applicability and the extra bridge required here can both be audited
exactly.

For two intervals of the same length \(N=c^\nu\), their Theorem 1.1 is

\[
 \|\alpha\|\|\beta\|c^{1+o(1)}
 \left(
  \frac{N^{1/8}}{c^{3/32}}
  +\frac{N^{5/16}}{c^{3/16}}
  +\frac{N^{2/3}}{c^{7/18}}
 \right).
\tag{9.136}
\]

The three exponents of \(c\) in (9.136) are

\[
 \frac{29}{32}+\frac\nu8,\qquad
 \frac{13}{16}+\frac{5\nu}{16},\qquad
 \frac{11}{18}+\frac{2\nu}{3}.
\tag{9.137}
\]

Against the better of Weil and complete Cauchy, whose exponent is
\(b(\nu)=\min(1,\nu+1/2)\), the exact margins are therefore

\[
 \boxed{
 \begin{aligned}
 \mathfrak b_1(\nu)&=b(\nu)-\frac{29}{32}-\frac\nu8,\\
 \mathfrak b_2(\nu)&=b(\nu)-\frac{13}{16}-\frac{5\nu}{16},\\
 \mathfrak b_3(\nu)&=b(\nu)-\frac{11}{18}-\frac{2\nu}{3}.
 \end{aligned}}
\tag{9.138}
\]

At the critical length \(\nu=1/2\), these are

\[
 (\mathfrak b_1,\mathfrak b_2,\mathfrak b_3)
 =\left(\frac1{32},\frac1{32},\frac1{18}\right).
\tag{9.139}
\]

The first and third margins vanish at \(13/28\) and \(7/12\),
respectively, reproducing the published nontrivial interval.  On the
full-residue box forced by the direct Fourier bridge (9.15), however,
\(\nu=1\) and

\[
 (\mathfrak b_1,\mathfrak b_2,\mathfrak b_3)
 =\left(-\frac1{32},-\frac18,-\frac5{18}\right).
\tag{9.140}
\]

Thus the new fixed-modulus theorem is strictly nontrivial at square-root
length, but still does not estimate the full Fourier box arising from
(9.13).

There is also a closer published result which averages over the modulus.
Normalize Pascadi's Corollary 7.9 by

\[
 M=N=C^\nu,\qquad q=C^\kappa,\qquad d=C^\tau,
 \qquad 0\leq\tau\leq\kappa\leq1.
\tag{9.141}
\]

When the fixed divisor \(q\) is squarefree, its factorization in that
corollary has \(d'=1\) and square-divisor parameter \(f=d\).  The exact
power margins in the two alternatives inside the published minimum are

\[
 \boxed{
 \begin{aligned}
 \mathfrak p_1(\nu,\kappa,\tau)
  &=-\frac16\max\{\tau+4\nu-3,\ \tau+2\nu-2,\ -\tau\},\\
 \mathfrak p_2(\nu,\kappa,\tau)
  &=-\frac16\max\{\tau+4\nu-\kappa-2,
                    \ \tau+2\nu-\kappa-1,
                    \ \kappa-\tau-1\}.
 \end{aligned}}
\tag{9.142}
\]

Positive means that the parenthetical factor saves a power.  For the
favorable critical choice

\[
 \nu=\frac12,\qquad \kappa=1,\qquad \tau=\frac12,
\]

both margins equal \(1/12\).  But at full residue length \(\nu=1\),

\[
 \boxed{
 \max(\mathfrak p_1,\mathfrak p_2)
 =-\frac{1+\tau}{6}<0
 \qquad(0\leq\tau\leq\kappa\leq1).}
\tag{9.143}
\]

Consequently even the modulus-averaged corollary worsens, rather than
improves, the full-residue Fourier estimate.  It permits coefficients
depending on the modulus only under common pointwise majorants.  The
actual transforms \(\widehat\alpha_s\) and \(\beta_s\) in (9.15) have
good individual Parseval norms, but taking a common pointwise majorant
discards exactly that information.  Hence Corollary 7.9 is not a hidden
averaged bridge for (9.13).

The algebra behind the new fourth-moment method is nevertheless relevant.
Let

\[
 T=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
 S=\begin{pmatrix}0&-1\\1&0\end{pmatrix},
\]

and let \(A_0\) be an integral representative of the inverse of the
Kloosterman multiplier.  For

\[
 g=T^{A_0h_1}ST^{h_2}ST^{A_0h_3}ST^{h_4}S
\]

direct multiplication gives the exact identity

\[
 \boxed{
 \operatorname{Tr}(g)
 =A_0^2h_1h_2h_3h_4
  -A_0(h_1+h_3)(h_2+h_4)+2,\qquad
 \Delta(g)=\operatorname{Tr}(g)^2-4.}
\tag{9.144}
\]

For a prime \(p\), the special representation character used in the
paper is

\[
 \boxed{
 \chi_p^\circ(g)=
 \begin{cases}
 p,&g\equiv\pm I\pmod p,\\
 \left(\dfrac{\Delta(g)}p\right),&g\not\equiv\pm I\pmod p.
 \end{cases}}
\tag{9.145}
\]

Equivalently, \(1+\chi_p^\circ(g)\) is the number of fixed points of
\(g\) on \(\mathbb P^1(\mathbb F_p)\).  This representation-theoretic
identity must not be replaced by a raw inverse-cycle count.  Indeed, for

\[
 p=5,qquad(h_1,h_2,h_3,h_4)=(1,1,1,2),
\]

one has \(\operatorname{Tr}(g)=-2\), \(\Delta(g)=0\), and one projective
fixed point, but the cyclic system

\[
 x_j+\bar x_{j-1}=h_j,\qquad x_j\in\mathbb F_5^\times,
\]

has no solution.  The missing fixed orbit meets \(0\) or the point at
infinity.  Thus the informal phrase ``typically one plus a Legendre
symbol'' cannot serve as a finite identity.  The rigorous route is
(9.145), together with every scalar congruence stratum
\(g\equiv\gamma I\pmod d\), \(\gamma^2=1\), in Proposition 3.4 and the
explicit error family

\[
 h_1h_2h_3=0\quad\hbox{or}\quad h_1+h_3=0
\tag{9.146}
\]

from Proposition 3.6.

This leaves a sharply identified possible adaptation, rather than a
proved estimate.  For separated smooth pieces, (9.15) writes the
relevant family in the coherent form

\[
 \boxed{
 \sum_{s\asymp S}\frac{\mu(s)}s
 \left\langle\widehat\alpha_s,K_s\beta_s\right\rangle,
 \quad
 K_s(m,b)=S(m,-b;s),}
\tag{9.147}
\]

where \(\widehat\alpha_s\) is generated by the same \(\mu(r)\)-weighted
\(r\)-sequence for every \(s\), and \(\beta_s(b)\) is generated by the
same factorized \((h,\delta)\)-sequence through
\(h\delta\equiv b\pmod s\).  Applying a spectral norm separately for
each \(s\) destroys this coherence and the outer \(\mu(s)\) average.
Taking Cauchy before separating moduli instead creates cross-modulus
fourth cycles, while (9.145) is presently a single-modulus character
identity.

The precise missing lemma for this route is therefore a **coherent
cross-modulus fourth-trace estimate** which:

1. converts those mixed cycles to a common quadratic-character family;
2. retains the scalar-divisor strata and the degenerates in (9.146);
3. bounds the common discriminant multiplicity energy with the strength
   required by the \(RS\) target; and
4. keeps both outer Möbius weights and the factorization \(h\delta\)
   before any absolute value over the Type-II fixed factor.

No such published lemma was found, and it is not proved here.  The latest
averaged-Chowla improvement of Menon does not substitute for it: its
saving is
\(O(\log\log H/\log H+(\log\log X)^2/\log X)\), and the paper itself
identifies \(1/\log H\) as the effective ceiling of that method.  Such a
logarithmic gain cannot absorb any of the positive power deficits in
(9.85), (9.100), or (9.143).

All finite statements in (9.138), (9.142), and (9.144)--(9.146) are
checked by
`scripts/audit_mobius_type_ii.py` and
`scripts/audit_centered_fourth_trace.py`, including exhaustive small-box
matrix/projective tests.  These checks validate the reduction boundary;
they do not prove the coherent cross-modulus estimate or
CK\(_{\rm ub}(3)\).

### 9.28 Fixed-numerator spacing and the arbitrary-operator barrier

The coherent family (9.147) has more spacing than a generic Farey family
when the same \(r\) is retained.  Let

\[
 u\equiv\bar r\pmod s,\quad 0\leq u<s,
 \qquad
 v\equiv\bar r\pmod t,\quad 0\leq v<t,
\]

with \((r,st)=1\).  Choose the signed least residue \(k\) of
\(ut-vs\pmod{st}\).  Then there is an integer \(\ell\) such that

\[
 \boxed{
 \left\|\frac us-\frac vt\right\|_{\mathbb R/\mathbb Z}
   =\frac{|k|}{st},
 \qquad
 rk-(t-s)=\ell st.}
\tag{9.148}
\]

The congruence is immediate from

\[
 ru=1+p s,qquad rv=1+q t,
\]

since

\[
 r(ut-vs)=t-s+(p-q)st.
\]

It has a useful dyadic consequence.  Suppose

\[
 Y<r,s,t\leq2Y,qquad s\neq t,qquad Y\geq2.
\tag{9.149}
\]

If \(\ell=0\) in (9.148), then
\(|rk|=|t-s|<Y<r\), forcing \(k=0\) and then \(s=t\), a
contradiction.  Hence \(\ell\neq0\), and

\[
 |rk|\geq st-|t-s|>Y^2-Y.
\]

Using \(r\leq2Y\) and \(st\leq4Y^2\) gives the completely elementary
spacing bound

\[
 \boxed{
 \left\|\frac{\bar r_s}{s}-\frac{\bar r_t}{t}\right\|_{\mathbb R/\mathbb Z}
 \geq\frac1{16Y}.}
\tag{9.150}
\]

Thus, for fixed \(r\) in the balanced box, distinct denominator phases
are separated on the inverse-linear scale \(Y^{-1}\), not the generic
Farey scale \(Y^{-2}\).  Equivalently, the potentially closest Farey
collisions cannot occur inside a single balanced fixed-numerator slice.
The proof is finite, includes composite and non-coprime pairs \((s,t)\),
and requires only that \(r\) be a unit modulo both.

This observation does not by itself close the sum, because using a large
sieve on each fixed-\(r\) slice and then applying Cauchy over \(r\)
still discards the two Möbius interaction.  The exact loss is easiest to
see at the operator level.  Collapse the product variables temporarily
to

\[
 \nu(a)=\sum_{h\delta=a}w(h,\delta)
\]

and define the coherent matrix

\[
 \mathcal L(r,a)
 =\sum_{s\asymp S}\mu(s)W(r,s,a)
   e\left(-\frac{a\bar r}{s}\right).
\tag{9.151}
\]

Then the separated model is \(\langle\mu,\mathcal L\nu\rangle\), with
input norm exponents \(\rho/2\) and \(a/2\).  An arbitrary-coefficient
operator estimate reaching the \(RS\) target would therefore require

\[
 \boxed{
 \kappa_{\rm req}
 =\rho+\sigma-\frac{\rho+a}{2}
 =\frac{\rho+2\sigma-a}{2}.}
\tag{9.152}
\]

Factoring \(\mathcal L\) through the \((r,s)\) Farey rows and applying
the better of the two reciprocal large-sieve orientations gives exactly
the already proved \(RS\sqrt A\) bound.  After removing the two input
norms, its operator exponent is

\[
 \boxed{
 \kappa_{\rm LS}=\frac\rho2+\sigma,
 \qquad
 \kappa_{\rm LS}-\kappa_{\rm req}=\frac a2.}
\tag{9.153}
\]

At the balanced maximal point this reads

\[
 \kappa_{\rm req}=2,qquad
 \kappa_{\rm LS}=\frac92,qquad
 \kappa_{\rm LS}-\kappa_{\rm req}=\frac52.
\tag{9.154}
\]

Therefore an arbitrary-\(\nu(a)\) coherent spectral-norm theorem is still
too strong by \(T^{5/2}\).  The fixed-numerator spacing (9.150) is real,
but a successful mixed-modulus fourth moment must use it while retaining
the factorization \(a=h\delta\) and both Möbius weights.  In particular,
the candidate lemma after (9.147) cannot be weakened to a generic
operator bound for arbitrary product coefficients.

The congruence certificate (9.148), the dyadic margin in (9.150), and the
exponent ledger (9.152)--(9.154) are checked exactly in
`scripts/audit_mobius_type_ii.py`; the tests exhaust all admissible
triples in the small dyadic boxes \(2\leq Y\leq20\).

### 9.29 Cross-numerator collisions, Farey counting, and the surviving signed gate

The fixed-\(r\) spacing argument cannot be used after a Cauchy expansion,
where the two numerators are generally different.  There is nevertheless
an exact integral replacement.  Put

\[
 u\equiv\bar r\pmod s,\qquad
 v\equiv\overline{r'}\pmod t,
\]

and let \(k\) be the signed least residue of \(ut-vs\) modulo \(st\),
choosing the positive representative in the tie \(k=st/2\).
Then a unique integer \(\ell\) satisfies

\[
 \boxed{rr'k-(r't-rs)=\ell st.}
\tag{9.155}
\]

Indeed, if \(ru=1+ps\) and \(r'v=1+qt\), multiplication by \(r't\)
and \(rs\), respectively, gives (9.155).  More importantly, the same
identity factors without a remainder:

\[
 \boxed{(rk-t)(r'+\ell s)=rs(k\ell-1).}
\tag{9.156}
\]

No cross-coprimality such as \((rr',st)=1\) was inserted.  Thus (9.156)
is a necessary divisor-switching equation for the original family, not
an unjustified equivalence.  Its \(k\ell=1\) strata are genuine: the only
integer possibilities are \((k,\ell)=(1,1)\) and \((-1,-1)\), which force
\(t=r\) and \(r'=s\), respectively.  The tuples
\((r,s,r',t)=(5,7,3,5)\) and \((5,7,7,2)\) realize the two signs.

If

\[
 R<r,r'\leq2R,\qquad S<s,t\leq2S,
 \qquad \left\|\frac us-\frac vt\right\|\leq A^{-1},
\]

then (9.155) gives the fully elementary bounds

\[
 \boxed{
 |k|\leq\frac{4S^2}{A},\qquad
 |\ell|\leq\frac{4R^2}{A}+\frac{4R}{S}.}
\tag{9.157}
\]

At \((R,S,A)=(T^3,T^3,T^5)\), both new integers have length \(T\).
Away from \(k\ell=1\), summing \(r,s,k,\ell\) and using (9.156) only
through a divisor bound would cost \(T^{8+\varepsilon}\), one power above
the natural collision volume \(T^{7+\varepsilon}\).  The omitted
factor-degenerate strata are smaller and must be counted separately.
For \((k,\ell)=(1,1)\), one has \(t=r\), and reducing the original
inverse equation modulo \(r\) gives \(r'\equiv-s\pmod r\); hence there is
at most one \(r'\) in the balanced dyadic interval for each \(r,s\).
For \((k,\ell)=(-1,-1)\), one similarly has \(r'=s\) and
\(t\equiv-r\pmod s\).  Together these diagonals contain at most \(2RS\)
tuples, namely \(T^{6+o(1)}\) in the balanced box.  Thus the
nondegenerate \(T^8\) ledger is complete after adjoining a strictly
smaller \(T^6\) exceptional ledger.  The remaining one-power loss is
avoidable before the Möbius weights are considered.

Namely, \(u/s\) and \(v/t\) are reduced fractions.  For their unreduced
determinant \(j=ut-vs\), one has

\[
 (j,s)=(j,t)=(s,t).
\tag{9.158}
\]

When \(s,t\) are squarefree, write \(d=(s,t)\).  Then the exact reduced
denominator in \(\mathbb R/\mathbb Z\) is

\[
 \boxed{
 \frac{st}{(j,st)}
 =\frac{\operatorname{lcm}(s,t)}{(j/d,d)}.}
\tag{9.159}
\]

There is also a direct finite collision bound.  Let \(\mathcal N(S,K)\)
count ordered reduced fractions with denominators in \((S,2S]\) whose
signed circular determinant has absolute value at most \(K\).  For a
fixed nonzero signed determinant \(k\), the ordinary determinant is one
of \(k-st,k,k+st\).  Fixing \(s,t\), the congruence \(ut\equiv k\pmod s\)
has at most \((s,t)\) solutions.  Grouping by \(d=(s,t)\mid k\) therefore
gives the explicit finite majorant

\[
 \boxed{
 \mathcal N(S,K)
 \leq 2S^2+24S^2\sum_{1\leq k\leq K}\tau(k)
 \ll_\varepsilon S^2(1+K)T^\varepsilon.}
\tag{9.160}
\]

Here the last notation assumes \(S,K\leq T^{O(1)}\); the first inequality
is the unconditional finite statement.

The four signs also admit an exact finite change of coordinates.  Define

\[
 \mathcal M_R(u;s)=
 \sum_{\substack{R<r\leq2R\\ru\equiv1\pmod s}}\mu(r),
\tag{9.160a}
\]

and write \(k(u,s;v,t)\) for the signed circular determinant used in
(9.160).  Then, with no estimate or discarded boundary term,

\[
\boxed{
\begin{aligned}
 &\sum_{\substack{R<r,r'\leq2R\\S<s,t\leq2S\\
                  (r,s)=(r',t)=1}}
 \mu(r)\mu(s)\mu(r')\mu(t)\,
 {\bf1}_{|k(\bar r_s,s;\overline{r'}_t,t)|\leq K}\\
 &\qquad =
 \sum_{\substack{S<s,t\leq2S\\
                  u\bmod s,\ (u,s)=1\\
                  v\bmod t,\ (v,t)=1}}
 \mu(s)\mu(t)\mathcal M_R(u;s)\mathcal M_R(v;t)\,
 {\bf1}_{|k(u,s;v,t)|\leq K}.
\end{aligned}}
\tag{9.160b}
\]

In the balanced interval \(\mathcal M_R(u;s)\in\{0,\pm1\}\), since an
interval of length \(R\) contains at most one integer in a residue class
modulo \(s>R\).  Thus (9.160b), unlike the unsigned bound (9.160), retains
all four Möbius weights.  It is the directly formalizable signed-Farey
interface on which a genuine Type I/II or dispersion argument would have
to act.

Each reduced fraction \(u/s\) has at most \(1+R/s\) inverse lifts
\(r\asymp R\).  In the balanced dyadic interval the lift is unique,
because its length is \(S<s\).  Taking \(K\asymp S^2/A=T\) in (9.160)
proves the unsigned central-collision bound \(T^{7+\varepsilon}\).
Thus the extra \(T\) in the raw \((r,s,k,\ell)\) divisor ledger is not a
real obstruction.  This is a counting theorem only: taking absolute
values in (9.160) erases all four weights
\(\mu(r)\mu(s)\mu(r')\mu(t)\), so it supplies none of the power
cancellation required by the coupled kernel.

Nor may the full product kernel be replaced by its central arc.  With

\[
 \mathcal K_{H,L}(x)=\sum_{h\leq H}\sum_{\delta\leq L}e(h\delta x)
 =\sum_a\tau_{H,L}(a)e(ax),
\tag{9.161}
\]

one has the exact noncentral resonance

\[
 \boxed{\mathcal K_{q,q}(1/q)=q,}
\tag{9.162}
\]

although \(1/q>1/q^2=(HL)^{-1}\).  Formula (9.159) identifies the exact
denominator of every such rational stratum, but approximate rational
arcs still have to be estimated; central Farey counting alone is not a
majorant for (9.161).

For completeness, there is an exact two-dimensional additive completion
which removes the inverse but displays why termwise treatment stops.
Write

\[
 \widehat{1_H}(a;s)=\sum_{h\leq H}e_s(-ah),\qquad
 \widehat{1_L}(b;s)=\sum_{\delta\leq L}e_s(-b\delta).
\]

Finite Fourier inversion and the complete identity

\[
 \sum_{x,y\bmod s}e_s(ax+by-\bar rxy)=s\,e_s(rab)
\]

give

\[
 \boxed{
 \sum_{h\leq H}\sum_{\delta\leq L}e_s(-\bar r h\delta)
 =\frac1s\sum_{a,b\bmod s}
 \widehat{1_H}(a;s)\widehat{1_L}(b;s)e_s(rab).}
\tag{9.163}
\]

The \(a=b=0\) term is exactly \(HL/s\).  If it is bounded separately
and both dyadic Möbius sums are assigned a common exponent \(\beta\), the
balanced maximal box requires

\[
 a-\sigma+\beta(\rho+\sigma)\leq\rho+\sigma,
 \qquad\text{hence}\qquad \beta\leq\frac23.
\tag{9.164}
\]

Classical zero-free technology does not provide this power bound.
Equation (9.164) is a barrier for separating the additive zero mode, not
a lower bound for the complete expression: cancellation between dual
modes and gcd strata remains possible and must be retained.

The published results located in this audit do not supply that
cancellation.  Farey pair-correlation theorems concern unsigned reduced
fractions and are consistent with (9.160).  Humphries studies the
two-dimensional inverse graph for one fixed modulus; Bourgain--Garaev's
multilinear reciprocal-set estimates work in one fixed residue ring;
and Shkredov's modular-hyperbola incidence bounds are over one fixed
prime field.  None averages the varying squarefree \(s,t\) family while
retaining \(\mu(r)\mu(s)\mu(r')\mu(t)\) and the product kernel.  Moreover,
Garaev--Shparlinski exhibit moduli and short intervals for which a
one-variable inverse exponential sum is as large as \(N^{1-\gamma}\),
so a uniform one-variable power saving cannot simply be assumed.

The remaining analytic statement is therefore narrower than the former
arbitrary-operator gate but still unproved: a **signed cross-modulus
product-kernel estimate** must combine (9.156), (9.159), and (9.163)
before taking absolute values over either Möbius pair or over the dual
zero/nonzero modes.  The checker verifies the integral identities and
finite bounds (9.155)--(9.160b) exactly on the stated small boxes,
including the two degenerate diagonals and the improved constant in
(9.157).  It checks the root-of-unity evaluations (9.161)--(9.163)
numerically to explicit tolerances; their exact status comes from the
displayed finite Fourier derivation, not from floating-point computation.
None of these checks proves the signed estimate or CK\(_{\rm ub}(3)\).

### 9.30 Exact shifted-Chowla coordinates after additive completion

There is one further cancellation hidden by the last paragraph of
Section 9.29.  It does not prove the coupled-kernel estimate, but it removes
the isolated additive origin as a logically necessary sub-gate.  Let

\[
 d=r-s.
\]

Because the outer sum already has \((r,s)=1\), this substitution has the
exact consequences

\[
 (d,s)=1,\qquad \bar r_s=\bar d_s,
 \qquad e_s(rab)=e_s(dab).
\tag{9.165}
\]

In particular, for an arbitrary finite coefficient \(W(r,s)\), (9.163)
gives the boundary-exact identity

\[
\boxed{
\begin{aligned}
 &\sum_{S<s\leq2S}\sum_{\substack{R<r\leq2R\\(r,s)=1}}
 \mu(r)\mu(s)W(r,s)
 \sum_{h\leq H}\sum_{\delta\leq L}e_s(-\bar r_s h\delta)\\
 &=\sum_{S<s\leq2S}
 \sum_{\substack{R-s<d\leq2R-s\\(d,s)=1}}
 \mu(s+d)\mu(s)W(s+d,s)\frac1s
 \sum_{a,b\bmod s}
 \widehat{1_H}(a;s)\widehat{1_L}(b;s)e_s(dab).
\end{aligned}}
\tag{9.166}
\]

Thus there is no replacement of the moving endpoint by \(|d|\leq R\),
and no discarded \(d=0\) term.  The displayed inequalities
\(R-s<d\leq2R-s\) are the complete boundary terms.  In the ranges used
here \(s>1\), so \((d,s)=1\) already excludes \(d=0\).

The additive origin must not be separated from its axes.  Orthogonality
gives the exact finite formulas

\[
 \sum_{b\bmod s}\widehat{1_L}(b;s)
 =s\left\lfloor\frac Ls\right\rfloor,
 \qquad
 \sum_{a\bmod s}\widehat{1_H}(a;s)
 =s\left\lfloor\frac Hs\right\rfloor.
\tag{9.167}
\]

Consequently the complete row \(a=0\), including the factor \(1/s\),
is \(H\lfloor L/s\rfloor\), the complete column \(b=0\) is
\(L\lfloor H/s\rfloor\), and their union is

\[
\boxed{
 H\left\lfloor\frac Ls\right\rfloor
 +L\left\lfloor\frac Hs\right\rfloor-\frac{HL}{s}.}
\tag{9.168}
\]

On the balanced maximal box \(H,L<s\).  Each complete axis therefore
vanishes exactly, while their union equals \(-HL/s\).  Equivalently, the
positive origin \(HL/s\) cancels against the nonzero points on either
complete axis.  One may delete one complete zero axis, but not both axes:
their common origin would then be subtracted twice.  Hence the exponent
\(2/3\) in (9.164) is only the cost of an invalidly premature pointwise
separation.  It is not a remaining standalone Mertens hypothesis.  The
off-axis frequencies and one axis must still be estimated jointly.

For a nonzero residue let \(a^*\in(-s/2,s/2]\) be its centered
representative.  The sharp interval transform satisfies

\[
 \left|\widehat{1_H}(a;s)\right|
 \leq\min\left(H,\frac{s}{2|a^*|}\right),
 \qquad a\ne0,
\tag{9.169}
\]

and likewise for \(L\).  Dyadically partitioning the centered residues is
an exact partition of the finite sum; (9.169), however, does **not** make
the complementary sharp-frequency blocks power-negligible.  The lowest
nonzero transition block has

\[
 A_0=\frac{s}{H},\qquad B_0=\frac{s}{L},\qquad C_0=A_0B_0.
\tag{9.170}
\]

At

\[
 S=R=T^3,\qquad H=L=T^{5/2},
\]

these are \(A_0=B_0=T^{1/2}\) and \(C_0=T\).  In (9.166) the phase in
this block changes by order one at the circular shift scale

\[
 D_0=\frac{S}{C_0}=T^2=X^{2/3},\qquad X:=T^3.
\tag{9.171}
\]

The exact exponent ledger for this block is

\[
 \underbrace{T^2}_{HL/S}
 \underbrace{T}_{A_0B_0}
 \underbrace{T^3}_{s}
 \underbrace{T^2}_{|d|\ \mathrm{near}}
 =T^8.
\tag{9.172}
\]

The normalized local target is \(RS=T^6\), so this lowest dual block
requires a genuine \(T^2=X^{2/3}\) saving.  Formula (9.172) is a trivial
upper ledger, not a lower bound.  It also does not claim that the sharp
completion is supported only on (9.170); every complementary dyadic block
and both circular boundary arcs remain in the exact partition.

The complementary **near** blocks can also be classified without a
conjectural estimate.  Write \(|a^*|\asymp T^\alpha\),
\(|b^*|\asymp T^\beta\), and put

\[
 U_H(\alpha)=\min(h,\sigma-\alpha),\qquad
 U_L(\beta)=\min(\ell,\sigma-\beta).
\]

The sharp Fourier bound and the circular window
\(D=S/(AB)\) give the exact exponent ledger

\[
\boxed{
 E_{\rm near}(\alpha,\beta)
 =U_H(\alpha)+U_L(\beta)+\alpha+\beta
  +\max(0,\sigma-\alpha-\beta).}
\tag{9.173}
\]

For the balanced maximal box \(h=\ell=5/2\), \(\sigma=3\).  If
\(\alpha+\beta\leq3\), then

\[
 E_{\rm near}=U_H(\alpha)+U_L(\beta)+3\leq8;
\]

if \(\alpha+\beta\geq3\), then

\[
 E_{\rm near}
 =(U_H(\alpha)+\alpha)+(U_L(\beta)+\beta)\leq6.
\tag{9.174}
\]

Thus no nonzero near block has a larger deficit than the \(T^2\) deficit
in (9.172), and every block with \(AB\geq S\) reaches the local target by
the trivial near-window count.  This closes the near-block exponent
polytope; it does not estimate the far arcs.

There is an exact one-modulus Parseval identity on those remaining blocks:

\[
 \sum_{d\bmod s}\left|
  \frac1s\sum_{a\in\mathcal A}\sum_{b\in\mathcal B}
  x_a y_b e_s(dab)\right|^2
 =\frac1s\sum_{c\bmod s}\left|
  \sum_{\substack{a\in\mathcal A,b\in\mathcal B\\ab\equiv c\pmod s}}
  x_a y_b\right|^2.
\tag{9.175}
\]

When \(AB=o(s)\), centered-product congruences have only \(O(1)\)
possible lifts to integer equalities; divisor energy bounds the right side
up to \(T^\varepsilon\).  Still on the face \(R=S\), Cauchy in \(d\),
followed by absolute summation over \(s\), then has exponent

\[
 E_{L^2}=\sigma+U_H(\alpha)+U_L(\beta)
             +\frac{\alpha+\beta}{2}.
\tag{9.176}
\]

At \((\alpha,\beta)=(1/2,1/2)\), this is \(17/2\), still
\(5/2\) above the target \(6\).  For \(AB\geq s\), even the simple
integer-divisor reduction of (9.175) is unavailable because modular
hyperbola multiplicities enter.  Hence one-modulus Parseval does not
handle the far complement: a cross-modulus or two-Möbius step is still
mathematically necessary.

The rational-resonance strata in the no-wrap blocks are equally explicit.
Since \((d,s)=1\), put \(g=(ab,s)\).  Then

\[
\boxed{
 \frac{dab}{s}
 =\frac{d(ab/g)}{s/g},\qquad
 \left(d\frac{ab}{g},\frac{s}{g}\right)=1,
 \qquad q_{\rm red}=\frac{s}{(ab,s)}.}
\tag{9.177}
\]

If \(0<|ab|<s\), this gives only the finite lower bound
\(q_{\rm red}\geq s/|ab|\).  It does **not** exclude transition-block
resonance.  For example,

\[
 s=62,\quad d=-1,\quad a=b=2,\quad H=L=31
\]

has \((d,s)=1\), \(|ab|<s\), \(s/H=s/L=2\), but

\[
 q_{\rm red}=31,\qquad
 \mathcal K_{31,31}(-4/62)=\mathcal K_{31,31}(-2/31)=31.
\]

Thus the scalar gcd \((ab,s)\) creates genuine rational strata even in a
no-wrap transition block.  Formula (9.177) parameterizes those strata; it
does not remove them.  The near part of blocks with \(AB\geq S\) is
covered by (9.174), but the far arcs and all resonant scalar-gcd strata
still require a gcd-stratified modular-hyperbola estimate.

There is an exact way to retain the axis cancellation when desired.  For
\(L<s\), summing the whole \(b\)-coordinate first gives

\[
 \frac1s\sum_{b\bmod s}\widehat{1_L}(b;s)e_s(dab)
 =\mathbf 1_{\{1,\ldots,L\}}([da]_s),
\]

and hence

\[
\boxed{
 \frac1s\sum_{a,b\bmod s}
 \widehat{1_H}(a;s)\widehat{1_L}(b;s)e_s(dab)
 =\sum_{a\bmod s}\widehat{1_H}(a;s)
  \mathbf 1_{\{1,\ldots,L\}}([da]_s).}
\tag{9.178}
\]

The \(a=0\) term on the right is zero, so (9.178) includes all origin/axis
boundary terms with no remainder.  It is useful for checking a proposed
axis treatment, but summing out \(b\) also discards the product
factorization needed by the intended Type-I/II route; it is not itself an
estimate.

Because the outer factor \(\mu(s)\) restricts to squarefree \(s\), the
scalar gcd in (9.177) has a canonical ordered factorization.  Put

\[
 g_a=(a,s),\qquad g_b=\left(b,\frac{s}{g_a}\right),
 \qquad q=\frac{s}{g_ag_b},\qquad
 a'=\frac a{g_a},\quad b'=\frac b{g_b}.
\]

Then \(g_a,g_b,q\) are pairwise coprime and

\[
\boxed{
 (ab,s)=g_ag_b,\qquad
 \frac{dab}{s}=\frac{da'b'}q,\qquad
 (a'b',q)=1,\qquad
 \mu(s)=\mu(g_a)\mu(g_b)\mu(q).}
\tag{9.179}
\]

This is a genuine Type-I/II coordinate system for the resonant strata,
not merely a denominator label.  For the family
\(s=gq\), \(a=b=g\), \((g,q)=1\), it gives
\(g_a=g\), \(g_b=1\), \(a'=1\), \(b'=g\), so the transition resonance
has a short scalar factor \(g\asymp T^{1/2}\) and a long reduced modulus
\(q\asymp T^{5/2}\).  The remaining estimate must average
\(\mu(s+d)\mu(g_a)\mu(g_b)\mu(q)e_q(da'b')\) with the transformed
Fourier weights and moving \(d\)-endpoints.  Neither the one-modulus
Parseval bound nor the cited fixed-ring estimates perform this joint
average.

This identifies a precise published-theorem mismatch.  Even before the
additional \(e_s(dab)\) weight is addressed, the averaged Chowla theorem
of Matomäki--Radziwiłł--Tao supplies decay only of rough size
\(\log\log D/\log D\), not the \(X^{2/3}\) power demanded by (9.172).
Tao--Teräväinen's unweighted two-point conclusion is for almost all outer
scales and is qualitative, so it cannot give a uniform bound for every
\(T\).  Guo's August 2026 result has a fixed power-of-log saving only for the
**logarithmically weighted** two-point correlation and shifts in a fixed
polylogarithmic range; its statement explicitly does not prove ordinary
Cesàro two-point Chowla, and its shift range does not reach
\(D=X^{2/3}\).  Lichtman's theorem concerns Möbius on shifted primes, not
the binary weight \(\mu(s)\mu(s+d)\).

Accordingly, the finite sum in (9.166), with (9.167)--(9.179) retained
before absolute values, is an exact interface for the remaining joint
estimate.  Its nonzero dyadic blocks split into circular near arcs
\(\|d/s\|\leq C^{-1}\) and complementary scalar-gcd strata while retaining
both Möbius weights and the factorization \(ab\).  Taking absolute values
over \(d\), or replacing the \(ab\)-coefficients by arbitrary coefficients,
returns the previous large-sieve loss.  Before attempting an estimate,
Section 9.31 performs one more exact completion of each scalar stratum.

### 9.31 Complete unit spectrum on each scalar-gcd stratum

The ordered splitting (9.179) can be completed further without applying
Cauchy.  Two finite lift identities account for the different exact-gcd
conditions.  If \((g,q)=1\) and \(u\in(\mathbb Z/q\mathbb Z)^\times\),
then

\[
\boxed{
 \sum_{\substack{x\bmod gq\\x\equiv u\pmod q\\(x,gq)=1}}
 \widehat{1_H}(x;gq)
 =\sum_{h\leq H}c_g(h)e_q(-\bar g_q u h).}
\tag{9.180}
\]

For an unrestricted lift one instead has

\[
\boxed{
 \sum_{\substack{y\bmod gq\\y\equiv v\pmod q}}
 \widehat{1_L}(y;gq)
 =g\,\widehat{1_{\lfloor L/g\rfloor}}(v;q).}
\tag{9.181}
\]

Both follow by inserting the finite interval transform and using
orthogonality over the lift variable.  The unit restriction in (9.180)
produces the Ramanujan sum; no endpoint is lost in (9.181), whose last
interval has the exact floor \(\lfloor L/g\rfloor\).

Define the complete double-unit bilinear sum

\[
 U_q(A,B;d)=
 \sum_{u,v\in(\mathbb Z/q\mathbb Z)^\times}
 e_q(duv-Au-Bv),\qquad (d,q)=1.
\]

For a prime \(p\), summing first over \(v\) gives the exact local identity

\[
 U_p(A,B;d)
 =p\,\mathbf 1_{p\nmid B}e_p(-AB\bar d_p)-c_p(A).
\tag{9.182}
\]

The indicator is essential: if \(p\mid B\), the stationary residue
\(u=B\bar d_p\) is not a unit.  Chinese remaindering (9.182) over
squarefree \(q\) gives

\[
\boxed{
 U_q(A,B;d)=
 \sum_{\substack{k\mid q\\(k,B)=1}}
 k\mu(q/k)c_{q/k}(A)
 e_k\!\left(-AB\,\overline{d(q/k)}_k\right).}
\tag{9.183}
\]

The phase for \(k=1\) is one.  Multiplication by the outer Möbius sign
now performs an exact sign migration:

\[
\boxed{
 \mu(q)U_q(A,B;d)=
 \sum_{\substack{k\mid q\\(k,B)=1}}
 k\mu(k)c_{q/k}(A)
 e_k\!\left(-AB\,\overline{d(q/k)}_k\right),}
\tag{9.184}
\]

because \(q\) is squarefree.  Thus every proper divisor layer carries
\(\mu(k)\), not a separately estimated \(\mu(q)\).

Combining (9.180)--(9.184) yields a closed finite formula for one ordered
stratum.  Put \(s=g_ag_bq\), with the factors in (9.179), and define

\[
 \mathcal F_{g_a,g_b,q}(d)
 :=\frac{\mu(s)}s
 \sum_{\substack{a,b\bmod s\\(a,s)=g_a\\
                  (b,s/g_a)=g_b}}
 \widehat{1_H}(a;s)\widehat{1_L}(b;s)e_s(dab).
\]

For \(q>1\), so that this is off the coordinate axes, one has

\[
\boxed{
\begin{aligned}
 \mathcal F_{g_a,g_b,q}(d)
 &=\frac{\mu(g_a)\mu(g_b)}{g_bq}
 \sum_{h\leq H}c_{g_b}(h)
 \sum_{\delta'\leq L/g_a}
 \sum_{\substack{k\mid q\\(k,\delta')=1}}
 k\mu(k)c_{q/k}(h)\\
 &\qquad\qquad\times
 e_k\!\left(
  -\bar g_{b,k}h\delta'\,
   \overline{d(q/k)}_k\right).
\end{aligned}}
\tag{9.185}
\]

Here \(L/g_a\) in the summation means the exact integer endpoint
\(\lfloor L/g_a\rfloor\), and every inverse is taken only after the
displayed coprimality conditions make it legal.  The checker numerically
verifies (9.180)--(9.185) on deterministic small squarefree factors,
including composite \(q=6\), intermediate divisor layers, negative
frequencies, and the indicator \((k,\delta')=1\).  Exactness is supplied
by the displayed finite algebra, rather than inferred from those samples.

Formula (9.185) materially narrows the far-arc gate.  All proper layers
\(k<q\) have the migrated sign \(\mu(k)\) and an explicit Ramanujan
cofactor.  The top layer \(k=q\), however, is

\[
 \frac{\mu(g_a)\mu(g_b)\mu(q)}{g_b}
 \sum_{h\leq H}c_{g_b}(h)
 \sum_{\substack{\delta'\leq L/g_a\\(\delta',q)=1}}
 e_q(-\bar g_b h\delta'\bar d_q),
\tag{9.186}
\]

and remains an inverse-product kernel coupled to
\(\mu(g_ag_bq+d)\).  On the transition resonance
\(g_a\asymp T^{1/2}\), \(g_b=1\), \(q\asymp T^{5/2}\), it has lengths
\(H=T^{5/2}\) and \(L/g_a=T^2\).  No cited theorem handles this kernel
with the simultaneous \(g_a,q,d\) dependence and shifted Möbius factor.
Thus (9.185) proves that the proper divisor spectrum is structurally
simpler, while (9.186) is the exact surviving top-spectrum gate; neither
is declared bounded here.

### 9.32 Coprimality migration and the first theorem-compatible Type-II form

The condition \((k,\delta')=1\) in (9.185) can be expanded before any
absolute value.  This does more than remove a side condition: it moves
the Möbius sign to the modulus which actually carries the inverse phase.
Insert

\[
 \mathbf 1_{(k,\delta')=1}
 =\sum_{j\mid(k,\delta')}\mu(j),
\]

and write

\[
 k=j\lambda,\qquad q=j\lambda n,qquad
 \delta'=j\delta_0.
\]

All three factors are pairwise coprime because \(q\) is squarefree.  The
coefficient in (9.185) then satisfies the exact sign identity

\[
 \frac1q\,k\mu(k)\mu(j)
 =\frac{\mu(\lambda)}n,
\]

and reduction of the phase from modulus \(j\lambda\) to \(\lambda\)
gives

\[
 e_{j\lambda}\!\left(
 -\bar g_bh(j\delta_0)\overline{dn}_{j\lambda}
 \right)
 =e_\lambda\!\left(
 -\bar g_bh\delta_0\overline{dn}_\lambda
 \right).
\]

Finally, multiplicativity of Ramanujan sums, using \((g_b,n)=1\), gives
\(c_{g_b}(h)c_n(h)=c_{g_bn}(h)\).  Consequently (9.185) is exactly

\[
\boxed{
\begin{aligned}
 \mathcal F_{g_a,g_b,q}(d)
 ={}&\mu(g_a)\mu(g_b)
 \sum_{j\lambda n=q}\frac{\mu(\lambda)}{g_bn}
 \sum_{h\leq H}c_{g_bn}(h)\\
 &\times\sum_{\delta_0\leq L/(g_aj)}
 e_\lambda\!\left(
 -\bar g_{b,\lambda}h\delta_0
  \overline{dn}_\lambda\right).
\end{aligned}}
\tag{9.187}
\]

The endpoint in (9.187) is
\(\lfloor L/(g_aj)\rfloor\), the phase at \(\lambda=1\) is one, and no
coprimality condition on \(\delta_0\) remains.  The finite checker compares
(9.187) with (9.185) for prime and composite squarefree \(q\), including
negative phases and every ordered factorization \(j\lambda n=q\).

Formula (9.187) is the first scalar-stratum form for which a published
Kloosterman-fraction theorem is syntactically applicable without replacing
a modulus-dependent coefficient by a common majorant.  Indeed, return to
\(r=s+d\).  Since \(\lambda\mid s\), one has \(d\equiv r\pmod\lambda\),
and the phase is

\[
 e_\lambda\!\left(
 -h\delta_0\overline{r g_bn}_\lambda\right).
\tag{9.188}
\]

After fixing \(g_a,g_b,j,n\), the coefficient of the product
\(h\delta_0\) is independent of the varying inverse modulus \(\lambda\).
The inverted variable is the sparse sequence
\(m=r g_bn\asymp Rg_bn\), and its \(L^2\)-norm still has size
\(R^{1/2}T^\varepsilon\).  Thus Bettin--Chandee Theorem 1 can be inserted
with

\[
 M=Rg_bn,\qquad N=\lambda,\qquad
 A=\frac{HL}{g_aj},
\tag{9.189}
\]

but the Ramanujan weight in that product coefficient must be retained.  For
squarefree \(m=g_bn\), one period has the exact moments

\[
 \sum_{h\bmod m}|c_m(h)|=2^{\omega(m)}\varphi(m),
 \qquad
 \sum_{h\bmod m}|c_m(h)|^2=m\varphi(m).
\tag{9.189a}
\]

More generally, divisor expansion gives

\[
 \sum_{h\leq H}|c_m(h)|^2
 \ll_\varepsilon m(H+m)T^\varepsilon.
\tag{9.189b}
\]

Thus the product-coefficient norm has exponent

\[
 \frac{p}{2}
 +\frac{\gamma_b+\eta+
  \max(h,\gamma_b+\eta)-h}{2}.
\tag{9.189c}
\]

On the transition strata \(m\leq H T^{O(\eta)}\), this is
\(A^{1/2}m^{1/2}T^\varepsilon\), not merely
\(A^{1/2}T^\varepsilon\); when \(m>H\), (9.189c) is larger.  This is an
applicability statement, not yet a sufficient estimate.

The exact exponent ledger shows where the theorem stops.  Write the
exponents of \(g_a,g_b,j,n,\lambda\) as
\(\gamma_a,\gamma_b,\iota,\eta,\lambda_0\), so their sum is \(\sigma\),
and put

\[
 p=h+\ell-\gamma_a-\iota,qquad
 m_0=\rho+\gamma_b+\eta.
\]

The three coefficient norms in Theorem 1 therefore have exponent
\((\rho+\lambda_0)/2\) plus (9.189c).  In the range
\(\gamma_b+\eta\leq h\), this is
\((\rho+\lambda_0+p+\gamma_b+\eta)/2\).  Its two parenthetical terms have
exponents

\[
\boxed{
 \frac7{20}(m_0+\lambda_0+p)
   +\frac14\max(m_0,\lambda_0),
 \quad
 \frac38(m_0+\lambda_0+p)
   +\frac18\{p+\max(m_0,\lambda_0)\}.}
\tag{9.190}
\]

There is additionally
\(\tfrac12\max(0,p-m_0-\lambda_0)\) from the large-phase factor.  The
termwise sum over the fixed factors costs only
\(\gamma_a+\iota\): the exact \(1/(g_bn)\) in (9.187) cancels the
\(g_b,n\) counting lengths.

At the primitive transition corner

\[
 (\rho,\gamma_a,\gamma_b,\iota,\eta,\lambda_0,h,\ell)
 =\left(3,\frac12,0,0,0,\frac52,\frac52,\frac52\right),
\]

one has \(p=9/2\), coefficient-norm exponent \(5\), and the two
exponents in (9.190) are \(17/4\) and \(75/16\).  Including the
\(g_a\)-sum gives

\[
 \boxed{E_{\rm BC}=\frac{163}{16},\qquad
 E_{\rm trivial}=\frac{21}{2},\qquad
 E_{\rm target}=6.}
\tag{9.191}
\]

Thus the theorem saves exactly \(T^{5/16}\) over this triple-form trivial
ledger but still misses the local target by \(T^{67/16}\).  The gap is
larger than the earlier \(T^2\) sharp-frequency diagnostic because
(9.187) has completed an entire scalar stratum; this comparison must not
be used as a lower bound for the original block.

In fact the direct theorem covers **no** scalar-factor box on the balanced
face.  Put \(x=\gamma_a+\iota\).  From
\(\gamma_a+\gamma_b+\iota+\eta+\lambda_0=3\), the fixed-factor cost plus
the lower envelope of the fixed-factor cost plus the three coefficient
norms, including (9.189c), is

\[
 x+\frac{3+\lambda_0+p+\gamma_b+\eta}{2}
 =\frac{11}{2};
\tag{9.192}
\]

when \(\gamma_b+\eta>h\), the actual left side is larger.

The geometric exponent in the first term of (9.190) is
\(11-2x\geq5\), while the inverted-variable scale
\(m_0=3+\gamma_b+\eta\geq3\).  Hence that parenthetical exponent is at
least

\[
 \frac7{20}\cdot5+\frac14\cdot3=\frac52.
\]

The large-phase penalty is nonnegative, so (9.192) proves the uniform
finite-polytope conclusion

\[
 \boxed{E_{\rm BC}\geq8=E_{\rm target}+2.}
\tag{9.193}
\]

Equality can occur only on a degenerate nonoscillatory boundary of this
ledger; the primitive oscillatory corner has the larger gap (9.191).
The exact-rational checker exhausts the quarter-power grid of the factor
simplex and verifies the analytic lower bound (9.193).  Thus factorizing
the coprimality condition repairs theorem compatibility but does not hide
a covered balanced subregion.

The closest trace-function result does not fill the gap.  Korolev and
Shparlinski prove only a logarithmic saving for a Möbius-twisted bounded-
conductor trace function in intervals of length at least
\(p^{1/2+\varepsilon}\), with prime modulus \(p\).  Formula (9.188) has a
varying squarefree composite modulus and must average the full
\(h\delta_0\) family as well as the second modulus Möbius sign.  Applying
that result at fixed \(\lambda,h,\delta_0\), even on prime strata, loses
all of those lengths and cannot absorb (9.191).  The power-saving
Fouvry--Kowalski--Michel range and the newer fixed-numerator bilinear
Kloosterman-fraction bounds have the same structural mismatch when used
termwise.

Accordingly, (9.187)--(9.191) do not prove the gate.  They replace the
previous coefficient-dependent top-spectrum statement by a precise
published-theorem-compatible Type-II interface and prove quantitatively
that the direct theorem insertion is insufficient.  The primitive face
\(j=n=1\), \(\lambda=q\) remains self-similar to (9.186); a successful
argument must take a mixed moment in the product coefficient or preserve
the simultaneous \(\mu(r)\mu(\lambda)\) average before the fixed-factor
sum.

### 9.33 Centered common-divisor dispersion on the primitive face

The top layer in (9.186) must not be separated from the proper divisor
layers before its unit-group mean is removed.  For a positive modulus
\(m\), an integer \(A\), and \(x\in(\mathbb Z/m\mathbb Z)^\times\), put

\[
 \mathscr E_{m,A}(x)
 :=e_m(A\bar x_m)-\frac{c_m(A)}{\varphi(m)}.
\]

Let \(m,n\) be squarefree and \(L=[m,n]\).  Inversion permutes the unit
group modulo \(L\), so direct expansion gives the exact cross-modulus
covariance

\[
\boxed{
 \sum_{x\bmod L}^{*}
 \mathscr E_{m,A}(x)\overline{\mathscr E_{n,B}(x)}
 =c_L\!\left(A\frac Lm-B\frac Ln\right)
 -\frac{\varphi(L)c_m(A)c_n(B)}{\varphi(m)\varphi(n)}.}
\tag{9.194}
\]

This expression has a stronger squarefree factorization than a generic
LCM-modulus correlation.  Write

\[
 t=(m,n),\qquad m=tu,\qquad n=tv.
\]

Then \(t,u,v\) are pairwise coprime and (9.194) becomes

\[
\boxed{
 c_u(A)c_v(B)
 \left\{
  c_t(Av-Bu)-\frac{c_t(A)c_t(B)}{\varphi(t)}
 \right\}.}
\tag{9.195}
\]

In particular, the covariance is **identically zero when \((m,n)=1\)**,
for every pair \(A,B\), not merely after an estimate.  Moreover

\[
 \mu(m)\mu(n)=\mu(tu)\mu(tv)=\mu(u)\mu(v),
\tag{9.196}
\]

so the two modulus signs survive on the coprime cofactors rather than
being lost in the common divisor.  Summing (9.194) over
\(A=h\delta\) and \(B=h'\delta'\) therefore proves exact orthogonality
of the complete centered product kernels whenever their oscillatory
moduli are coprime.  This is the first cross-modulus identity in the
audit which simultaneously retains the product coefficients and both
modulus Möbius signs.

The same centering occurs before the divisor layers of (9.184) are
estimated.  Averaging the complete double-unit sum over its bilinear
coefficient gives

\[
 \frac1{\varphi(q)}\sum_{d\bmod q}^{*}\mu(q)U_q(A,B;d)
 =\frac{c_q(A)c_q(B)}{\varphi(q)}.
\]

Consequently (9.184) has the exact centered form

\[
\boxed{
\begin{aligned}
 &\mu(q)U_q(A,B;d)-\frac{c_q(A)c_q(B)}{\varphi(q)}\\
 &\quad=\sum_{\substack{k\mid q\\(k,B)=1}}
 k\mu(k)c_{q/k}(A)
 \left\{
 e_k\!\left(-AB\,\overline{d(q/k)}_k\right)
 -\frac{c_k(A)}{\varphi(k)}
 \right\}.
\end{aligned}}
\tag{9.197}
\]

The \(k=1\) bracket vanishes exactly.  Thus the nonoscillatory divisor
layer is not a separate contribution after centering, and the mean of
the top \(k=q\) layer cancels jointly with the proper layers **down to**
the explicit mean \(c_q(A)c_q(B)/\varphi(q)\), not to zero.  That
remaining mean is not discarded: it must stay recombined with the
principal/axis family as in Sections 9.24 and 9.30.  The dispersion below
acts only on the centered remainder in (9.197).  Bounding (9.186) by
itself discards this cancellation and asks for a strictly stronger
theorem than the centered scalar-stratum problem.

There is also an exact nonzero-frequency interface.  Define

\[
 \widehat{\mathscr C}_{m,n;A,B}(v)
 :=\sum_{x\bmod L}^{*}
 \mathscr E_{m,A}(x)\overline{\mathscr E_{n,B}(x)}e_L(-vx)
\]

and write \(S_L(a,b)=\sum_{x\bmod L}^{*}e_L(a\bar x+bx)\),
\(a_m=c_m(A)/\varphi(m)\), and
\(b_n=c_n(B)/\varphi(n)\).  Direct expansion gives

\[
\boxed{
\begin{aligned}
 \widehat{\mathscr C}_{m,n;A,B}(v)
 ={}&S_L\!\left(A\frac Lm-B\frac Ln,-v\right)
 -b_nS_L\!\left(A\frac Lm,-v\right)\\
 &-a_mS_L\!\left(-B\frac Ln,-v\right)
 +a_mb_n c_L(v).
\end{aligned}}
\tag{9.198}
\]

At \(v=0\), (9.198) is exactly (9.194); for \(v\ne0\) it is a
centered linear combination of four classical Kloosterman sums, not an
arbitrary inverse-product coefficient.

There is an additional tensor factorization on the coprime face.  Define
the one-modulus centered transform

\[
 \mathscr K_{m,A}(b)
 :=S_m(A,b)-\frac{c_m(A)c_m(b)}{\varphi(m)}.
\tag{9.198a}
\]

If \((m,n)=1\), Chinese remaindering separates the two unit coordinates
in every Fourier mode and gives

\[
\boxed{
 \widehat{\mathscr C}_{m,n;A,B}(v)
 =\mathscr K_{m,A}(-v\bar n_m)
  \mathscr K_{n,-B}(-v\bar m_n).}
\tag{9.198b}
\]

Both factors in (9.198b) vanish at \(v=0\), recovering the coprime
orthogonality in (9.195).  For \(v\ne0\), (9.198b) keeps the left and
right product coefficients separate and keeps the two Möbius weights
available for a Type-II treatment.  Expanding this product termwise
returns the four terms in (9.198), so no estimate or missing correction
is hidden in the tensor notation.

With the Fourier convention of Section 9.16, a smooth physical \(r\)-sum
satisfies the exact Poisson identity

\[
\boxed{
 \sum_{r\in\mathbb Z}W(r/R)
 \mathscr E_{m,A}(r)\overline{\mathscr E_{n,B}(r)}
 =\frac RL\sum_{v\in\mathbb Z}
 \widehat W(vR/L)\widehat{\mathscr C}_{m,n;A,B}(-v),}
\tag{9.199}
\]

where the centered factors are extended by zero off the units.  Hence
all incomplete endpoints are contained in the nonzero dual frequencies;
there is no silently completed sharp interval.

For \(m,n\asymp Q\) and \(t=(m,n)\), the dual length in (9.199) is

\[
 \frac LR\asymp\frac{Q^2}{tR}.
\tag{9.200}
\]

The physical/dual transition is therefore \(t_0=Q^2/R\).  At the
primitive transition corner \(Q=T^{5/2}\), \(R=T^3\), this is
\(t_0=T^2\).  The large-common-divisor pairs have the finite bound

\[
 \#\{m,n\in(Q,2Q]:(m,n)\geq D\}
 \leq\sum_{d\geq D}\left\lfloor\frac{2Q}{d}\right\rfloor^2
 \ll\frac{Q^2}{D},
\tag{9.201}
\]

so at \(D=t_0\) their pair count is \(T^3\), a \(T^2\) sparsity
relative to all \(Q^2=T^5\) pairs.  This matches the smallest balanced
deficit (9.172) at the level of modulus-pair counting, but is not by
itself a bound for the weighted kernel.

Equations (9.194)--(9.201) replace the former undifferentiated primitive
face by two exact tasks.  For \(t\geq t_0\), one must combine the proved
large-gcd sparsity with the centered product-coefficient moments.  For
\(t<t_0\), one must estimate the nonzero dual Kloosterman combination
(9.198), of length \(Q^2/(tR)\), while retaining
\(\mu(u)\mu(v)\) and both factorizations \(A=h\delta\),
\(B=h'\delta'\).  The zero dual frequency and every coprime-modulus
covariance are now evaluated exactly; the nonzero dual estimate remains
unproved and is the next analytic gate.

The fixed-modulus theorems located in the literature do not directly
bound this last tensor.  Blomer--Pascadi Theorem 1.1 averages two
independent argument intervals for one fixed modulus.  In (9.198b), both
moduli vary, while the linear arguments are the cross-inverses
\(-v\bar n_m\) and \(-v\bar m_n\), and \(A,B\) retain divisor-product
coefficients.  Kerr--Shparlinski--Wu--Xi likewise work with a fixed prime
field or a fixed Kloosterman modulus in their Type-II inputs.  Applying
either result after fixing \(m,n,A,B\) uses only a pointwise Weil-type
bound and discards \(\mu(m)\mu(n)\).  Formula (9.198b), rather than four
separate applications, is therefore the theorem-compatible object a new
two-modulus trace or dispersion estimate must control.

Even the most favorable direct insertion into the new tensor is
quantitatively insufficient.  When \((\delta,m)=1\), symmetry and a
unit change of variable give

\[
 S_m(h\delta,-v\bar n_m)
 =S_m(-v\delta\bar n_m,h).
\tag{9.202}
\]

Thus, after fixing \(\delta,m,n\), Blomer--Pascadi Theorem 5.5 is
syntactically applicable to the \((v,h)\)-sum, with the other tensor
factor absorbed into the arbitrary \(v\)-coefficient.  At the coprime
primitive corner its interval exponents relative to the fixed modulus
\(m\) are

\[
 |v|=m^{4/5},\qquad |h|=m.
\]

Substitution into every term of their function \(H(M,N,c)\) gives

\[
 H(m^{4/5},m,m)=m^{11/45+o(1)}.
\tag{9.203}
\]

The best complete-Cauchy factor is already \(m\), whereas Theorem 5.5
produces \(m^{1+11/45+o(1)}\); this is a loss
\(m^{11/45}=T^{11/18}\).  On the still more favorable unit-\(h\) face,
using the two short variables \((v,\delta)=(m^{4/5},m^{4/5})\) gives

\[
 H(m^{4/5},m^{4/5},m)=m^{13/90+o(1)},
\tag{9.204}
\]

again a loss over complete Cauchy, now \(T^{13/36}\).  These are exact
rational substitutions into Theorem 5.5, not heuristic comparisons.
They prove that applying the fixed-modulus theorem to only one factor of
(9.198b) cannot close the primitive face.  Any successful use of the
Kloosterman tensor must take a joint moment over both varying moduli (or
exploit the two Möbius signs) before paying either factor's operator norm.

### 9.34 Factorwise centering for a double Möbius Type-II split

The centered transform in (9.198a) has a further exact decomposition
which is adapted to a Type I/II factorization of each Möbius modulus.
Let \(m=ab\), with \((a,b)=1\), and put

\[
 M_{q,A}(z):=\frac{c_q(A)c_q(z)}{\varphi(q)},
 \qquad
 \mathscr K_{q,A}(z)=S_q(A,z)-M_{q,A}(z).
\]

Write \(\bar b_a\) and \(\bar a_b\) for the two CRT inverses, and abbreviate

\[
 \mathscr K_a^{(b)}
 :=\mathscr K_{a,A\bar b_a}(z\bar b_a),\qquad
 \mathscr K_b^{(a)}
 :=\mathscr K_{b,A\bar a_b}(z\bar a_b).
\]

Twisted multiplicativity of the raw Kloosterman sum and invariance of a
Ramanujan sum under multiplication by a unit give

\[
 S_{ab}(A,z)
 =S_a(A\bar b_a,z\bar b_a)
  S_b(A\bar a_b,z\bar a_b),
 \qquad
 M_{ab,A}(z)=M_{a,A}(z)M_{b,A}(z).
\tag{9.205}
\]

Subtracting the second product from the first therefore leaves exactly
three, rather than four, terms:

\[
\boxed{
 \mathscr K_{ab,A}(z)
 =\mathscr K_a^{(b)}\mathscr K_b^{(a)}
  +\mathscr K_a^{(b)}M_{b,A}(z)
  +M_{a,A}(z)\mathscr K_b^{(a)}.}
\tag{9.206}
\]

The all-principal product \(M_{a,A}M_{b,A}\) cancels identically.  This
is an algebraic consequence of centering, not an estimate, and (9.206)
is valid for arbitrary coprime positive \(a,b\); squarefreeness enters
only when the Möbius weights are restored.

Now write the coprime cofactors in (9.198b) as

\[
 u=ab,\qquad v=cd,\qquad (a,b,c,d)\quad\text{pairwise coprime},
\]

and set \(z_u=-k\bar v_u\), \(z_v=-k\bar u_v\).  Applying (9.206) on
both sides gives the finite nine-term identity

\[
\boxed{
 \widehat{\mathscr C}_{u,v;A,B}(k)
 =\left(K_aK_b+K_aM_b+M_aK_b\right)
  \left(K_cK_d+K_cM_d+M_cK_d\right),}
\tag{9.207}
\]

where every local \(K\) includes the CRT-scaled numerator and frequency
from (9.206).  Thus every one of the nine summands contains at least one
centered local transform from \(\{a,b\}\) and at least one from
\(\{c,d\}\).  There is no term which is principal on an entire side.
For squarefree \(u,v\), the signs split without loss:

\[
 \mu(u)\mu(v)=\mu(a)\mu(b)\mu(c)\mu(d).
\tag{9.208}
\]

Consequently a Vaughan/Heath--Brown-style split may be inserted before
any Cauchy--Schwarz step while retaining all four factor signs and a
certified centered local factor on each side.  This is the precise
factorized interface missing from a termwise application of the
fixed-modulus estimates in Sections 9.5 and 9.27.

There is a useful, but limited, pointwise screening on the unit face.
If \((Az,q)=1\) and \(q\) is squarefree, then

\[
 |M_{q,A}(z)|=\frac1{\varphi(q)}\ll_\varepsilon q^{-1+\varepsilon},
 \qquad
 |\mathscr K_{q,A}(z)|\ll_\varepsilon q^{1/2+\varepsilon}.
\tag{9.209}
\]

Replacing a local centered factor by its local mean therefore saves
\(q^{3/2-o(1)}\).  At the primitive corner
\(u,v\asymp T^{5/2}\), with balanced Type-II factors
\(a,b,c,d\asymp T^{5/4}\), the exact ledger is

\[
 \text{one local mean saves }T^{15/8-o(1)},
 \qquad
 \text{two local means save }T^{15/4-o(1)}.
\tag{9.210}
\]

Compared only with the \(T^2\) deficit diagnostic in (9.172), the four
nine-term patterns containing two means have a raw margin \(T^{7/4}\),
the four patterns containing exactly one mean still miss by \(T^{1/8}\),
and the fully centered pattern \(K_aK_bK_cK_d\) receives no such
pointwise gain:

\[
 2-\frac{15}{8}=\frac18,
 \qquad
 2\frac{15}{8}-2=\frac74.
\tag{9.211}
\]

This is a **screening ledger, not a closure proof**.  The comparison does
not yet account for the product-coefficient multiplicities, nonunit
strata, smooth dual weights, or the simultaneous sums over all four
factors.  In particular it does not authorize deleting the two-mean
patterns from the coupled kernel.  It does, however, identify the
analytic priority sharply: first control the fully centered four-local
term, then recover the missing \(T^{1/8}\) on the one-mean terms, while
the two-mean terms should be treated by their explicit totient
denominators rather than by a generic Kloosterman norm.

Pascadi's composite-modulus Type-II theorem is structurally close to
(9.206), since its proof also exploits a factorization of the modulus.
Its published statement, however, bounds two argument sequences for one
fixed modulus.  It does not average the mutually inverted pair
\((u,v)\), and applying it after taking absolute values over the other
three factors loses (9.208).  Hence the negative fixed-modulus audits
(9.21) and (9.203)--(9.204) remain in force.  The new result is the exact
nine-term reduction and the unit-mean screening (9.205)--(9.211); the
joint estimate for the fully centered and one-mean families remains
unproved.

### 9.35 Numerator completion and Young's varying-level rational large sieve

The obstruction at the end of Section 9.34 changes after completing the
*numerator* of each centered local transform.  Let \((\gamma,q)=1\), and
use the Fourier convention \(e_q(x)=e(x/q)\).  Directly opening the
Kloosterman sum and the Ramanujan mean gives the finite identity

\[
\boxed{
 \sum_{h\bmod q}\mathscr K_{q,\gamma h}(z)e_q(-\ell h)
 =q\,1_{(\ell,q)=1}
 \left(e_q(z\gamma\bar\ell)-\frac{c_q(z)}{\varphi(q)}\right).}
\tag{9.212}
\]

In particular, the zero numerator-dual mode and **every nonunit dual
mode vanish exactly**.  If \(q=ab\), \((a,b)=1\), and only the fully
centered term in (9.206) is retained, CRT factors the left side of
(9.212) into the product of the two corresponding local transforms.
It is therefore supported precisely on \((\ell,ab)=1\).  This statement
is valid for arbitrary coprime positive \(a,b\), not only for primes or
balanced factors.

For a smooth numerator interval, Poisson summation in residue classes
now reads, up to replacing \(\ell\) by \(-\ell\),

\[
 \sum_{h\in\mathbb Z}W(h/H)\mathscr K_{q,\gamma h}(z)
 =\frac Hq\sum_{\ell\in\mathbb Z}
 \widehat W(H\ell/q)
 \sum_{r\bmod q}\mathscr K_{q,\gamma r}(z)e_q(-\ell r).
\tag{9.213}
\]

At the primitive corner \(H\asymp q\), rapid decay restricts the dual
sum to \(O(T^\varepsilon)\) values of \(\ell\), and (9.212) keeps only
the units.  Thus the axes and scalar-gcd dual strata which survived the
*uncentered* completion in Sections 9.29--9.30 do not occur in the
fully centered numerator completion.

Complete both sides of (9.198b), write the two nonzero dual frequencies
as \(L,M>0\) after splitting signs, and keep the primitive unit face.
For \((u,vLM)=1\), \((M,v)=1\), put

\[
 j_M:=\frac{M\bar M_v-1}{v}.
\]

Elementary additive reciprocity gives the exact phase identity

\[
\boxed{
 e_u(-k\delta\overline{vL}_u)
 e_v(k\delta'\overline{uM}_v)
 =e_{vLM}\!\left(k(M\delta+L\delta')\bar u_{vLM}\right)
  e_M\!\left(kj_M\delta'\bar u_M\right)
  e\!\left(-\frac{k\delta}{uvL}\right).}
\tag{9.214}
\]

The second factor has fixed modulus \(M=T^{O(\varepsilon)}\), so residue
class separation costs only \(T^\varepsilon\).  The last phase has
argument \(T^{-1+O(\varepsilon)}\) at
\(k,\delta,\delta'\asymp T^2\) and
\(u,v\asymp T^{5/2}\), and may be retained in the smooth coefficient.
The first factor is the varying-level rational character needed below,
with

\[
 q=vLM,\qquad t=k,\qquad
 A=M\delta+L\delta',\qquad b=u.
\tag{9.215}
\]

Young's additive large sieve (Theorem 1.2 of the reference in Section
11) states

\[
 \max_{\|\alpha\|_2=1}\sum_{q\sim Q}\sum_{t\bmod q}^{*}
 \left|\sum_{ab\sim N\atop (a,b)=1,(ab,q)=1}
 \alpha_{a,b}e_q(ta\bar b)\right|^2
 \ll_\varepsilon (Q^2+N)^{1+\varepsilon}.
\tag{9.216}
\]

Unlike the fixed-modulus inputs audited above, (9.216) averages the
outer modulus and the complete unit row simultaneously.  A shorter
\(k\)-interval is inserted by extending its row coefficient by zero.
After dyadically separating the sign and size of \(A\), the primitive
scales in (9.215) give the exact exponent ledger

\[
\begin{array}{c|c}
 \text{quantity}&T\text{-exponent}\\ \hline
 Q=vLM&5/2\\
 N=|A|u&9/2\\
 Q^2+N&5\\
 \sum_{A,u}|\alpha_{A,u}|^2
   \ \leq\ U\sum_A r_{L,M}(A)^2&17/2\\
 \text{Cauchy over the actual }(v,k)\text{ rows}&9/4\\ \hline
 \text{Young bound}&9\\
 \text{raw five-variable count}&11\\
 \text{saving}&2.
\end{array}
\tag{9.217}
\]

Here \(r_{L,M}(A)=\#\{(\delta,\delta'):M\delta+L\delta'=A\}\), and
\(\sum_A r_{L,M}(A)^2\ll T^{6+\varepsilon}\) is the elementary additive
convolution energy bound for two intervals of length \(T^2\).  Hence
(9.216) supplies exactly the \(T^2\) saving missing in (9.172), with no
power margin.  The exceptional slice \(A=0\) has only \(O(T^{2+\varepsilon})\)
pairs \((\delta,\delta')\), rather than \(T^4\), and has the same saving
before the large sieve is used.

All coprimality conditions in (9.216) must be enforced, rather than
hidden in \(T^\varepsilon\).  For squarefree main moduli, set

\[
 d=(k,q),\qquad e=(A,q/d),\qquad g=(A/e,u),
\]

and write their dyadic exponents as \(\kappa,\eta,\gamma\).  After
cancelling \(d,e\) from the additive character and \(g\) from the
rational number, the reduced outer modulus, row length, rational height,
and coefficient energy have exponents

\[
 \frac52-\kappa-\eta,\qquad
 2-\kappa,\qquad
 \frac92-\eta-2\gamma,\qquad
 \frac{17}{2}-2\gamma.
\]

The last entry uses the finite congruence estimate

\[
 \sum_{A\equiv0\ (g)}r_{L,M}(A)^2
 \ll T^\varepsilon\frac{D^3}{g},\qquad D=T^2,
\tag{9.218}
\]

after separating the \(T^{O(\varepsilon)}\) common factors of \(g\) with
\(LM\).  One factor \(g^{-1}\) comes from (9.218), and the other from
restricting \(u\) to multiples of \(g\).  Even charging
\(T^{\kappa+\eta+\gamma}\) for selecting \(d,e,g\), the resulting bound
has exponent

\[
 \mathcal Y(\kappa,\eta,\gamma)
 =\frac{13}{2}+\frac\eta2+
  \frac12\max\!\left(5-2\kappa-2\eta,
                      \frac92-\eta-2\gamma\right)
 \leq9.
\tag{9.219}
\]

Indeed, the first branch is \(9-\kappa-\eta/2\), while the second is at
most \(35/4\).  Thus none of these three gcd decompositions worsens the
critical \(T^9\) threshold.

The mean-containing terms in (9.207) also have an elementary modulus
sum.  For squarefree \(q\) and nonzero \(k\),

\[
 \frac{c_q(k)}{\varphi(q)}
 =\frac{\mu(q/(q,k))}{\varphi(q/(q,k))},\qquad
 \sum_{Q<q\leq2Q}\frac{|c_q(k)|}{\varphi(q)}
 \leq\tau(k)\sum_{e\leq2Q\atop e\ {\rm squarefree}}
       \frac1{\varphi(e)}
 \ll_\varepsilon T^\varepsilon.
\tag{9.220}
\]

Equations (9.212)--(9.220) are an **exact arithmetic exponent closure for
one fixed scalar-factor stratum of the coprime-unit, fully centered
primitive family**, not yet a proof of CK\(_{\rm ub}(3)\).  The ledger
(9.217) does not include the outer sum over the scalar factors
\(g_a,j\) in (9.187).  Restoring that sum by triangle costs
\(T^{\gamma_a+\iota}\); at the transition corner this is
\(T^{1/2}\), so the globally aggregated primitive family is not closed.
The corrected coverage calculation is given in Section 9.39.  Uniform
separation of the archimedean weights, nonunit numerator multipliers, and
recombination with the principal/axis spectra remain additional duties.
Common-modulus strata are treated separately in Sections 9.36--9.37.
The valid conclusion is narrower: the fixed-stratum raw term maps to a
published varying-level theorem at exactly the required exponent.

### 9.36 Common-modulus collision before the inverse-residue sum

The common divisor \(t=(m,n)\) should not be bounded by a pointwise
Kloosterman estimate.  Completing the numerator one step earlier turns
it into an exact CRT collision.  For \(x\in(\mathbb Z/q\mathbb Z)^*\)
and \((\gamma,q)=1\), direct finite Fourier inversion gives

\[
\boxed{
 \sum_{h\bmod q}\mathscr E_{q,\gamma h}(x)e_q(-\ell h)
 =q\,1_{(\ell,q)=1}
 \left(1_{x\equiv\gamma\bar\ell\ ({\rm mod}\ q)}
       -\frac1{\varphi(q)}\right).}
\tag{9.221}
\]

Thus the unit support in (9.212) already exists before the
inverse-residue sum: a centered inverse phase becomes one unit residue
class minus the uniform unit-group mean.

Let \(m=tu\), \(n=tv\), where \(t,u,v\) are pairwise coprime, and put
\(Q=tuv\).  For unit residues \(r\bmod m\), \(s\bmod n\), define

\[
 \mathscr D_{m,r}(x)
 :=1_{x\equiv r\ ({\rm mod}\ m)}-\frac1{\varphi(m)}.
\]

If \(r\equiv s\pmod t\), let \(x_0\bmod Q\) be the unique simultaneous
solution \(x_0\equiv r\pmod m\), \(x_0\equiv s\pmod n\).  Expanding the
two centered point masses and summing the free CRT coordinate gives

\[
\boxed{
\begin{aligned}
 \sum_{x\bmod Q}^{*}\mathscr D_{m,r}(x)\mathscr D_{n,s}(x)e_Q(-kx)
 ={}&1_{r\equiv s\ ({\rm mod}\ t)}e_Q(-kx_0)\\
 &-\frac{c_v(k)}{\varphi(n)}e_m(-kr\bar v_m)
  -\frac{c_u(k)}{\varphi(m)}e_n(-ks\bar u_n)\\
 &+\frac{c_Q(k)}{\varphi(m)\varphi(n)}.
\end{aligned}}
\tag{9.222}
\]

There is no Weil loss in the first term: it is a single CRT point.
For the left numerator dual \(L\) and the conjugate right numerator
dual \(M\), (9.221) selects

\[
 r\equiv\delta\bar L\pmod m,\qquad
 s\equiv-\delta'\bar M\pmod n.
\]

Consequently the collision in (9.222) exists exactly when

\[
\boxed{t\mid M\delta+L\delta'.}
\tag{9.223}
\]

On this support, CRT factorization of the additive character gives

\[
 e_Q(-kx_0)
 =e_m(-k\delta\overline{vL}_m)
  e_v(k\delta'\overline{mM}_v).
\tag{9.224}
\]

This is precisely the left side of (9.214), with its left modulus
replaced by \(m=tu\).  Its varying-level rational character has
numerator \(A=M\delta+L\delta'\), denominator \(m\), and outer modulus
\(vLM\).  Equation (9.223) cancels the same factor \(t\) from numerator
and denominator:

\[
 \frac{A}{m}=\frac{A/t}{u}.
\tag{9.225}
\]

This cancellation is also visible in the coefficient energy.  Put
\(t=T^\tau\), \(0\leq\tau\leq2\); this is exactly the range with
nonzero physical dual frequencies, whose length is \(T^{2-\tau}\).
For fixed \(t\), the Young ledger is

\[
\begin{array}{c|c}
 \text{quantity}&T\text{-exponent}\\ \hline
 vLM&5/2-\tau\\
 k\text{-row}&2-\tau\\
 |A/t|u&9/2-2\tau\\
 \sum_{A/t,u}|\alpha_{A/t,u}|^2&17/2-2\tau\\
 (v,k)\text{ row Cauchy}&9/4-\tau\\
 \text{Young constant}&5-2\tau\\ \hline
 \text{bound for fixed }t&9-3\tau\\
 \text{after summing }t\asymp T^\tau&9-2\tau\leq9.
\end{array}
\tag{9.226}
\]

The energy entry uses (9.218) with \(g=t\), while the count of
\(u=m/t\) supplies the second \(t^{-1}\).  Hence the **fixed-scalar
nonzero-dual CRT collision term** has exponent \(9-2\tau\).  This still
omits the outer scalar-factor sum from (9.187).  At the transition corner
that sum costs \(T^{1/2}\), so the corrected exponent is
\(19/2-2\tau\), which closes precisely when \(\tau\geq1/4\); see
(9.236)--(9.238).

The remaining coprimality splits do not consume this margin.  If
\(\kappa,\eta,\gamma\) denote respectively the row gcd, outer-numerator
gcd, and lowest-rational gcd exponents after (9.225), the bound after
summing \(t\) is

\[
 \frac{13}{2}-\tau+\frac\eta2+
 \frac12\max\!\left(5-2\tau-2\kappa-2\eta,
                    \frac92-2\tau-\eta-2\gamma\right)
 \leq9.
\tag{9.227}
\]

The two branches are
\(9-2\tau-\kappa-\eta/2\) and
\(35/4-2\tau-\gamma\).  The three Ramanujan marginal terms in
(9.222) and the \(k=0\) covariance are evaluated next.  Nonunit
numerator multipliers are not silently included in this conclusion.

### 9.37 Ramanujan marginals and the common-modulus zero mode

The three noncollision terms in (9.222) are strictly easier after their
squarefree factors are kept intact.  Since \(t,u,v\) are pairwise
coprime,

\[
 \frac{c_v(k)}{\varphi(n)}
 =\frac1{\varphi(t)}\frac{c_v(k)}{\varphi(v)},\qquad
 \frac{c_Q(k)}{\varphi(m)\varphi(n)}
 =\frac{c_t(k)}{\varphi(t)^2}
  \frac{c_u(k)}{\varphi(u)}
  \frac{c_v(k)}{\varphi(v)}.
\tag{9.228}
\]

Apply (9.220) to every normalized Ramanujan factor before taking the
remaining absolute values.  For \(t=T^\tau\), \(0\leq\tau\leq2\), a
one-sided marginal leaves only one cofactor modulus, the \(k\)-row, and
the two numerator intervals; the factor \(1/\varphi(t)\) pays for the
dyadic \(t\)-sum.  The all-mean term removes both cofactor-modulus sums.
Their exponent ledger is

\[
\boxed{
 \mathcal M_{\rm one}(\tau)=\frac{17}{2}-2\tau\leq\frac{17}{2},
 \qquad
 \mathcal M_{\rm all}(\tau)=6-\tau\leq6.}
\tag{9.229}
\]

Both are below the target exponent \(9\), with margins at least
\(1/2\) and \(3\), respectively.  No cancellation of a Möbius sum is
used here.

At \(k=0\), the four terms of (9.222) must be recombined before
estimation.  Since \(c_j(0)=\varphi(j)\), they collapse exactly to

\[
 \sum_{x\bmod Q}^{*}\mathscr D_{m,r}(x)\mathscr D_{n,s}(x)
 =1_{r\equiv s\ ({\rm mod}\ t)}-\frac1{\varphi(t)}.
\tag{9.230}
\]

With the numerator residues selected by (9.221), this is
\(1_{t\mid M\delta+L\delta'}-1/\varphi(t)\), on
\((\delta\delta',t)=1\).  The centering removes every complete period.
More precisely, for positive interval lengths \(D_1,D_2\) and
\((LM,t)=1\),

\[
\boxed{
 \left|
 \sum_{\substack{\delta\leq D_1,\ \delta'\leq D_2\\
                  (\delta\delta',t)=1}}
 \left(1_{t\mid M\delta+L\delta'}-\frac1{\varphi(t)}\right)
 \right|
 \leq \#\{\delta\leq D_1:(\delta,t)=1\}\leq D_1.}
\tag{9.231}
\]

For each fixed unit \(\delta\bmod t\), the target is one unit residue
class of \(\delta'\); the counts of any two residue classes in an
interval differ by at most one, which proves (9.231).  Shifted intervals
obey the same bound, and separated smooth weights follow by partial
summation.  At \(D_1,D_2\asymp T^2\), (9.231) saves one full \(T^2\)
numerator length.  Including \(t,u,v\), the zero-mode arithmetic count
is at most \(T^{7-\tau+\varepsilon}\), well below the exponent-\(9\)
threshold.

Consequently both one-sided marginals, the all-mean term, and the zero
mode remain arithmetically controlled after restoring the transition
scalar cost: their exponents become at most \(9,13/2,15/2-\tau\),
respectively.  The collision term is controlled only for
\(\tau\geq1/4\).  The unit-numerator residual is therefore the
small-common-divisor range \(0\leq\tau<1/4\), together with coherent
scalar Möbius aggregation and the uniform separation/recombination of
the original archimedean weights.

### 9.38 Exact reduction of nonunit numerator multipliers

The unit hypothesis in (9.221) can be removed exactly.  Let
\(g=(\delta,q)\), \(c=q/g\).  Opening the inverse phase and the
Ramanujan mean before summing \(h\) gives

\[
\boxed{
\begin{aligned}
 &\sum_{h\bmod q}\mathscr E_{q,\delta h}(x)e_q(-\ell h)\\
 &\quad=q\,1_{g\mid\ell}\,1_{(\ell/g,c)=1}
 \left(
 1_{x\equiv(\delta/g)\overline{\ell/g}\ ({\rm mod}\ c)}
 -\frac1{\varphi(c)}
 \right).
\end{aligned}}
\tag{9.232}
\]

Thus the dual support forces \((\ell,q)=g\), and the surviving kernel is
the same centered point mass as (9.221), now on the reduced modulus
\(c=q/g\).  The extreme case \(c=1\) vanishes identically.

There is also no hidden Kloosterman loss when this reduced point mass is
summed over the original unit group.  Let \(c,d\mid Q\),
\(h=[c,d]\), \(Q=hw\), and assume \((h,w)=1\), as holds for divisors of
a squarefree ambient modulus.  If

\[
 \Sigma_Q(k)
 :=\sum_{x\bmod Q}^{*}\mathscr D_{c,r}(x)
                    \mathscr D_{d,s}(x)e_Q(-kx),
\]

then CRT gives

\[
\boxed{
 \frac{\Sigma_Q(k)}Q
 =\frac{c_w(k)}w\,
  \frac1h
  \sum_{x\bmod h}^{*}\mathscr D_{c,r}(x)
                    \mathscr D_{d,s}(x)
                    e_h(-k\bar w_hx).}
\tag{9.233}
\]

The deleted ambient coordinates therefore contribute only a normalized
Ramanujan factor, with \(|c_w(k)|/w\leq1\); the core on the right is
exactly the reduced collision (9.222).

For a dyadic gcd \(g=T^\xi\), restricting \(\delta\) to multiples of
\(g\) saves \(T^\xi\), while summing the possible \(g\)-values costs at
most \(T^\xi\).  Hence the finite gcd bookkeeping is neutral, the
normalized free factor in (9.233) costs no power, and every oscillatory
modulus in the core is shortened:

\[
 \boxed{
  \text{gcd selection }T^\xi
  \times\text{ numerator restriction }T^{-\xi}
  \times\left|\frac{c_w(k)}w\right|
  \leq1.}
\tag{9.234}
\]

At the primitive numerator scale \(H\asymp q\), smooth completion has
\(|\ell|\leq T^\varepsilon\).  The support condition in (9.232) then
forces \(g\leq T^\varepsilon\), so all primitive nonunit multipliers
reduce to Sections 9.35--9.37 without a power loss.

For shorter numerator intervals, (9.232)--(9.234) are an exact reduced
interface rather than a complete global estimate: the reduced moduli,
the possibly longer quotient dual rows, and the original archimedean
weights must still be dyadically separated together.  In particular,
this section does not declare CK\(_{\rm ub}(3)\) proved.  It does remove
the former algebraic ambiguity about nonunit completion and proves that
no pointwise Weil factor is created by the deleted prime coordinates.

### 9.39 Restoring the scalar-factor sum: exact transition coverage

The Young ledgers above are statements for fixed
\(g_a,g_b,j,n\).  The transition corner of (9.187) has

\[
 \rho=\sigma=3,\qquad h=\ell=\lambda_0=\frac52,
 \qquad x:=\gamma_a+\iota=\frac12,
 \qquad \gamma_b=\eta=0.
\tag{9.235}
\]

Thus the reduced \(\delta_0\)-length is \(T^{\ell-x}=T^2\).
Let \(t=T^\tau\) be the common factor of the two oscillatory moduli in
the dispersion square.  After the collision condition cancels \(t\)
from numerator and denominator, the exact exponent ledger, now including
both the dyadic \(t\)-sum and the outer scalar-factor triangle cost, is

\[
\begin{array}{c|c}
 \text{quantity}&T\text{-exponent}\\ \hline
 \text{reduced numerator}&2\\
 \text{outer oscillatory modulus}&5/2-\tau\\
 \text{nonzero row}&2-\tau\\
 \text{rational height}&9/2-2\tau\\
 \text{coefficient energy}&17/2-2\tau\\
 \text{row Cauchy}&9/4-\tau\\
 \text{Young constant}&5-2\tau\\ \hline
 \text{fixed-stratum Young bound}&9-3\tau\\
 \text{after the }t\text{-sum}&9-2\tau\\
 \text{after the scalar-factor sum}&19/2-2\tau.
\end{array}
\tag{9.236}
\]

The dispersion second-moment target is \(RS^2=T^9\), not the local
first-moment target \(RS=T^6\).  At \(\tau=0\), the raw count, Young
bound, and target have exponents

\[
 \boxed{\frac{23}{2},\qquad\frac{19}{2},\qquad9,}
\tag{9.237}
\]

so the required saving is \(5/2\), while (9.216) supplies only \(2\).
More generally,

\[
 \boxed{
  E_{\rm Young}^{\rm scalar}(\tau)-9
   =\frac12-2\tau,
  \qquad
  E_{\rm Young}^{\rm scalar}(\tau)\leq9
   \Longleftrightarrow \tau\geq\frac14.}
\tag{9.238}
\]

This is a finite rational coverage proposition: on the admissible
quarter-power grid \(0\leq\tau\leq2\), the uncovered set is exactly the
single grid point \(\tau=0\); without discretizing, it is the interval
\(0\leq\tau<1/4\).  The checker evaluates every entry of (9.236)--(9.238)
with exact fractions.

The residual can be written before any scalar triangle inequality.  On
the primitive transition face \(g_b=j=n=1\), put
\(G=T^{1/2},Q=T^{5/2},D=T^2\).  Since \(r=gq+d\), reduction modulo
\(q\) gives \(\bar r_q=\bar d_q\).  Up to the already displayed smooth
weights and exact moving endpoints, every unresolved packet has the
finite form

\[
\boxed{
 \mathfrak P[\Omega]
 :=\sum_{g\asymp G}\mu(g)
 \sum_{q\asymp Q\atop(g,q)=1}\mu(q)
 \sum_{d\in I(gq)\atop(d,gq)=1}\mu(gq+d)
 \sum_{h\asymp T^{5/2}}
 \sum_{\delta_0\asymp T^2}
 \Omega(g,q,d,h,\delta_0)
 e_q(-h\delta_0\bar d_q),}
\tag{9.239}
\]

Here \(I(gq)=(R-gq,2R-gq]\) is the exact moving interval inherited
from (9.166), and \(\Omega\) denotes the corresponding localized smooth
weight together with the scalar-stratum coefficients already present in
(9.187).  Formula (9.239) retains the product \(h\delta_0\) and the
simultaneous signs \(\mu(g)\mu(q)\mu(gq+d)\).  The phase is independent
of \(g\) only after \(d\) is fixed; consequently Cauchy in \(g\) asks for
short two-point Möbius correlations between \(g_1q+d\) and
\(g_2q+d\), rather than giving free orthogonality.

There is an exact two-cutoff Type-I/II decomposition of the last Möbius
factor which introduces no remainder.  For integers \(U,V\geq1\) and
\(r>\max(U,V)\), use \(\mu*\mu*1=\mu\) and split the two divisor
variables at \(U,V\).  Divisor orthogonality gives

\[
 \sum_{b\leq U\atop b\mid r}\mu(b)
 \sum_{c\mid r/b}\mu(c)=0,
 \qquad
 \sum_{c\leq V\atop c\mid r}\mu(c)
 \sum_{b\mid r/c}\mu(b)=0.
\tag{9.240}
\]

Subtracting the common short--short rectangle from either equality
cancels both mixed rectangles in the full convolution and yields

\[
\boxed{
 \mu(r)=
 -\sum_{bc\mid r\atop b\leq U,\ c\leq V}\mu(b)\mu(c)
 +\sum_{bc\mid r\atop b>U,\ c>V}\mu(b)\mu(c).}
\tag{9.241}
\]

Inserting \(r=gq+d\) in (9.239) defines a short--short Type-I packet
and a long--long Type-II packet, both still carrying

\[
 \mu(g)\mu(q)\mu(b)\mu(c),\qquad
 bc\mid gq+d,\qquad
 \Omega(g,q,d,h,\delta_0)e_q(-h\delta_0\bar d_q).
\tag{9.242}
\]

Thus no cross term, endpoint term, or truncation error is hidden in this
split, and the coupled product \(h\delta_0\) has not been replaced by an
arbitrary coefficient.  The finite checker verifies (9.241) for unequal
cutoffs as well as the diagonal choice \(U=V\).  Estimating these two
packets uniformly in the small-common-factor range remains the analytic
gate; (9.241) is a reduction, not its proof.

The short--short packet cannot be closed by congruence density alone.
Indeed, \(bc\mid r=gq+d\) and \((r,gq)=1\) imply \((bc,q)=1\), so for
fixed \(b,c,q,d\) the variable \(g\) occupies one residue class modulo
\(bc\).  Hence

\[
 \#\{g\asymp G:bc\mid gq+d\}
 \leq \frac{G}{bc}+1,
\quad
 \sum_{b\leq U,c\leq V}
 \left(\frac{G}{bc}+1\right)
 \ll G\log(2U)\log(2V)+UV.
\tag{9.243}
\]

If \(G=T^\gamma,U=T^u,V=T^v\), the absolute Type-I exponent is therefore

\[
 \boxed{E_{\rm I}^{\rm abs}(u,v)=\max(\gamma,u+v)\geq\gamma.}
\tag{9.244}
\]

At \(\gamma=1/2\), every choice \(u+v\leq1/2\) retains the full missing
half-power, while \(u+v>1/2\) is worse.  Thus the Type-I congruence is a
useful reparametrization but supplies no covered transition box after
absolute values.

The balanced cutoff is \(U=V=T^{1/4}\).  In the long--long packet write
\(r=bck\).  At its lower cutoff face,

\[
 bc>T^{1/2},\qquad k\ll T^{5/2},\qquad
 |bck-gq|=|d|\ll T^2,
\tag{9.245}
\]

and, since \(d\equiv bck\pmod q\),

\[
 e_q(-h\delta_0\bar d_q)
 =e_q(-h\delta_0\overline{bck}_q),
 \qquad
 \left|\frac{k}{q}-\frac{g}{bc}\right|\ll T^{-1}.
\tag{9.246}
\]

For fixed \(b,c,g,q\), the allowed \(k\)-window has exponent \(3/2\).
The exact cutoff ledger is therefore product floor \(1/2\), quotient
ceiling \(5/2\), fixed-divisor quotient window \(3/2\), and rational
distance exponent \(-1\).  This is a near-determinant Type-II family in
the two long variables \(k,q\), coupled to the three short factors
\(b,c,g\) and the unfused product \(h\delta_0\).  No published estimate
cited here controls this complete family; (9.245)--(9.246) specify the
remaining long--long interface rather than bounding it.

There is a second exact recombination which shows that independent
Möbius cancellation in \(g\) is not the right target.  Put
\(s=gq\) and \(m=g\delta_0\).  Since \(s\) is squarefree and
\((d,s)=1\),

\[
 \mu(g)\mu(q)=\mu(s),\qquad
 e_q(-h\delta_0\bar d_q)=e_s(-hm\bar d_s).
\tag{9.247}
\]

For dyadic sets \(\mathcal G,\mathcal Q\), define the divisor-incidence
multiplicity

\[
 \nu_{\mathcal G,\mathcal Q}(s,m)
 :=\#\{g:g\mid(s,m),\ g\in\mathcal G,\ s/g\in\mathcal Q\}.
\tag{9.248}
\]

Then the complete primitive scalar sum has the boundary-exact identity

\[
\boxed{
 \sum_{gq=s\atop g\in\mathcal G,\ q\in\mathcal Q}
 \mu(g)\mu(q)
 \sum_{\delta_0\leq L/g}
 e_q(-h\delta_0\bar d_q)
 =\mu(s)\sum_{m\leq L}
 \nu_{\mathcal G,\mathcal Q}(s,m)e_s(-hm\bar d_s).}
\tag{9.249}
\]

There is no floor error: \(\delta_0\leq\lfloor L/g\rfloor\) is
equivalent to \(m=g\delta_0\leq L\).  Also
\(\nu_{\mathcal G,\mathcal Q}(s,m)\leq\tau((s,m))\leq\tau(s)\), so it
is divisor-bounded pointwise, although it depends jointly on the modulus
and the product variable.  The finite checker verifies (9.247)--(9.249)
for every selected divisor family on squarefree \(s\leq60\), including
the reduced modulus \(q=1\).

Consequently (9.239) can equivalently be expressed with only the original
two shifted signs \(\mu(s)\mu(s+d)\), at the price of the structured
coefficient \(\nu_{\mathcal G,\mathcal Q}(s,m)\):

\[
 \sum_{s\asymp S}\mu(s)
 \sum_{d\in I(s)\atop(d,s)=1}\mu(s+d)
 \sum_{h\asymp H}\sum_{m\asymp L}
 \nu_{\mathcal G,\mathcal Q}(s,m)
 \widetilde\Omega(s,d,h,m)e_s(-hm\bar d_s).
\tag{9.250}
\]

This removes the artificial scalar triangle inequality but returns the
full modulus \(s\asymp T^3\).  Young's theorem in the fixed reduced
modulus \(q\asymp T^{5/2}\) does not directly apply to (9.250), while
replacing \(\nu\) by an arbitrary divisor-bounded coefficient discards
the incidence relation which created the sparsity.  The revised analytic
gate is therefore a divisor-incidence large sieve for (9.250), or an
equivalent estimate of the Type-I/II packets (9.242), in the range
\(0\leq\tau<1/4\).

The incidence coefficient also has an exact second moment with all floor
boundaries retained.  Write
\(\mathcal G_{s,\mathcal Q}=\{g\in\mathcal G:g\mid s,
s/g\in\mathcal Q\}\).  Opening the square in (9.248) gives

\[
\boxed{
 \sum_{m\leq L}\nu_{\mathcal G,\mathcal Q}(s,m)^2
 =\sum_{g_1,g_2\in\mathcal G_{s,\mathcal Q}}
   \left\lfloor\frac{L}{[g_1,g_2]}\right\rfloor
 \leq\left(\frac LG+1\right)\tau(s)^2,}
\tag{9.251}
\]

where every \(g\in\mathcal G\) is at least \(G\).  At the transition
scale this is \(T^{2+\varepsilon}\), rather than the full ambient
\(m\)-length \(T^{5/2}\).  Thus the incidence energy recovers exactly the
half-power hidden by a scalar triangle inequality.  It does not by itself
prove (9.250): lifting the rational phase from the reduced modulus
\(q\asymp T^{5/2}\) to the full modulus \(s\asymp T^3\) changes the
large-sieve conductor, and a valid theorem must exploit (9.251)
simultaneously with that lift.  Treating \(\nu\) as an arbitrary
divisor-bounded sequence would not do so.

The \(k\)-aspect of Young's multiplicative main theorem does not provide
that missing interface.  In its definition, \(k\) is fixed and the norm
sums over every Dirichlet character \(\theta\pmod k\), while \(q\) is
the varying primitive conductor; the bound is \(Q^2kT+N\).  Formula
(9.250) has no \(\theta\)-family, and its divisor \(g\) varies jointly
with \(s,m\).  Moreover, Young's stated additive Theorem 1.2 specializes
to \(k=T=1\); the following sentence mentions analogous hybrid bounds
but does not state a variable-\(k\) average.  Hence the fixed-\(k\)
factor cannot be identified with the sum over \(g\), and
\(Q^2k+N\) is not a published bound for (9.250).

Nor does Fourier-separating the near window and then applying
Bettin--Chandee close (9.245).  The most favorable resulting trilinear
scales are

\[
 M=T^3,qquad N=T^{5/2},qquad A=T^{9/2}.
\tag{9.252}
\]

If \(T^\xi\) is the residual cost in the scalar part of the modulus
coefficient, the three coefficient norms have total exponent
\(5+\xi\).  The two parenthetical exponents in Bettin--Chandee Theorem 1
are, exactly,

\[
 \frac7{20}(3+5/2+9/2)+\frac14\max(3,5/2)=\frac{17}{4},
 \qquad
 \frac38(3+5/2+9/2)
  +\frac18(9/2+3)=\frac{75}{16},
\tag{9.253}
\]

and the large-phase penalty vanishes.  Consequently this route gives

\[
 \boxed{E_{\rm BC}^{\rm near}=\frac{37}{4}+\xi.}
\tag{9.254}
\]

Even granting the unrealistically favorable \(\xi=0\), this is
\(T^{1/4}\) above the second-moment target \(T^9\); the trivial scalar
norm \(\xi=1/2\) leaves \(T^{3/4}\).  Thus a successful use of the near
determinant must put the restriction \(|bck-gq|\leq T^2\) inside the
operator estimate.  Merely Fourier-separating it into admissible
coefficients and invoking the published trilinear fraction theorem loses
its density and cannot close the gate.

The determinant restriction itself has a further exact affine
parametrization.  Put \(B=bc\) and assume \((B,g)=1\).  Choose the unique
\(q_0\in\{1,\ldots,B-1\}\) satisfying
\(gq_0\equiv-d\pmod B\), and set
\(k_0=(d+gq_0)/B\).  Then every positive solution of
\(Bk-gq=d\) lies on

\[
 \boxed{q=q_0+Bt,\qquad k=k_0+gt.}
\tag{9.255}
\]

At the balanced cutoff, the \(t\)-interval has length
\(Q/B=T^2\), the same exponent as \(|d|\).  Moreover \((B,d)=1\), so
\(t\mapsto q_0+Bt\pmod d\) permutes all residues modulo \(d\).  Additive
reciprocity gives, with the exact archimedean factor retained,

\[
 \boxed{
 e_q(-A\bar d_q)=e_d(A\bar q_d)e(-A/(dq)).}
\tag{9.256}
\]

Consequently the unweighted complete reciprocal core is elementary:

\[
 \boxed{
 \sum_{t\bmod d\atop(q_0+Bt,d)=1}
 e_d\!\left(A\overline{q_0+Bt}_d\right)=c_d(A).}
\tag{9.257}
\]

The checker verifies (9.255)--(9.257), including negative \(A\), for
all coprime small \(B,g,d\) in its deterministic range.  Thus the
unweighted near-determinant core is not an unknown Weil-size sum.  The
actual residual is the affine Möbius--inverse packet

\[
\boxed{
 \sum_{t\asymp d}
 \mu(q_0+Bt)
 W_{B,g,d,A}(t)
 e_d\!\left(A\overline{q_0+Bt}_d\right),}
\tag{9.258}
\]

where \(B=T^{1/2}\), \(d=T^2\), and
\(q_0+Bt\asymp T^{5/2}\); the smooth factor in (9.256) is part of
\(W\).  This is strictly more structured than a generic two-modulus
coupled kernel.  It is not covered by the one-variable trace theorems
above: \(t\mapsto\mu(q_0+Bt)\) is not a multiplicative coefficient.
Equivalently, detecting \(q\equiv q_0\pmod B\) converts (9.258) to
inverse-plus-linear phases modulo \(Bd\asymp T^{5/2}\), where the
matching composite-modulus theorem in Section 9.8 supplies only
logarithmic saving.  A successful estimate must average (9.258) over
\(B,g,d\) and the product coefficient \(A=h\delta_0\), rather than apply
that theorem termwise.

### 9.40 Complete affine periods and the partially fixed-modulus theorem

There is an exact Parseval identity behind (9.258), but it must be used
with the product structure rather than with an arbitrary numerator
sequence.  For coefficients \(x_t\), put

\[
 F_{B,g,d}(a)=
 \sum_{t\bmod d\atop(q_0+Bt,d)=1}
 x_t e_d\!\left(a\overline{q_0+Bt}_d\right).
\]

Since \(t\mapsto q_0+Bt\pmod d\) is a permutation and inversion is a
permutation of the reduced residue classes,

\[
 \boxed{
 \sum_{a\bmod d}|F_{B,g,d}(a)|^2
 =d\sum_{t\bmod d\atop(q_0+Bt,d)=1}|x_t|^2.}
\tag{9.259}
\]

This keeps every nonunit boundary exactly: coefficients for which
\((q_0+Bt,d)>1\) occur on neither side.  The checker verifies (9.259)
for arbitrary deterministic complex coefficient vectors in its finite
range.

For comparison, let

\[
 \rho_{H,L}(n)=\#\{(h,\delta):h\leq H,\delta\leq L,h\delta=n\},
 \qquad
 \Gamma_d(a)=\sum_{n\equiv a\pmod d}\rho_{H,L}(n).
\]

Cauchy inside each residue class gives the boundary-exact finite
majorant

\[
 \boxed{
 \sum_{a\bmod d}\Gamma_d(a)^2
 \leq
 \left\lceil\frac{HL}{d}\right\rceil
 \sum_{n\leq HL}\rho_{H,L}(n)^2.}
\tag{9.260}
\]

At \(H=T^{5/2},L=d=T^2\), the right side has exponent \(7\), up to
divisor powers.  Combining (9.259) and (9.260) by Cauchy gives exponent
\((7+4)/2=11/2\) for a fixed \(B,g,d\).  This is a valid local bound,
but summing it over \(B,g,d\) independently throws away the determinant
geometry and does not prove the \(T^9\) dispersion target.

The large component in (9.260) is in fact orthogonal to the reciprocal
transform.  More precisely, every frequency
\(\overline{q_0+Bt}_d\) in (9.259) is a unit.  If \(d\mid L\), complete
\(\delta\)-periods therefore give, for every \((u,d)=1\),

\[
 \boxed{
 \sum_{h\leq H}\sum_{\delta\leq L}e_d(hu\delta)
 =L\left\lfloor\frac Hd\right\rfloor.}
\tag{9.261}
\]

Consequently the complete-period portion of the affine packet collapses
without an inequality:

\[
 \boxed{
 \sum_{t\bmod d\atop(q_0+Bt,d)=1}x_t
 \sum_{h\leq H}\sum_{\delta\leq L}
 e_d\!\left(h\delta\overline{q_0+Bt}_d\right)
 =L\left\lfloor\frac Hd\right\rfloor
 \sum_{t\bmod d\atop(q_0+Bt,d)=1}x_t.}
\tag{9.262}
\]

Thus the complete-period core is an affine-progression Mertens sum, not
a generic Möbius--trace sum.  Prefix differences give the same exact
statement for unweighted translated intervals.  In the actual packet,
however, the dyadic endpoints and the smooth factor
\(e(-h\delta/(dq))\) leave incomplete periods.  Smooth completion in
\(\delta\) replaces those periods by bounded dual modes satisfying
\(h\equiv nq\pmod d\); controlling these endpoint modes simultaneously
over \(B,g,d\) is still required.  Equations (9.259)--(9.262) isolate
that requirement and do not assert cancellation in an affine Möbius
progression.

A new theorem of Wright on trilinear Kloosterman fractions with a fixed
factor in the denominator is close enough to warrant a literal exponent
audit.  Reciprocity gives

\[
 e_q(-A\overline{Bk}_q)
 =e_{Bk}(A\bar q_{Bk})e(-A/(Bkq)),
\tag{9.263}
\]

so after Fourier-separating the near-determinant window his theorem has

\[
 M=Q=T^{5/2},\qquad N=K=T^{5/2},\qquad
 R=B=T^{1/2},\qquad A=T^{9/2}.
\tag{9.264}
\]

The three coefficient norms and the factor \((AMN)^{1/2}\) both have
exponent \(19/4\), while \(R^{1/4}\) contributes \(1/8\).  The five
terms in the parenthesis in the stated theorem have exponents

\[
 -\frac5{16},\quad-\frac14,\quad-\frac{17}{40},
 \quad-\frac45,\quad-\frac5{16}.
\tag{9.265}
\]

Here the third entry uses the weaker \(A^{-1/20}\) printed in the theorem
statement; a stronger power appears later in its proof, but the maximum
in (9.265) is unchanged.  The fixed-\(B,g\) block is therefore

\[
 \frac{19}{4}+\frac{19}{4}+\frac18-\frac14=\frac{75}{8}.
\tag{9.266}
\]

The theorem contains no average over the two remaining \(T^{1/2}\)
short coordinates.  Direct triangle summation over \(B\) and \(g\)
raises (9.266) to \(83/8\), which is \(11/8\) above the second-moment
target \(9\).  Hence the partially fixed-modulus theorem does not close
(9.245) after the near window has been separated.  Its mechanism may
still be relevant inside a future joint \(B,g\) operator, but that
operator is not part of the published statement.  The executable ledger
checks every fraction in (9.264)--(9.266).

The incomplete periods also have an exact smooth dual description.  Use
the Fourier convention
\(\widehat V(\xi)=\int_{\mathbb R}V(x)e(-\xi x)\,dx\), and absorb the
archimedean factor into

\[
 V_{h,q,d}(x)=W_\delta(x)e\!\left(-\frac{hLx}{dq}\right).
\]

Poisson summation in residue classes modulo \(d\) gives

\[
\boxed{
\begin{aligned}
 &\sum_{\delta\in\mathbb Z}W_\delta(\delta/L)
 e_d(h\delta\bar q_d)e(-h\delta/(dq))\\
 &\qquad=L
 \sum_{n\in\mathbb Z\atop n\equiv-h\bar q_d\ ({\rm mod}\ d)}
 \widehat V_{h,q,d}\!\left(\frac{Ln}{d}\right).
\end{aligned}}
\tag{9.267}
\]

At the transition scale,
\(hL/(dq)\asymp1\), so all derivatives of \(V_{h,q,d}\) are uniform.
Consequently (9.267) is negligible to arbitrary power unless
\(|n|\ll T^\varepsilon d/L\ll T^\varepsilon\).  Its congruence is
equivalent to

\[
 h+nq=jd.
\]

Combining this with (9.255) puts every surviving endpoint mode on the
two-dimensional affine lattice

\[
\boxed{
\begin{aligned}
 q&=q_0+Bt,& k&=k_0+gt,\\
 h&=jd-n(q_0+Bt),&
 Bk-gq&=d,\qquad h+nq=jd.
\end{aligned}}
\tag{9.268}
\]

Here \(t\) has exponent \(2\), \(|j|\ll T^{1/2+\varepsilon}\), and
\(|n|\ll T^\varepsilon\).  Thus the endpoint is not a five-variable
generic trace sum: it is a bounded union of two-dimensional affine
Möbius packets.  The finite checker verifies both equations in (9.268),
including negative \(n,j,h\), for all coprime small inputs in its range.

There is a useful but insufficient character screening of this lattice.
Because \(q_0\equiv-d\bar g\pmod B\), multiplicative orthogonality gives
the exact identity

\[
\boxed{
 1_{B\mid gq+d}
 =\frac1{\varphi(B)}
  \sum_{\chi\ ({\rm mod}\ B)}
  \chi(-gq)\overline{\chi(d)},}
\tag{9.269}
\]

on the unit support already present in (9.242).  Write the exponents of
\(B,g,q\) as \(\beta,\gamma,\lambda\).  Progression density makes the
raw \(B,g,q\) exponent

\[
 \beta+\gamma+(\lambda-\beta)=\gamma+\lambda.
\]

Therefore Bombieri--Vinogradov applied after fixing \(g,d\) changes only
logarithms: its sum over \(B\) has the same power exponent \(\lambda\)
as the progression volume.  It does not supply the missing scalar
half-power.

Even an optimistic primitive-character treatment, after separately
removing the principal and induced spectra, still stops short.  The
ordinary multiplicative large sieve gives the two normalized character
energies

\[
\begin{aligned}
 E_g&=-\beta+\max(2\beta,\gamma)+\gamma,\\
 E_q&=-\beta+\max(2\beta,\lambda)+\lambda.
\end{aligned}
\tag{9.270}
\]

At \((\beta,\gamma,\lambda)=(1/2,1/2,5/2)\), these are \(1\) and
\(9/2\).  Character Cauchy therefore has exponent \(11/4\), saving only
\(1/4\) from the raw exponent \(3\).  The scalar-aware transition needs
saving \(1/2\), so this route still misses by \(1/4\).

The exact long-character mean square that would fill this screening gap
is

\[
\boxed{
 \sum_{B\asymp T^{1/2}}\frac1{\varphi(B)}
 \sum_{\chi\ ({\rm mod}\ B)}^{*}
 \left|\sum_{q\asymp T^{5/2}}
 \mu(q)\chi(q)W_q(q/T^{5/2})\right|^2
 \ll_\varepsilon T^{4+\varepsilon}.}
\tag{9.271}
\]

The ordinary primitive large sieve gives \(T^{9/2+\varepsilon}\);
the diagonal scale is only \(T^{3+\varepsilon}\).  Thus (9.271) asks for
an intermediate factor \(T^{1/2}\), not square-root cancellation.
Nevertheless, neither the first-moment Bombieri--Vinogradov theorem nor
the published one-variable Möbius--trace estimates cited below imply
(9.271).  Moreover (9.271) is only the character core of the endpoint
problem: a complete proof must retain the smooth lattice relation
\(h+nq=jd\), the \(d\)-average, and the principal/induced recombination.
It is recorded as an exact quantitative target, not as a proved
replacement for the coupled-kernel gate.

The principal spectrum cannot be bounded away by an elementary
Selberg-sieve Euler product.  If the congruence attached to each
\(B=bc\) in (9.241) is replaced by its principal density
\(1/\varphi(B)\), the exact two-cutoff coefficient is

\[
\boxed{
\begin{aligned}
 \mathcal P_{U,V}(r)
={}&-\sum_{bc\mid r\atop b\leq U,\ c\leq V}
 \frac{\mu(b)\mu(c)}{\varphi(bc)}\\
 &+\sum_{bc\mid r\atop b>U,\ c>V}
 \frac{\mu(b)\mu(c)}{\varphi(bc)}.
\end{aligned}}
\tag{9.272}
\]

For every prime \(p>\max(U,V)\), the only admissible divisor pair is
\((b,c)=(1,1)\), and hence

\[
 \boxed{\mathcal P_{U,V}(p)=-1.}
\]

This is a finite obstruction, not merely an exponent heuristic.  In
particular, no pointwise estimate
\(\mathcal P_{U,V}(r)\ll r^{-\delta}\), and no power saving obtained by
taking absolute values of the principal Euler product, can hold
uniformly.  The \(B=1\) prime slice has no nonprincipal character with
which to cancel.  A successful argument must therefore retain the
outer Möbius weights and the endpoint phase on this slice, or recombine
it with the already centered principal/axis terms before the Type-I/II
character separation.  The checker verifies (9.272) exactly as a
rational number and verifies \(\mathcal P_{U,V}(p)=-1\) for every tested
prime above unequal cutoffs.

The inverse phase does remain on the prime slice, so estimates for
Kloosterman sums over primes are a more relevant published input than an
absolute sieve.  If \(r=s+d\) is prime, then \(d\equiv r\pmod q\), and

\[
 e_q(-h\delta_0\bar d_q)=e_q(-h\delta_0\bar r_q).
\]

Irving's Theorem 1 bounds
\(\sum_{q\asymp Q}\max_a|\sum_{p\asymp x}e_q(a\bar p)|\) by the sum of
three terms with exponents

\[
 \frac54Q+\frac58x,\qquad
 Q+\frac9{10}x,\qquad
 \frac76Q+\frac{13}{18}x,
\]

in exponent notation, for \(Q^{2/3}\leq x\leq Q^{3/2}\).  On the
present full dyadic scales \(Q=T^{5/2},x=T^3\), this gives

\[
\boxed{
 \max\!\left(5,\frac{26}{5},\frac{61}{12}\right)
 =\frac{26}{5},\qquad
 E_{\rm trivial}=\frac{11}{2}.}
\tag{9.273}
\]

Thus even the full-prime-interval theorem saves only \(3/10\), short of
the missing scalar \(1/2\) by \(1/5\).  The actual moving
\(d\)-window has length \(T^2\) around height \(T^3\), whereas the
theorem uses \(p\asymp x\).  Even granting an unproved translated
short-interval version and optimistically substituting \(x=T^2\), its
three exponents are \(35/8,43/10,157/36\); the saving over \(9/2\) is
only \(1/8\).  Finally, the theorem takes a maximum over one fixed
numerator \(a\), not a joint \(h\delta_0\)-moment.  Summing the product
numerators termwise would discard all of their energy.  Hence the
published prime-Kloosterman estimate does not control the \(B=1\) prime
slice, even before that additional product loss.  The executable ledger
checks every fraction in (9.273) and in the optimistic short-window
substitution.

### 9.41 Selberg variance does not remove the prime-density mode

There is a tempting further reduction on the \(B=1\) prime slice: replace
the prime weight by its centered version
\(\Lambda(s+d)-1\), and estimate its short-interval variance before the
outer \(s\)-sum.  This must not be confused with the exact Ramanujan
centering in (9.228)--(9.231).  That earlier identity centers residue
classes in the numerator variables modulo \(t\); it contains no identity
which replaces \(\Lambda(s+d)\) by \(\Lambda(s+d)-1\).

The most favorable scalar exponent audit already shows the limitation.
Put \(X=T^3\), \(Y=T^2\), and \(\vartheta=Y/X=T^{-1}\).  If the outer
coefficients have second moment \(O(XT^\varepsilon)\), Cauchy reduces the
centered scalar model to the multiplicative Selberg integral

\[
 J(X,\vartheta)
 =\int_X^{2X}
 \left|\psi(t+\vartheta t)-\psi(t)-\vartheta t\right|^2dt.
\]

The unconditional input recorded by Languasco--Perelli--Zaccagnini in
this range is, up to logarithms or a little-\(o\) improvement,
\(J(X,\vartheta)\ll X^3\vartheta^2=XY^2\).  Hence

\[
 \boxed{
  J(X,Y/X)\ll T^{7+\varepsilon},\qquad
  X^{1/2}J(X,Y/X)^{1/2}\ll T^{5+\varepsilon}.}
\tag{9.274}
\]

The right side is exactly the trivial \(XY=T^5\) exponent and remains
\(T^{1/2}\) above the required \(T^{9/2+\varepsilon}\).  Thus the
unconditional almost-all short-interval theorem supplies no power saving
for this transition.  It is not legitimate to insert the conjectural
variance \(J\ll XYT^\varepsilon\).  Selberg's RH estimate does have that
power scale (with logarithms), and would give only the diagnostic

\[
 \boxed{J(X,Y/X)\ll_{\rm RH}T^{5+\varepsilon},\qquad
 X^{1/2}J^{1/2}\ll_{\rm RH}T^{4+\varepsilon},}
\tag{9.275}
\]

which lies \(T^{1/2}\) below the target but is not an unconditional input.
The actual packet also retains inverse phases and product-numerator
weights, so (9.274) is an optimistic screening calculation, not an
estimate for the full prime slice.

Centering also creates a separate density term.  Even in the stripped
unweighted projection it is

\[
 Y\sum_{s\asymp X}\mu(s)W(s/X).
\]

To place this below \(T^{9/2+\varepsilon}\) requires

\[
 \boxed{
  \sum_{s\asymp T^3}\mu(s)W(s/T^3)
  \ll T^{5/2+\varepsilon}=X^{5/6+\varepsilon}.}
\tag{9.276}
\]

This is a fixed \(T^{1/2}\) Mertens power saving.  The standard
zero-free region gives no fixed power, and the actual divisor-incidence
coefficient in (9.250) is more structured rather than absent.  No term
in (9.228)--(9.231) cancels (9.276): those formulas concern a different
additive zero mode.  Consequently a prime-density centering argument
must either prove an exact recombination with another original axis term
before separation, or retain the outer Möbius sum and the inverse/product
phase jointly.  Merely quoting an almost-all primes-in-short-intervals
theorem does not weaken the current coupled gate.  The executable ledger
checks every exponent and the exact required Mertens ratio \(5/6\).

### 9.42 Direct averaged Möbius-on-shifted-primes theorem

Lichtman's averaged shifted-prime theorem is closer to the signed scalar
projection than the Selberg-variance route because it treats the Möbius
and prime weights jointly.  Up to endpoint strips, the change of variables

\[
 h=Y-d,\qquad n=s+d-Y
\]

maps
\(\mu(s)\Lambda(s+d)\) to
\(\mu(n+h)G(n)\) with the single shift-independent coefficient
\(G(n)=\Lambda(n+Y)\).  Its second moment is
\(\sum_{n\asymp X}|G(n)|^2\ll X\log X\), so the theorem's moderate-growth
hypothesis is satisfied.  Restricting all shifts to a common \(n\)-interval
loses endpoint strips of total size \(O(Y^2\log X)=T^{4+o(1)}\), already
below the \(T^{9/2+\varepsilon}\) target.

For \(Y=X^{2/3}\), the quantitative specialization with one Möbius and
one von Mangoldt factor gives, for every fixed \(\delta>0\),

\[
\boxed{
 \sum_{d\leq Y}
 \left|\sum_{s\asymp X}\mu(s)\Lambda(s+d)\right|
 \ll_\delta
 \frac{XY}{(\log X)^{1/3-\delta}}
 +O(Y^2\log X).}
\tag{9.277}
\]

Thus (9.277) proves genuine cancellation and avoids separating the
density term (9.276), but its \(T\)-power exponent is still
\(3+2=5\).  It supplies no fixed power saving, whereas the scalar
transition requires \(T^{1/2}\), so the exact remaining power gap is
\(1/2\).  More importantly, the theorem requires the coefficient
\(G(n)\) to be fixed across the shift average.  The actual packet has a
\(d\)-dependent reciprocal phase, the joint product numerator
\(h\delta_0\), and divisor-incidence weights.  These cannot be inserted
as an arbitrary \(G_d(n)\) into the published statement.  Hence
(9.277) is a rigorous coverage result for the stripped signed prime
projection and a no-coverage certificate for the transition gate, not
an estimate for (9.239).

### 9.43 Completing the transition numerator before separating Möbius

The product numerator in (9.239) can be removed exactly at the
transition scale.  For fixed \(g,q,d,\delta_0\), put

\[
 W_{g,q,d,\delta_0}(x)
 :=\Omega(g,q,d,Hx,\delta_0),
\]

including in \(W\) every already retained archimedean factor depending
on \(h\).  With
\(\widehat W(\xi)=\int_{\mathbb R}W(x)e(-\xi x)\,dx\), ordinary Poisson
summation gives the boundary-exact identity

\[
\boxed{
 \sum_{h\in\mathbb Z}
 \Omega(g,q,d,h,\delta_0)e_q(-h\delta_0\bar d_q)
 =
 H\sum_{\ell\in\mathbb Z\atop
        \ell\equiv\delta_0\bar d_q\ ({\rm mod}\ q)}
 \widehat W_{g,q,d,\delta_0}\!\left(\frac{H\ell}{q}\right).}
\tag{9.278}
\]

The localized weights are uniformly inert in \(h/H\), including the
factor \(e(-h\delta_0/(dq))\), whose logarithmic derivative is \(O(1)\)
at the transition.  Repeated integration by parts therefore restricts
(9.278), with an arbitrary power error, to

\[
 |\ell|\ll T^\varepsilon q/H\ll T^\varepsilon.
\]

The congruence in (9.278) is
\(\delta_0\equiv\ell d\pmod q\).  Since
\(\delta_0,|d|\asymp T^2\), \(q\asymp T^{5/2}\), and
\(|\ell|\ll T^\varepsilon\), choosing the truncation exponent below
\(1/2\) gives
\[
 q>\delta_0+|\ell d|.
\]
There is then only one integer representative:

\[
\boxed{\delta_0=\ell d.}
\tag{9.279}
\]

This includes both signs of \(d\): \(\ell\) has the sign which makes
\(\ell d>0\).  The finite checker verifies the general lemma that
\(\delta_0\equiv\ell d\pmod q\) and
\(q>\delta_0+|\ell d|\) force (9.279), for positive \(\delta_0,q\)
and either sign of the nonzero unit \(d\).

Substitution in (9.239) eliminates the \(\delta_0\)-sum:

\[
\boxed{
 \mathfrak P[\Omega]
 =
 H\sum_{0<|\ell|\ll T^\varepsilon}
 \sum_{g\asymp G}\mu(g)
 \sum_{q\asymp Q\atop(g,q)=1}\mu(q)
 \sum_{d\in I(gq)\atop(d,gq)=1}
 \mu(gq+d)\,\Xi_\ell(g,q,d)
 +O_A(T^{-A}),}
\tag{9.280}
\]

after increasing \(A\) to absorb the polynomial number of original
terms.  Here \(\Xi_\ell\) is the Fourier-transformed inert weight with
the exact condition that \(\ell d\) lies in the original
\(\delta_0\)-interval.  No inverse phase or arbitrary product
coefficient remains.

The exponent ledger agrees exactly with, and explains, the scalar-aware
Young endpoint.  The raw exponent is \(23/2\); deleting the
\(\delta_0\)-length saves \(2\), while \(q/H\) has exponent zero:

\[
\boxed{
 \frac{23}{2}-2=\frac{19}{2},
 \qquad
 \frac{19}{2}-9=\frac12.}
\tag{9.281}
\]

Thus completing \(h\) recovers Young's full two-power saving but does
not by itself recover the remaining scalar half-power.  After removing
the common factors already accounted for in (9.281), a sufficient
three-variable core estimate is

\[
\boxed{
 \sum_{g\asymp T^{1/2}}\mu(g)
 \sum_{q\asymp T^{5/2}}\mu(q)
 \sum_{d\asymp T^2}\mu(gq+d)\Xi_\ell(g,q,d)
 \ll_\varepsilon T^{9/2+\varepsilon}}
\tag{9.282}
\]

uniformly for the separated inert weights and bounded dual modes in
(9.280).  Its absolute exponent is \(5\), so (9.282) asks for exactly
\(T^{1/2}\).  With \(s=gq\), \(S=T^3\), and \(D=S^{2/3}\), its
separated model is a divisor-incidence weighted averaged-Chowla bound
of size \(S^{3/2+\varepsilon}\), rather than the
\(S^{5/3-o(1)}\) scale supplied by published logarithmic-cancellation
theorems.  Equivalently, the required relative saving is
\(S^{-1/6}=T^{-1/2}\).

There are two different Fourier variables here.  The nonzero
\(\ell\) in (9.278) is dual to the product numerator \(h\).  The circle
variable \(\alpha\) used to analyze the remaining \(d\)-shift
correlation is dual to \(d\).  Formula (9.279) does not force that
\(\alpha\) lies on minor arcs, and the \(\alpha=0\) component of the
weighted correlation is generally still present.  Consequently the
classical \(S^{4/5+\varepsilon}\) minor-arc bound for a Möbius
exponential sum, although numerically stronger than the required
\(S^{5/6+\varepsilon}\), cannot yet be applied to the whole of
(9.282).  A valid closure must prove that the original principal/axis
recombination cancels those \(d\)-major arcs, or estimate them jointly
with the structured divisor-incidence coefficient.

Known one-variable Möbius--trace results do not close (9.239) or its
recombined form (9.250).  Even if
one optimistically grants a translated prime-modulus version of the
Fouvry--Kowalski--Michel smoothed estimate at \(D=q^{4/5}\), it saves
only \(q^{-1/120+o(1)}\): its factor is
\((q/D)^{1/6}q^{-1/24}=q^{-1/120}\).  The missing scalar cost is
\(T^{1/2}=q^{1/5}\).  Korolev--Shparlinski reaches intervals longer than
\(q^{1/2+\varepsilon}\), but only with logarithmic saving, and both
statements are prime-modulus results whereas (9.239) averages squarefree
composite \(q\); the actual moving interval is an additional mismatch.
Hence neither theorem supplies the required power or the composite-modulus
aggregation.  The remaining analytic task is
precisely to estimate (9.239) for \(0\leq\tau<1/4\) before taking an
absolute value over \(g\); no unconditional closure is claimed.

### 9.44 Transporting the centering through numerator completion

The centering from (9.197) can be carried through the completion in
Section 9.43 exactly.  It does not, however, turn the surviving
\(d\)-weight into an additive minor-arc weight.  Recall

\[
 \mathscr E_{q,A}(x)=e_q(A\bar x_q)-\frac{c_q(A)}{\varphi(q)}.
\]

For \((d\delta_0,q)=1\), formula (9.221), with the sign of the numerator
retained, gives

\[
\boxed{
 \sum_{h\bmod q}\mathscr E_{q,-h\delta_0}(d)e_q(-\ell h)
 =q\,1_{(\ell,q)=1}
 \left(
  1_{\delta_0\equiv-\ell d\ ({\rm mod}\ q)}
  -\frac1{\varphi(q)}
 \right).}
\tag{9.283}
\]

Changing \(\ell\) to \(-\ell\) makes the point-mass condition identical
to (9.279).  Smooth Poisson summation merely weights the bounded values of
\(\ell\); it does not change the point-minus-uniform bracket in (9.283).
The point term is the dilation packet in (9.280), whereas the uniform
term is a Ramanujan marginal of the type already bounded in
(9.228)--(9.229).  Thus the latter may be estimated separately, but it
cannot be declared an equal-size cancellation of the former.

There is a finite short-box certificate for this mismatch.  Put

\[
 U_q(D)=\#\{1\leq d\leq D:(d,q)=1\},\qquad 1\leq D<q.
\]

Since \(d\equiv\delta\pmod q\) is then literal equality on
\([1,D]^2\), summing the normalized bracket in (9.283), with the signs
aligned and \(\ell=1\), gives

\[
\boxed{
 \sum_{\substack{d,\delta\leq D\\(d\delta,q)=1}}
 \left(1_{\delta\equiv d\ ({\rm mod}\ q)}
       -\frac1{\varphi(q)}\right)
 =U_q(D)-\frac{U_q(D)^2}{\varphi(q)}.}
\tag{9.284}
\]

In particular, if \(q\) is prime and \(D<q\), then

\[
 \boxed{\mathcal C_q(D)=D-\frac{D^2}{q-1}.}
\tag{9.285}
\]

For \(D\leq(q-1)/2\), this is at least \(D/2\), so the short-box
centered mass is not zero.  At the transition scales

\[
 q=T^{5/2},\qquad D=T^2,
\]

the point mass has normalized exponent \(2\), the uniform background
has exponent \(2+2-5/2=3/2\), and

\[
\boxed{
 E_{\rm point}-E_{\rm uniform}=\frac12.}
\tag{9.286}
\]

This is exactly the scalar half-power left in (9.281).  Formula (9.284)
is a counterexample to a *universal algebraic vanishing-moment claim*;
it is not asserted as a lower bound for the particular signed smooth
weight \(\Xi_\ell\).  What it proves is that (9.167)--(9.179) and the
Ramanujan centering alone do not imply
\(\sum_d\Xi_\ell(g,q,d)=0\), nor do they remove the \(d\)-major arcs.

The closest short-interval Möbius theorems do not supply the missing
power.  Matomäki--Radziwiłł--Tao's averaged Chowla estimate has decay of
rough order \(\log\log D/\log D\).  The later average Fourier-uniformity
theorems give \(o(1)\), not a fixed power.  The all-interval theorem of
Matomäki--Shao--Tao--Teräväinen gives, for \(D\geq
S^{5/8+\varepsilon}\), arbitrary fixed log-power saving for a Möbius
sum against a fixed nilsequence.  Our \(D=S^{2/3}\) is in that range,
but even the direct specialization

\[
 \sum_{S<n\leq S+D}\mu(n)F(n)
 \ll_A D(\log S)^{-A}
\]

costs \(SD(\log S)^{-A}=T^5(\log T)^{-A}\) after the outer
\((g,q)\)-count.  It does not reach \(T^{9/2+\varepsilon}\), and its
fixed nilsequence does not encode the jointly varying divisor-incidence
weight.  Therefore the weakest currently isolated analytic input remains
the weighted averaged-Chowla power estimate (9.282), including its
central major arc.  A classical minor-arc estimate cannot be applied to
the whole packet unless an additional, weight-specific vanishing identity
is proved; none follows from the exact centering.

### 9.45 The actual archimedean weight has no power-frequency reserve

It remains logically possible that the particular weight inherited from
the AFE has an accidental zero moment even though the centered finite
algebra does not force one.  The exact normalization (5.13a)--(5.13b)
shows, however, that no such saving can come from nonstationary phase or
integration by parts at the transition corner.  There

\[
 R=S=T^3,\qquad M=K=T^{1/2},\qquad L=H=T^{5/2},
\]

and every dimensionless parameter in the original coupled kernel has
power exponent zero:

\[
\boxed{
 T\lambda_0=\frac{TL}{MR}\asymp1,\qquad
 \omega_0=\frac{HM}{S}\asymp1,\qquad
 \chi_0=\frac{M^2R}{ST}\asymp1,\qquad
 \frac{KS}{MR}\asymp1.}
\tag{9.287}
\]

The scalar transition and the new Poisson sample are on the same fixed
scale.  With \(g=T^{1/2}\), \(D=T^2\), \(L=gD\), and
\(q=H=T^{5/2}\), one also has

\[
\boxed{
 \frac{g\delta_0}{L}\asymp1,
 \qquad \frac Hq\asymp1,
 \qquad
 \frac{g(\ell d)}L
 =\ell\frac gG\frac dD=O(T^\varepsilon).}
\tag{9.288}
\]

Consequently \(\Xi_\ell\) is a bounded-frequency Fourier coefficient of
a fixed-scale smooth function of \(d/D\), up to the already allowed
\(T^\varepsilon\) seminorms.  Repeated integration by parts therefore
produces no negative power of \(T\).  The executable ledger evaluates the
six exponents in (9.287)--(9.288) exactly and obtains zero in every entry.

The zeros of \(G_t(z)\) at \(z=\pm1/2\) do not alter this conclusion.
They are zeros in the AFE Mellin variable and were used to remove the
boundary pole in the **zero Poisson mode** in Section 4.  They are not
zeros of the bounded nonzero \(h\)-Fourier coefficient in (9.278), and
they do not imply a zero \(d\)-Fourier coefficient.  A weight-specific
escape would therefore require a new exact identity such as

\[
\boxed{
 \mathcal Z_\ell(g,q)
 :=\int_{\mathbb R}\Xi_\ell(g,q,Dx)\,dx=0,}
\tag{9.289}
\]

after all dyadic pieces and principal/centered corrections are recombined.
No such identity is proved here, and even (9.289) alone would address only
the additive origin, not every small-denominator major arc.  Thus the
actual archimedean scale rules out a power saving by analytic
nonstationarity; the surviving half-power must come from an exact global
recombination not yet found or from arithmetic cancellation in (9.282).

### 9.46 Recombining the scalar sign after numerator completion

Once the inverse phase and the \(\delta_0\)-sum have disappeared, the
short scalar sign is no longer an independent source of cancellation.
For one separated component of \(\Xi_\ell\), write its \((g,q,d)\)-weight
as \(X_g(g)X_q(q)X_d(d)\), and define

\[
 \boxed{
 \omega_{G,Q}(s)
 :=\sum_{g\mid s\atop g\asymp G,\ s/g\asymp Q}
 X_g(g)X_q(s/g).}
\tag{9.290}
\]

The coprimality already in (9.280) and squarefreeness give, term by term,

\[
 \mu(g)\mu(q)=\mu(gq)=\mu(s).
\]

Therefore the completed scalar core has the boundary-exact identity

\[
\boxed{
\begin{aligned}
 &\sum_{g\asymp G}\mu(g)X_g(g)
  \sum_{q\asymp Q\atop(g,q)=1}\mu(q)X_q(q)
  \sum_{d\in I(gq)\atop(d,gq)=1}
       \mu(gq+d)X_d(d)\\
 &\qquad=
 \sum_{s\asymp S}\mu(s)\omega_{G,Q}(s)
 \sum_{d\in I(s)\atop(d,s)=1}\mu(s+d)X_d(d).
\end{aligned}}
\tag{9.291}
\]

No endpoint was changed: \(I(s)=(R-s,2R-s]\) is the same moving interval.
The executable checker proves the finite weighted sign identity for every
squarefree \(s\leq60\), arbitrary complex weights on any selected divisor
family, and positive or negative unit shifts.  In particular, a later
triangle inequality over \(g\) cannot be justified as “using the third
Möbius sign”; after completion that sign has merged into \(\mu(s)\).

The new coefficient has the elementary norm

\[
 |\omega_{G,Q}(s)|\ll\tau(s),\qquad
 \sum_{s\asymp S}|\mu(s)\omega_{G,Q}(s)|^2
 \ll_A S(\log S)^A
\tag{9.292}
\]

for some fixed \(A\), uniformly for bounded separated weights.  Thus the
right side of (9.291), after the exact expansion
\(1_{(s,d)=1}=\sum_{j\mid(s,d)}\mu(j)\), is a sum of
arbitrary-coefficient shifted Möbius forms in Lichtman's Fourier lemma and
Theorem 6.2.  On the \(j\)-layer write \(s=jn,d=jh\); its raw density is
\(SD/j^2\), so summing the divisor layers costs no power, and the fixed
coefficient is the corresponding restriction of
\(G(s)=\mu(s)\omega_{G,Q}(s)\).  The moving smooth endpoints can be
restricted to common intervals with total boundary cost
\(D^2S^\varepsilon=T^{4+\varepsilon}\), as in Section 9.42; alternatively
they may be retained by partial summation.

This exact compatibility does not provide a power.  Lichtman's Lemma 2.1
has the schematic consequence

\[
\boxed{
 \sum_{|d|\leq D}
 \left|\sum_{s\asymp S}G(s)\mu(s+d)\right|
 \ll D^{1/2}
 \left\{F_G(S)\,\mathcal U_\mu(S,D)\right\}^{1/2},}
\tag{9.293}
\]

where \(F_G(S)=\sum_{s\leq2S}|G(s)|^2\) and
\(\mathcal U_\mu\) is the short-interval Fourier-uniformity integral.
The published estimates make (9.293) smaller than \(SD\) by logarithmic
or qualitative factors, subject in Theorem 6.2 to its displayed
exceptional-set term.  Even granting arbitrary fixed log-power decay,
its \(T\)-power ledger remains

\[
 \boxed{SD=T^5,\qquad
  \text{target }S^{3/2}=T^{9/2},\qquad
  \text{gap }T^{1/2}=S^{1/6}.}
\tag{9.294}
\]

For the unseparated actual \(\Xi_\ell\), smooth separation replaces
\(\omega_{G,Q}(s)X_d(d)\) by an integral of such components and incurs
its recorded \(L^1\) separation norm; this cannot turn logarithmic decay
into (9.294)'s fixed power.  Hence (9.291) is a useful positive theorem
match and a negative power audit: the residual is a two-Möbius weighted
averaged-Chowla problem, not a three-independent-sign problem.

### 9.47 The central major arc after the exact Type-I/II split

The zero frequency in the short--short packet can be compared with the
long--long packet without replacing the two-cutoff identity by a formal
infinite convolution.  Group (9.241) by the product \(m=bc\), and put

\[
 \boxed{
 \lambda_{U,V}(m)
 :=\sum_{bc=m}\mu(b)\mu(c)
 \left(1_{b>U,\ c>V}-1_{b\leq U,\ c\leq V}\right).}
 \tag{9.295}
\]

Writing \(\mu_{\leq U}(n)=\mu(n)1_{n\leq U}\), the global
boundary-exact convolution identity is

\[
 \boxed{
 \sum_{m\mid n}\lambda_{U,V}(m)
 =\mu(n)-\mu_{\leq U}(n)-\mu_{\leq V}(n).}
 \tag{9.296}
\]

Indeed, in convolution notation
\(\lambda_{U,V}=\mu*\mu-\mu*\mu_{\leq V}
-\mu_{\leq U}*\mu\), and convolving with \(1\) proves (9.296).
In particular, its left side equals \(\mu(n)\) for every
\(n>\max(U,V)\), exactly as in (9.241), with no truncation error.  It
also shows why the two zero frequencies cannot be cancelled term by
term.  If \(\lambda^{\rm I}\) and
\(\lambda^{\rm II}\) denote the negative short--short and positive
long--long parts, respectively, then

\[
 \boxed{
 \lambda^{\rm II}_{U,V}(m)=0
 \quad(m<(U+1)(V+1)),\qquad
 \lambda^{\rm I}_{U,V}(1)=\lambda_{U,V}(1)=-1.}
 \tag{9.297}
\]

In particular, for a prime \(p>\max(U,V)\), its value
\(\mu(p)=-1\) in (9.296) comes entirely from \(m=1\); the long--long
rectangle has no matching modulus.  Any cancellation of this density
must therefore aggregate different product moduli rather than pair equal
frequencies.

There is a completely finite statement of the aggregate density.  Fix
\(s,M\geq1\), let \(P=[s,1,2,\ldots,M]\), and normalize by the unit
residues in one period.  Chinese remaindering gives

\[
\boxed{
 \frac{1}{\#\{0\leq d<P:(d,s)=1\}}
 \sum_{\substack{0\leq d<P\\(d,s)=1}}
 \sum_{\substack{m\leq M\\m\mid s+d}}\lambda_{U,V}(m)
 =\sum_{\substack{m\leq M\\(m,s)=1}}
   \frac{\lambda_{U,V}(m)}m.}
\tag{9.298}
\]

Indeed, when \((m,s)>1\), the congruence \(d\equiv-s\pmod m\)
contains no unit modulo \(s\); when \((m,s)=1\), it occupies exactly a
\(1/m\)-fraction of the unit residues.  The checker verifies (9.295)--
(9.298) with exact integers and rational numbers.  Thus the relevant
principal coefficient is the finite prefix on the right of (9.298), not
the unsupported substitution \(1/\zeta(1)=0\).

The latter substitution does explain the formal source of a possible
global cancellation.  For \({\rm Re}\,z>1\), set
\(M(z)=\sum_{n\geq1}\mu(n)n^{-z}=1/\zeta(z)\) and
\(M_U(z)=\sum_{n\leq U}\mu(n)n^{-z}\).  Absolute convergence gives

\[
\boxed{
 \sum_{m\geq1}\frac{\lambda_{U,V}(m)}{m^z}
 =(M-M_U)(M-M_V)-M_UM_V
 =M^2-M(M_U+M_V).}
\tag{9.299}
\]

Consequently this Dirichlet series tends to zero as \(z\to1^+\).
This is only Abelian cancellation across the whole product family.  It
does not give a fixed-power estimate for the finite, coprimality-twisted
prefix in (9.298); the classical zero-free region supplies only a
subpower relative saving after Perron inversion.

For the balanced short--short range the nonzero completion modes are
already harmless.  If \(m=bc\leq UV\), \((m,s)=1\), and \(W\) is a
fixed smooth cutoff, Poisson summation gives

\[
 \sum_d W(d/D)1_{m\mid s+d}
 =\frac Dm\widehat W(0)
  +\frac Dm\sum_{k\ne0}e_m(-ks)\widehat W(kD/m).
 \tag{9.300}
\]

The second term is \(\ll_A(m/D)^{A-1}\).  Even with a sharp interval,
the \(O(1)\) error summed over \(s,b,c\) has balanced exponent
\(3+1/4+1/4=7/2\), below the first-moment target \(9/2\).  The only
short--short term at the missing scale is therefore its zero frequency,

\[
\boxed{
 -D\widehat W(0)
 \sum_s\mu(s)\omega_{G,Q}(s)B_U(s)B_V(s),\qquad
 B_U(s):=\sum_{\substack{b\leq U\\(b,s)=1}}\frac{\mu(b)}b.}
\tag{9.301}
\]

For a separated scalar component, expanding \(s=gq\) makes (9.301)
equally explicit:

\[
 -D\widehat W(0)
 \sum_{b\leq U,c\leq V}\frac{\mu(b)\mu(c)}{bc}
 \left(\sum_{\substack{g\asymp G\\(g,bc)=1}}
       \mu(g)X_g(g)\right)
 \left(\sum_{\substack{q\asymp Q\\(q,bc)=1}}
       \mu(q)X_q(q)\right).
 \tag{9.302}
\]

Thus a factorwise Mertens argument would need a genuine power, not just
the prime number theorem.  More generally, on the additive central arc
\(|\alpha|\ll S^{-1}\), suppose the \(G,Q,S\) Möbius polynomials have
relative power savings \(\eta_G,\eta_Q,\eta_S\), respectively.  Two
partial summations preserve those savings for separated smooth weights,
and the exact balanced exponent is

\[
\boxed{
 E_{\rm central}
 =5-\left(\tfrac12\eta_G+\tfrac52\eta_Q+3\eta_S\right),
 \qquad
 E_{\rm central}\leq\tfrac92
 \Longleftrightarrow
 \tfrac12\eta_G+\tfrac52\eta_Q+3\eta_S\geq\tfrac12.}
\tag{9.303}
\]

The executable ledger checks (9.303) with exact fractions; for example,
a saving \(\eta_S=1/6\) in the length-\(S\) polynomial alone is exactly
the threshold.  Known unconditional zero-free-region bounds correspond
to no fixed positive \(\eta\), so this route does not prove the gate.

There is nevertheless a genuine improvement in the remaining Type-II
geometry.  The cutoff \(U=V=T^{1/4}\) in (9.245) was balanced before
the \(h\)-completion.  After (9.280), Type I is completed in the
length-\(D=T^2\) variable \(d\), so much larger cutoffs are legal.  If
\(U=T^u,V=T^v\), put \(c=u+v<2\).  Summing the nonzero term in
(9.300) absolutely, with Fourier decay order \(A\), has exponent

\[
\boxed{
 E_{\rm I}^{\ne0}(A)
 =3+c+(A-1)(c-2),\qquad
 E_{\rm I}^{\rm sharp}=3+c.}
\tag{9.304}
\]

Thus every fixed \(c<2\) is closed by taking \(A\) large enough.  The
boundary-preserving choice

\[
\boxed{U=V=T^{3/4},\qquad c=\frac32}
\tag{9.305}
\]

already gives \(E_{\rm I}^{\rm sharp}=9/2\), while \(A=2\) gives the
smooth nonzero-mode exponent \(4\).  It leaves the zero frequency
(9.301) unchanged, but shortens the long--long packet.  Writing
\(n=s+d=Bk\), \(B=bc\), its exact exponent geometry becomes

\[
\boxed{
 B>T^{3/2},\qquad k\ll T^{3/2},\qquad
 \#\{k:Bk\in s+[D,2D]\}\ll T^{1/2}+1;
 \quad B>D\Longrightarrow k\ll T.}
\tag{9.306}
\]

The third statement is for fixed \(B,s\); all floor endpoints are
retained by the literal interval \(Bk\in s+[D,2D]\).  Hence the
post-completion residual has a symmetric product/quotient face
\((B,k)=(T^{3/2},T^{3/2})\), and its high-product face has a
complementary quotient of length only \(T\).  This is strictly shorter
than (9.245)'s \(B=T^{1/2},k=T^{5/2}\) face.  It is a useful new
starting point for a bilinear dispersion estimate, but it does not
cancel (9.301) or prove the central major arc.

This was the largest cutoff justified by estimating each Type-I
completion error separately.  Once the centered estimate (9.308) is
available, the endpoint choice (9.319) below supersedes (9.305) for the
final residual gate.

The product regrouping permits one more unconditional step.  Put
\[
 \Lambda_{U,V}(D)
 :=\sum_{m\leq D}\frac{\lambda_{U,V}(m)}m.
\]
For every \(n=s+d>\max(U,V)\), (9.296) gives the pointwise finite
decomposition

\[
\boxed{
\begin{aligned}
 \mu(s+d)
 ={}&\Lambda_{U,V}(D)\\
 &+\sum_{m\leq D}\lambda_{U,V}(m)
       \left(1_{m\mid s+d}-\frac1m\right)\\
 &+\sum_{\substack{m>D\\m\mid s+d}}\lambda_{U,V}(m).
\end{aligned}}
\tag{9.307}
\]

The middle line is unconditionally within the target.  To see this,
first omit the coprimality notation and let \(a_s\) and \(\lambda_m\)
be arbitrary coefficients on dyadic intervals of lengths \(S\) and
\(M\leq D\).  Poisson summation followed, for each nonzero \(k\), by
the additive large sieve for the \(1/(4M^2)\)-spaced points \(k/m\)
gives

\[
\boxed{
\begin{aligned}
 \mathcal C_M
 :={}&\sum_{m\asymp M}\lambda_m\sum_{s\asymp S}a_s
 \sum_dW(d/D)\left(1_{m\mid s+d}-\frac1m\right),\\
 |\mathcal C_M|
 \ll_{A,\varepsilon,W}{}&
 \left(\frac MD\right)^{A-1}
 \|\lambda\|_2\|a\|_2
 (S+M^2)^{1/2}T^\varepsilon .
\end{aligned}}
\tag{9.308}
\]

For completeness, one first uses the spacing argument for
\(|k|<M/2\); the remaining \(k\)'s are absorbed by arbitrary Schwartz
decay.  The sum over \(k\ne0\), including the factor \(D/m\), is
\(\ll_A(M/D)^{A-1}\).  Fixed \(k\) causes no coincident fractions on
one dyadic \(m\)-interval.

In the present application,
\(|\lambda_{U,V}(m)|\leq\tau(m)\), hence
\(\|\lambda\|_2\ll M^{1/2}T^\varepsilon\), while (9.292) gives
\(\|a\|_2\ll S^{1/2}T^\varepsilon\) for
\(a_s=\mu(s)\omega_{G,Q}(s)\).  If \(M=T^\beta\), \(S=T^3\),
\(D=T^2\), and \(A=2\), the exact exponent in (9.308) is

\[
\boxed{
 E_{\rm centred}(\beta)
 =\frac\beta2+\frac32
  +\frac12\max(3,2\beta)+(\beta-2)
 \leq\frac92\qquad(0\leq\beta\leq2).}
\tag{9.309}
\]

Equality occurs only at \(M=D=T^2\); at the new product floor
\(M=T^{3/2}\), the exponent is \(13/4\).

The original restriction \((d,s)=1\) is handled before applying
(9.307).  Expand it as \(\sum_{j\mid(d,s)}\mu(j)\), put
\(s=jn,d=jh\), and use squarefreeness: on the surviving support,
\[
 \mu(s)\mu(s+d)
 =\mu(jn)\mu(j(n+h))=\mu(n)\mu(n+h).
\]
The inclusion coefficient \(\mu(j)\) remains outside and has modulus
at most one.
The \(j\)-layer has lengths \(S_j=S/j,D_j=D/j\); after establishing
(9.308), take the endpoint cutoffs
\(U_j=V_j=\lfloor\sqrt{D_j}\rfloor\) and apply (9.307) to
\(\mu(n+h)\) with centering cutoff \(D_j\).  At its endpoint
\(M=D_j\), (9.308) has exponent \(9/2-2\tau\) for
\(j=T^\tau\leq T\), and at most \(4-3\tau/2\) for \(\tau\geq1\).
Thus the dyadic \(j\)-sum costs no power.  The auxiliary conditions
\((j,n(n+h))=1\) have ordinary divisor expansions and only
\(T^\varepsilon\) energy cost.  Moving endpoints cost
\(D^2T^\varepsilon=T^{4+\varepsilon}\), as in Section 9.42.
Consequently every centered low-product block on every gcd layer is
proved to be \(O(T^{9/2+\varepsilon})\).

After this step, the completed scalar core has the strictly weaker
remaining interface

\[
\boxed{
\begin{aligned}
 \mathfrak G_{\rm dens+comp}
 :=\sum_{\substack{s\asymp S\\d\in I(s)\\(d,s)=1}}
 &\mu(s)\omega_{G,Q}(s)X_d(d)\\
 &\times\left\{
 \Lambda_{U,V}(D)
 +\sum_{\substack{m>D\\m\mid s+d}}\lambda_{U,V}(m)
 \right\}
 \ll_\varepsilon T^{9/2+\varepsilon}.
\end{aligned}}
\tag{9.310}
\]

Formula (9.310) displays the primitive \(j=1\) layer; the exact gate
also sums its scaled \(j\)-analogues with \(D_j=D/j\).  The preliminary
choice here is \(U=V=T^{3/4}\); the endpoint split (9.319) below gives
the final sharper gate.  Separated smooth factors
in \(s,d\) may be restored with their recorded \(T^\varepsilon\) norm.
In the second term write \(s+d=mk\); then \(m>D=T^2\) forces
\(k\ll S/D=T\).
The density and complementary-divisor pieces are deliberately kept
together, since (9.299) shows that their cancellation is global rather
than equal-modulus algebra.  Estimate (9.310) remains unproved, but it
is narrower than (9.282): all Type-I nonzero modes and all centered
low-product Type-II modes have now been removed unconditionally.

### 9.48 Complementary divisor switching and the asymptotic-sieve boundary

The nonsquarefree shifted arguments do not belong to the remaining
gate.  If \(\mu(s+d)=0\), (9.307) says pointwise that its density plus
complementary part is the negative of its centered part.  Hence (9.308)
already bounds their total contribution.  It remains only to consider
squarefree \(n=s+d\).

Every divisor \(m\mid n\) is then squarefree.  Since the endpoint high
range has \(m>D\geq UV\), the short--short part of (9.295) is empty.
Define
\[
 R_{U,V}(m)
 :=\#\{(b,c):bc=m,\ b>U,\ c>V\}.
\]
All long--long factor pairs have the same sign, giving
\[
\boxed{\lambda_{U,V}(m)=\mu(m)R_{U,V}(m)
\qquad(\mu^2(m)=1,\ m>UV).}
\tag{9.311}
\]

If \(n=mk\) is squarefree, then \((m,k)=1\) and
\[
\boxed{\mu(m)=\mu(mk)\mu(k).}
\tag{9.312}
\]

Let
\[
 A(n):=\sum_{\substack{s+d=n\\s\asymp S,\ d\in I(s)\\(d,s)=1}}
       \mu(s)\omega_{G,Q}(s)X_d(d).
\]
On the squarefree support, complementary divisor switching turns the
second part of (9.310) into
\[
\boxed{
 \sum_{\substack{n\asymp S\\\mu^2(n)=1}}A(n)
 \sum_{\substack{m>D\\m\mid n}}\lambda_{U,V}(m)
 =
 \sum_{k\ll S/D}\mu(k)
 \sum_{\substack{m>D\\(m,k)=1\\mk\asymp S}}
 R_{U,V}(m)\mu(mk)A(mk).}
\tag{9.313}
\]

All endpoints and signs are literal.  The finite checker verifies
(9.311)--(9.312) for every squarefree product in its test range.  Formula
(9.313) is a parity-sensitive Möbius bilinear form, not an arbitrary
divisor sum.

This is exactly where the Friedlander--Iwaniec asymptotic sieve becomes
relevant, but it does not supply the estimate.  In their notation our
balanced exponent map is
\[
\boxed{
 x=S=T^3,\qquad {\mathcal D}=D=T^2=x^{2/3},\qquad
 N=k\leq T=x^{1/3}=\sqrt{\mathcal D},\qquad
 U=T=x/{\mathcal D}.}
\tag{9.314}
\]

Thus the top \(k\)-block lies at the lower parity-breaking boundary in
their condition (B1), and the endpoint divisor cutoff equals their
(B3) ceiling.  The executable exponent ledger checks these equalities.
However, Friedlander--Iwaniec **assume** their bilinear estimate (B);
it is not a conclusion of the asymptotic-sieve theorem.  Moreover, their
theorem starts with a nonnegative sequence \(a_n\), their coefficient is
\(\gamma(k,C)=\sum_{d\mid k,d\leq C}\mu(d)\), and their bilinear form
has no extra \(m\)-weight \(R_{U,V}(m)\).  Our \(A(n)\) is signed and
retains the shifted two-Möbius correlation.  Consequently applying their
Theorem 1 here would amount to assuming the missing estimate.

The genuinely narrowed residual is the squarefree asymptotic-sieve
bilinear gate
\[
\boxed{
 \Lambda_{U,V}(D)
 \sum_{\substack{n\asymp S\\\mu^2(n)=1}}A(n)
 +
 \sum_{k\ll T}\mu(k)
 \sum_{\substack{m>D\\(m,k)=1\\mk\asymp S}}
 R_{U,V}(m)\mu(mk)A(mk)
 \ll_\varepsilon T^{9/2+\varepsilon}.}
\tag{9.315}
\]

Equation (9.315), together with its scaled gcd layers, is equivalent to
(9.310) modulo the already proved centered contribution.  It exposes
the precise parity-breaking input still missing: a bilinear estimate for
the actual signed additive-convolution sequence \(A\), at
\(k\leq\sqrt D\), with the divisor multiplicity \(R_{U,V}\) retained.
The published asymptotic sieve names this kind of input but does not
prove it.

The strongest all-interval Möbius theorem cited in Section 9.44 does not
cover even one long factor of (9.315).  Write
\[
 b=T^\beta,\qquad c=T^\gamma,\qquad k=T^\kappa.
\]
The complementary polytope is
\[
\boxed{
 \beta+\gamma+\kappa=3,\qquad
 \beta,\gamma\geq1,\qquad 0\leq\kappa\leq1.}
\tag{9.316}
\]
After fixing \(c,k\), varying \(d\) gives the \(b\)-variable an interval
of exponent
\[
\boxed{
 \frac{D}{ck}=T^{\,2-\gamma-\kappa}=T^{\beta-1}.}
\tag{9.317}
\]
The published \(5/8\) threshold would require
\[
 \beta-1\geq\frac58\beta
 \quad\Longleftrightarrow\quad
 \beta\geq\frac83.
\]
But (9.316) gives \(\beta\leq3-\gamma\leq2\).  Therefore
\[
\boxed{
 \beta_{\rm required}-\beta_{\rm maximum}
 =\frac83-2=\frac23>0,}
\tag{9.318}
\]
and the one-factor coverage set is empty; the same argument applies to
\(c\).  The exact-rational checker verifies this gap.  Hence (9.315)
must exploit a joint \(b,c,k\) average (or an equivalent global
recombination); it cannot be reduced to a published all-interval estimate
for one Möbius factor.

### 9.49 The exact square-root cutoff

The centered bound (9.308) permits the canonical integer choice
\[
\boxed{U=V=\lfloor\sqrt D\rfloor.}
\tag{9.319}
\]
This is stronger than the preliminary \(T^{3/4}\) cutoff.  It separates
the two rectangles exactly:
\[
\boxed{
 \lambda^{\rm I}_{U,V}(m)=0\quad(m>D),\qquad
 \lambda^{\rm II}_{U,V}(m)=0\quad(m\leq D).}
\tag{9.320}
\]
Indeed, short--short has \(bc\leq U^2\leq D\), while long--long has
\(bc\geq(U+1)^2>D\).  The finite checker verifies both support
statements for unequal products around every tested square cutoff.
Thus (9.307) is now literally Type I density plus centered Type I for
\(m\leq D\), followed by pure Type II for \(m>D\); there is no
transition overlap.

At the balanced scale \(U=V=T\), the residual product polytope becomes
\[
\boxed{
 \beta+\gamma+\kappa=3,\qquad
 \beta,\gamma\geq1,\qquad0\leq\kappa\leq1.}
\tag{9.321}
\]
In particular each long Möbius factor has exponent at most \(2\), the
complementary quotient still has exponent at most \(1\), and the
one-factor \(5/8\) gap strengthens from the preliminary \(5/12\) to
\[
\boxed{\frac83-2=\frac23.}
\tag{9.322}
\]
All occurrences of (9.310)--(9.315) in the final gate use the endpoint
cutoff (9.319), and on the \(j\)-layer use
\(U_j=V_j=\lfloor\sqrt{D_j}\rfloor\).  This exact square-root split is
the smallest remaining joint \(b,c,k\) region obtained by the present
Type-I/II method.

Nor does (9.303) prove that such a Mertens estimate is necessary: the
actual coupled kernel could still cancel between the low-modulus prefix,
the long--long modes \(m\gtrsim D\), and different separated
archimedean components.  What (9.295)--(9.303) prove is the narrower
boundary: Type-I nonzero frequencies are closed; equal-modulus algebraic
cancellation is impossible; and the unresolved central mechanism is a
finite weighted density-prefix cancellation or a genuinely coupled
Type-II cancellation, not an omitted endpoint term.

### 9.50 Rational-denominator coverage of the additive circle variable

There is a useful fixed-power estimate on genuine minor arcs, but its
parameter interval does not enter the missing near-zero packet with
positive width.  This can be checked without hiding any logarithmic
loss in the exponent notation.  Let

\[
 M_X(\alpha):=\sum_{n\leq X}\mu(n)e(\alpha n),\qquad
 X=T^x,\qquad q=T^r,
\]

and suppose \((a,q)=1\) and

\[
 \left|\alpha-\frac aq\right|\leq q^{-2}.
\]

The Vaughan decomposition with both splitting parameters equal to
\(X^{2/5}\), together with the standard Type-I and Type-II exponential
sum lemmas, gives

\[
\boxed{
 |M_X(\alpha)|
 \ll_\varepsilon
 T^{4x/5+\varepsilon}
 +T^{x-r/2+\varepsilon}
 +T^{x/2+r/2+\varepsilon}.}
\tag{9.323}
\]

This is Proposition 4 in Cha--Kim's explicit account of the Vinogradov
bound, with the logarithms absorbed into \(T^\varepsilon\); see
[arXiv:2504.06726](https://arxiv.org/abs/2504.06726).  Their displayed
Type-I and Type-II estimates are respectively
\((X^{4/5}+X/q+q)X^\varepsilon\) and
\((X^{3/5}+X/q+q)^{1/2}X^{1/2+\varepsilon}\), which give (9.323).
Dyadic or fixed smooth subintervals follow by subtraction and partial
summation.

If the required relative saving is \(X^{-\eta}\), all three terms in
(9.323) are within \(X^{1-\eta+\varepsilon}\) exactly when

\[
\boxed{
 \eta\leq\frac15,
 \qquad 2x\eta\leq r\leq x(1-2\eta).}
\tag{9.324}
\]

The first inequality is the immovable \(X^{4/5}\) Type-I floor.  The
other two come from the reciprocal-denominator and denominator terms.
The executable exact-rational ledger records both the closed theorem
interval and its intersection with the denominators occurring below;
meeting at one endpoint is deliberately not counted as positive-width
coverage.

For the direct shifted Möbius polynomial in (9.282), the smooth
\(d\)-transform restricts the relevant circle variable to
\(|\alpha|\lesssim D^{-1}=T^{-2}\), while the central scale is
\(S^{-1}=T^{-3}\).  On a dyadic band
\(|\alpha|\asymp T^{-a}\), \(2\leq a\leq3\), the reciprocal rational
approximation has denominator exponent \(r=a\).  The length is \(x=3\),
and (9.303) requires \(\eta_S=1/6\).  Hence

\[
\boxed{
 r_{\rm theorem}\in[1,2],\qquad
 r_{\rm actual}\in[2,3],\qquad
 r_{\rm theorem}\cap r_{\rm actual}=\{2\}.}
\tag{9.325}
\]

Thus the classical fixed-power bound touches only the outer endpoint
\(|\alpha|\asymp D^{-1}\); it controls no dyadic annulus inside the
near-zero packet.

One might instead fix \(g\asymp T^{1/2}\) and apply (9.323) to the
\(q\asymp T^{5/2}\) polynomial.  Its frequency is
\(\alpha g\asymp T^{-(a-1/2)}\), so its reciprocal denominator has
\(r\in[3/2,5/2]\).  Saving the whole missing \(T^{1/2}\) from this
factor requires the maximal relative saving \(\eta_Q=1/5\).  Formula
(9.324) again gives only an endpoint:

\[
\boxed{
 r_{\rm theorem}\in[1,3/2],\qquad
 r_{\rm actual}\in[3/2,5/2],\qquad
 r_{\rm theorem}\cap r_{\rm actual}=\{3/2\}.}
\tag{9.326}
\]

There is an even quicker no-coverage test for the complementary
\((b,c,k)\)-polytope (9.321).  A single Möbius factor of length
\(T^\xi\) can save at most \(T^{\xi/5}\) through (9.323), whereas the
packet needs \(T^{1/2}\).  Therefore a one-factor Vinogradov argument
requires

\[
\boxed{\xi\geq\frac52.}
\tag{9.327}
\]

But (9.321) has \(\beta,\gamma\leq2\) and \(\kappa\leq1\).  Hence none
of the three complementary factors can supply the missing power alone.
The original \(q\)-factor has exactly \(\xi=5/2\), but (9.326) shows
that it saturates the power only at the outer endpoint.

The 2026 almost-all short-interval theorem of
Matomäki--Radziwiłł--Shao--Tao--Teräväinen does not change this power
ledger.  For Möbius against polynomial phases it proves arbitrary
logarithmic saving outside an exceptional set, not \(X^{-c}\); see
[Corollary 1.2(i)](https://link.springer.com/article/10.1007/s00222-026-01408-6).
The same paper obtains fixed-power discorrelation for divisor-function
coefficients, and explicitly distinguishes that case from
\(f\in\{\Lambda,\mu\}\).  Consequently neither Davenport uniformity,
the explicit Vinogradov minor-arc estimate, nor the newest almost-all
Fourier theorem proves (9.315).

The surviving circle-method interface is therefore more precise than
"control the minor arcs": it is the **positive-width near-zero/small-
denominator major-arc packet**, with the density prefix and the
long--long complementary modes kept together.  Any successful proof
must use joint \(b,c,k\) cancellation, an exact vanishing moment of the
actual combined multiplier, or a new fixed-power Möbius estimate on
that major-arc packet.  No such theorem is asserted here.

### 9.51 Finite Ramanujan diagonalization of density plus complement

The phrase "small-denominator major arc" can be sharpened further.
There is an exact finite Ramanujan expansion in which every nonzero
reduced denominator through \(D\) is already within the target.  Fix a
literal upper endpoint \(Y\asymp S\), write
\(c_r(n)=\sum_{u\bmod r}^{*}e_r(un)\), and put

\[
 K_{D,Y}(n)
 :=\Lambda_{U,V}(D)
   +\sum_{\substack{D<m\leq Y\\m\mid n}}\lambda_{U,V}(m).
\]

Define

\[
\boxed{
\begin{aligned}
 C_1(D,Y)
 &:=\Lambda_{U,V}(D)
    +\sum_{D<m\leq Y}\frac{\lambda_{U,V}(m)}m
   =\sum_{m\leq Y}\frac{\lambda_{U,V}(m)}m,\\
 C_r(D,Y)
 &:=\sum_{\substack{D<m\leq Y\\r\mid m}}
       \frac{\lambda_{U,V}(m)}m\qquad(r>1).
\end{aligned}}
\tag{9.328}
\]

Then the boundary-exact identity is

\[
\boxed{
 K_{D,Y}(n)=\sum_{r\leq Y}C_r(D,Y)c_r(n)
 \qquad(1\leq n\leq Y).}
\tag{9.329}
\]

Indeed,
\[
 \sum_{r\mid m}c_r(n)=m\,1_{m\mid n}.
\]
The \(r=1\) term in (9.329) is important: it combines the original
density prefix with the zero modes of **all** complementary moduli.
Thus no limiting Euler product and no interchange of the two pieces is
being used.  The executable checker constructs every \(C_r\) as an
exact rational number and verifies (9.329) for all tested cutoffs and
arguments.

The coefficients have an elementary uniform majorant.  Since
\(|\lambda_{U,V}(m)|\leq\tau(m)\) and
\(\tau(r\ell)\leq\tau(r)\tau(\ell)\),

\[
\boxed{
 |C_1(D,Y)|\ll_\varepsilon Y^\varepsilon,\qquad
 |C_r(D,Y)|
 \leq\frac{\tau(r)}r\sum_{\ell\leq Y/r}\frac{\tau(\ell)}\ell
 \ll_\varepsilon\frac{Y^\varepsilon}{r}\quad(r>1).}
\tag{9.330}
\]

Now let
\[
 F(\alpha)=\sum_{s\asymp S}a_s e(\alpha s),\qquad
 H(\alpha)=\sum_d X_d(d)e(\alpha d),
\]
where \(\|a\|_2\ll S^{1/2}T^\varepsilon\) as in (9.292) and
\(\|X_d\|_2\ll D^{1/2}T^\varepsilon\).  Formula (9.329) gives

\[
\boxed{
 \sum_{s,d}a_sX_d(d)K_{D,Y}(s+d)
 =\sum_{r\leq Y}C_r(D,Y)
   \sum_{u\bmod r}^{*}F(u/r)H(u/r).}
\tag{9.331}
\]

Consider a dyadic \(r\asymp R=T^\rho\) with \(2\leq R\leq D\).
Every primitive numerator is nonzero, so one discrete summation by
parts in the smooth \(d\)-weight, followed by the additive large sieve
for both polynomials, gives

\[
\boxed{
 \mathcal B_R
 \ll_\varepsilon
 \frac1R\left(\frac RD\right)^A
 \{(S+R^2)S\}^{1/2}
 \{(D+R^2)D\}^{1/2}T^\varepsilon.}
\tag{9.332}
\]

Here \(A\) counts discrete derivatives of the separated smooth weight;
the moving sharp endpoints were already removed at cost
\(D^2T^\varepsilon=T^{4+\varepsilon}\).  Taking only \(A=1\), the
exact exponent is

\[
\boxed{
 E_{\rm Ram}(\rho)=
 \begin{cases}
 3,&0\leq\rho\leq1,\\
 2+\rho,&1\leq\rho\leq3/2,\\
 1/2+2\rho,&3/2\leq\rho\leq2,
 \end{cases}
 \qquad E_{\rm Ram}(\rho)\leq\frac92.}
\tag{9.333}
\]

The exact-rational ledger verifies every breakpoint and the endpoint
equality at \(R=D\).  The same argument on a gcd layer uses
\(S_j=S/j,D_j=D/j,Y_j\asymp S_j\); its endpoint gains the same powers
of \(j\) as (9.308), so the dyadic \(j\)-sum costs no power.
Consequently **all \(2\leq r\leq D\) reduced-denominator modes are
proved within the target**.  In particular, the positive-width
small-denominator packet left in Section 9.50 is not a genuine
obstruction once density and complement are Ramanujan-diagonalized.

For \(r>D\), smoothness restricts the surviving primitive numerators to
\(0<|u|\ll rD^{-1}T^\varepsilon\).  The strictly weaker remaining
interface is therefore

\[
\boxed{
\begin{aligned}
 \mathfrak G_{\rm edge}
 :={}&C_1(D,Y)F(0)H(0)\\
 &+\sum_{D<r\leq Y}C_r(D,Y)
   \sum_{\substack{u\bmod r\\(u,r)=1\\
                   0<\|u\|_r\ll rD^{-1}T^\varepsilon}}
       F(u/r)H(u/r)
 \ll_\varepsilon T^{9/2+\varepsilon}.
\end{aligned}}
\tag{9.334}
\]

Modulo (9.332), the scaled gcd layers, and arbitrary-power Fourier
tails, (9.334) is equivalent to (9.310).  It is strictly weaker as a
sufficient gate because every intermediate reduced denominator has
already been discharged.

The high-denominator geometry retains the double Möbius structure
exactly.  Write \(m=rv\) in (9.328) and lift the reduced numerator to
the full-modulus frequency \(a_{\rm R}=uv\).  Then

\[
 \frac ur=\frac {a_{\rm R}}m,\qquad (a_{\rm R},m)=v,\qquad
 |u|\ll\frac rD,\qquad v=\frac mr,\qquad
 |a_{\rm R}|\ll\frac mD.
\tag{9.335}
\]

To retain the complementary quotient, put
\(k=T^\kappa,m=bc=T^{3-\kappa},r=T^\rho\), and write
\(v=T^\lambda,u=T^\nu\).  The exact exponent polytope is

\[
\boxed{
 \rho+\lambda=3-\kappa,\qquad
 \nu=\rho-2,\qquad
 \nu+\lambda=1-\kappa,\qquad
 \operatorname{len}(a_{\rm R})=1-\kappa.}
\tag{9.336}
\]

Thus the previously tempting constant sum \(1\) is only the top face
\(\kappa=0\), not the quotient-aware identity on every dyadic block.
Also \(a_{\rm R}\) is **not** the original AFE numerator
\(a_{\rm AFE}=h_0\delta_0\) retained in (9.239)--(9.246).  Poisson
completion in (9.278)--(9.280) has already absorbed that numerator into
the bounded dual weight.  The notation must not identify these two
different factorizations.

Moreover, at the square-root cutoff (9.319),
\[
 \lambda_{U,V}(m)
 =\sum_{\substack{bc=m\\b>U,\ c>V}}\mu(b)\mu(c)
 \qquad(m>D),
\]
so the second line of (9.334), before summing equal products, is
literally

\[
\sum_{b,c>T}\frac{\mu(b)\mu(c)}{bc}
\sum_{\substack{v\mid bc\\bc/v>D}}
\sum_{\substack{u\bmod bc/v\\(u,bc/v)=1\\
 |u|\ll bc/(vD)}}
 F\!\left(\frac{uv}{bc}\right)
 H\!\left(\frac{uv}{bc}\right),
\tag{9.337}
\]

with dyadic endpoints and separated weights restored.  Thus the
surviving wing is a genuine two-Möbius product-modulus form with a
factored Ramanujan frequency \(a_{\rm R}=uv\), of quotient-aware length
\(T^{1-\kappa+\varepsilon}\), coupled to the zero mode in the first line
of (9.334).

Banks--Shparlinski's 2025 multiple-Möbius theorem does not close
(9.337).  Their general theorem treats a three-variable **additive**
equation \(f(n_1)+g(n_2)+P(n_3)=M\), with an injectivity hypothesis,
and supplies logarithmic cancellation.  For fixed \(k\), the nearest
permissible specialization of \(km-d-s=0\) takes
\((n_1,n_2,n_3)=(m,d,s)\), \(f(m)=km\), \(g(d)=-d\), and
\(P(s)=-s\).  On squarefree coprime layers the arbitrary weight
\({\tt v}_d=\mu(d)\) removes the theorem's extra \(\mu(d)\), while the
divisor multiplicity in \(\lambda(m)\) costs only \(T^\varepsilon\).
Nevertheless Theorem 2.4 then gives \((M+D)S\) for each fixed \(k\).
On a dyadic \(k\asymp K\), where \(KM\asymp S\) and \(KD\leq S\),
the summed scale is
\[
 K(M+D)S=(S+KD)S\asymp S^2=T^6,
\]
which is \(T^{3/2}\) above the target.  See
[arXiv:2506.08787](https://arxiv.org/abs/2506.08787), Theorems 2.1 and
2.4.  Hence (9.334), or equivalently the zero/high pair (9.337), remains
unproved; but all nonzero denominators through \(D\) are no longer part
of the gate.

### 9.52 Quotient-aware high-edge coverage audit

The reduced cofactor and numerator are gcd strata of one full
frequency, not two independent averaging variables.  For each fixed
integer \(m\), the map

\[
 (r,u)\longmapsto a_{\rm R}=u\frac mr\pmod m
\]

is a boundary-exact bijection

\[
\boxed{
 \coprod_{\substack{r\mid m\\r>D}}(\mathbb Z/r\mathbb Z)^\times
 \;\longleftrightarrow\;
 \left\{a_{\rm R}\bmod m:
 a_{\rm R}\ne0,\ \frac m{(a_{\rm R},m)}>D\right\}.}
\tag{9.338}
\]

Indeed, the inverse sends \(a_{\rm R}\) to
\(v=(a_{\rm R},m),r=m/v,u=a_{\rm R}/v\).  Consequently the complete
high spectrum may be regrouped, with no limiting process or discarded
boundary, as

\[
\boxed{
 \sum_{m>D}\frac{\lambda_{U,V}(m)}m
 \sum_{\substack{a_{\rm R}\bmod m\\a_{\rm R}\ne0\\
                  m/(a_{\rm R},m)>D}}
 F(a_{\rm R}/m)H(a_{\rm R}/m).}
\tag{9.339}
\]

The smooth cutoff restricts
\(|a_{\rm R}|\ll mD^{-1}T^\varepsilon\); away from its equality
boundary the reduced-denominator condition in (9.339) is then
automatic.

The elementary large-sieve loss on a dyadic reduced denominator
\(r=T^\rho>D=T^2\) is exact.  With no Fourier decay, (9.332) has exponent

\[
\boxed{
 E_{\rm edge}^{\rm LS}(\rho)
 =-\rho+\frac32+1
  +\frac12\max(3,2\rho)+\frac12\max(2,2\rho)
 =\rho+\frac52.}
\tag{9.340}
\]

Relative to the target \(9/2\), its gap is therefore

\[
\boxed{E_{\rm edge}^{\rm LS}-\frac92=\rho-2=\nu.}
\tag{9.341}
\]

Even the optimistic heuristic of independent square-root cancellation
in \(u\) and \(v\) supplies only

\[
 \frac{\nu+\lambda}{2}=\frac{1-\kappa}{2}.
\]

It covers (9.341) precisely when

\[
\boxed{
 \nu\leq\lambda
 \quad\Longleftrightarrow\quad
 \rho\leq\frac{5-\kappa}{2}.}
\tag{9.342}
\]

Thus two hypothetical square roots cover at most the lower half of the
high wing.  The upper half \(\nu>\lambda\) requires more, and (9.338)
explains why treating \(u,v\) as independent cancellation directions
overcounts the available structure.

The following published-estimate coverage table records the remaining
mismatches.  A negative margin is a quantitative failure; “resonant”
means that the theorem does not estimate the selected coefficient even
if its displayed exponent were large enough.

| Input | Available saving on \(m=T^{3-\kappa},r=T^\rho\) | Required / coverage | Status |
|---|---:|---:|---|
| elementary reduced Farey large sieve | \(0\) beyond (9.340) | \(\nu=\rho-2\) | misses every positive-width high block |
| hypothetical \(u\)- and \(v\)-square roots | \((1-\kappa)/2\) | covers iff \(\nu\leq\lambda\) | diagnostic only; not a theorem |
| Dong--Robles--Zaharescu--Zeindler, Thm. 1.6 | \(\min(\rho/4,(3-\kappa)/7,\lambda/4)\) for an unrestricted \(\mu*\mu\) rational sum | at least \(\nu\) | quantitatively insufficient near \(\lambda=0\), and structurally resonant |
| Robert--Sargos / Fouvry--Iwaniec monomial forms | displayed \(X_{\rm phase}^{-1/2}=T^{-1/2}\) cap, since \(X_{\rm phase}=S/D=T\) | raw scalar normalization needs \(T^{-(3/2-\kappa)}\) | only the degenerate boundary \(\kappa=1\), no positive-width wing |

For the third row, the obstruction is exact: the high-edge coefficient
selects \(r\mid bc\), hence at the rational phase \(u/r\)

\[
 e\!\left(\frac{u\,bc}{r}\right)=1.
\tag{9.343}
\]

The cancellation in the unrestricted \(\mu*\mu\) exponential sum may
come from products outside this resonant divisibility subsequence, so
Theorem 1.6 of Dong--Robles--Zaharescu--Zeindler cannot be inserted into
(9.337).  Their arbitrary-\(g*h\) Type-II lemma has the same mismatch:
it controls a product phase, whereas the actual selected product phase
is identically one.

For the last row, expanding \(F(a_{\rm R}/m)H(a_{\rm R}/m)\) and fixing
\(n=s+d\) gives \(e(a_{\rm R}n/(bc))\).  On the support
\(a_{\rm R}\asymp bc/D\), \(n\asymp S\), its phase variation is exactly

\[
 X_{\rm phase}\asymp\frac{n a_{\rm R}}{bc}\asymp\frac SD=T.
\tag{9.344}
\]

The \(X^{-1/2}\) term in the published arbitrary-coefficient
three- and four-dimensional monomial estimates therefore caps their
uniform saving at one half-power.  Restoring the convolution weight and
the full numerator length does not fill the \(3/2-\kappa\) scalar gap.

This leaves two honest routes.  Postcompletion, one needs cancellation
across the **single full numerator** in (9.339), strong enough to recover
its entire \(T^{1-\kappa}\) length and compatible with the zero mode.
Precompletion, the exact packet (9.239)--(9.246) is the route that truly
retains \(a_{\rm AFE}=h_0\delta_0\) together with
\(\mu(g)\mu(q)\mu(b)\mu(c)\), the incidence \(bc\mid gq+d\), and the
inverse phase.  Neither route is proved here.  The executable finite
ledger checks (9.336), (9.338), (9.340)--(9.342), and the quantitative
rows of the table exactly.

### 9.53 Dual product Type II before the Ramanujan resonance

The resonance objection in (9.343) is specific to the postcompletion
Ramanujan spectrum.  Before selecting \(r\mid bc\), the generalized
Type-II estimate of Dong--Robles--Zaharescu--Zeindler is genuinely
applicable to both product polynomials.  A complete exponent audit shows
that this does not close the gate, but it gives a sharper and
structurally correct no-coverage statement.

Start with the long--long packet (9.242), which still retains the
original numerator \(a_{\rm AFE}=h\delta_0\) and all four signs
\(\mu(b)\mu(c)\mu(g)\mu(q)\).  Write \(gq+d=bck\), and only then apply
the exact \(h\)-completion (9.278)--(9.280).  The product numerator forces
\(\delta_0=\ell d\), with \(0<|\ell|\ll T^\varepsilon\), and one
separated dual mode is a smooth version of

\[
\boxed{
 H\sum_{b,c>T}\mu(b)\mu(c)
 \sum_k\sum_{g\asymp T^{1/2}}\mu(g)
 \sum_{q\asymp T^{5/2}}\mu(q)\,
 X_d(bck-gq).}
\tag{9.345}
\]

No Möbius factor was discarded in reaching (9.345); the disappearance
of \(h\delta_0\) is the exact consequence of using that product
structure in Poisson, rather than replacing it by an arbitrary
coefficient.  Additive Fourier inversion factors (9.345) into the
\((b,c)\)-product polynomial at frequency \(\alpha k\), the
\((g,q)\)-product polynomial at frequency \(-\alpha\), and the smooth
\(d\)-transform.

Put

\[
 b=T^\beta,\quad c=T^\gamma,\quad k=T^\kappa,\qquad
 \beta+\gamma+\kappa=3,\quad\beta,\gamma\geq1,
\tag{9.346}
\]

and consider the band
\(|\alpha|\asymp T^{-\mathfrak a}\),
\(2\leq\mathfrak a\leq3\).
Choose the rational approximation with denominator
\(q_\alpha\asymp T^{\mathfrak a}\): taking the nearest integer to
\(1/|\alpha|\), with numerator \(\operatorname{sgn}(\alpha)\), gives
an \(O(q_\alpha^{-2})\) error uniformly on the band.  Write

\[
 (k,q_\alpha)=T^{\tau_k},\qquad
 0\leq\tau_k\leq\kappa,\qquad x:=\beta+\gamma=3-\kappa.
\]

Multiplication by \(k\) changes the reduced denominator to
\(T^{\mathfrak a-\tau_k}\).  The approximation parameter in DRZZ
Lemma 4.2 has
exponent

\[
 u_{\tau_k}=(\kappa-2\tau_k)_+.
\]

The two exact Type-II constants are therefore

\[
\boxed{
\begin{aligned}
 M_{bc}
  &=\max\{x-\mathfrak a+\tau_k+u_{\tau_k},\ \beta,\ \gamma,\
           \mathfrak a-\tau_k\},\\
 M_{gq}
  &=\max\{3-\mathfrak a,\tfrac12,\tfrac52,\mathfrak a\}
   =\max\{\tfrac52,\mathfrak a\}.
\end{aligned}}
\tag{9.347}
\]

Lemma 4.2, including the coefficient norms, gives exponents
\((x+M_{bc})/2\) and \((3+M_{gq})/2\), respectively.  The number of
\(k\)'s in the gcd stratum has exponent \(\kappa-\tau_k\), while the
\(L^1\)-mass of the \(d\)-transform on this circle band is
\(T^{2-\mathfrak a}\).  Hence the complete pointwise-band exponent is

\[
\boxed{
 E_{\rm prod}(\beta,\gamma,\kappa,\mathfrak a,\tau_k)
 =\kappa-\tau_k+\frac{x+M_{bc}}2
  +\frac{3+M_{gq}}2+2-\mathfrak a.}
\tag{9.348}
\]

Keeping the \(bck\)-coefficient intact and using Cauchy--Parseval instead
gives

\[
\boxed{E_{\rm CS}(\tau_k)=5-\frac{\tau_k}{2}.}
\tag{9.349}
\]

The valid published/elementary bound on this stratum is the minimum of
(9.348) and (9.349).  Some large-gcd strata are now genuinely covered.
For example,

\[
 (\beta,\gamma,\kappa,\mathfrak a,\tau_k)
 =\left(1,\frac32,\frac12,\frac52,\frac12\right)
\]

has \(E_{\rm prod}=9/2\), and
\((1,1,1,5/2,1)\) has \(E_{\rm prod}=4\).

The dominant coprime stratum is completely different.  If \(\tau_k=0\),
then \(M_{bc}\geq\mathfrak a\),
\(M_{gq}=\max(5/2,\mathfrak a)\).  For
\(2\leq\mathfrak a\leq5/2\),

\[
 E_{\rm prod}
 \geq \frac{25}{4}+\frac{\kappa-\mathfrak a}{2}
 \geq5+\frac\kappa2,
\]

and for \(5/2\leq\mathfrak a\leq3\),

\[
 E_{\rm prod}\geq5+\frac\kappa2.
\]

Together with \(E_{\rm CS}(0)=5\), this proves the uniform identity

\[
\boxed{
 \min(E_{\rm prod},E_{\rm CS})=5
 \quad(\tau_k=0),\qquad
 5-\frac92=\frac12.}
\tag{9.350}
\]

The 2026 log-free Möbius estimate of Srivastav also reaches the central
major arc, but does not change (9.350).  Taking its rational
approximation \(0/1\), the parameter on either product side is
\[
 \delta_\alpha\asymp |\alpha|\,T^3
 =T^{3-\mathfrak a}.
\]
Whenever the theorem's range
\(\delta_\alpha\leq X^{1/5+\varepsilon}\) is satisfied, it saves at
most \(\delta_\alpha^{1/2}=T^{(3-\mathfrak a)/2}\) on that side.
Even granting this saving independently on both the \(bc\) and \(gq\)
sides gives \(T^{3-\mathfrak a}\), whereas the raw circle-band bound
needs \(T^{7/2-\mathfrak a}\).  The difference is again exactly
\(T^{1/2}\).  Thus the new log-free major-arc technology improves
logarithmic losses and constants, but not the missing power in this
coupled product geometry; see
[arXiv:2505.07803](https://arxiv.org/abs/2505.07803), Theorem 1.

Equality occurs on the admissible polytope, so (9.350) is not an
artifact of a loose case split.  Thus the dual application of the
published Type-II lemma recovers determinant density on the appropriate
bands and deletes some high-gcd strata, but it supplies **no power
saving at all beyond Cauchy on the coprime \(k\)-stratum**.  Since that
stratum has no polynomial density loss,

\[
 \#\{k\asymp K:(k,q_\alpha)=1\}
 =K\frac{\varphi(q_\alpha)}{q_\alpha}
  +O(\tau(q_\alpha))
 =K\,T^{-o(1)}
\tag{9.351}
\]

on every positive-length \(K\)-block; the bounded \(K\)-blocks contain
literal coprime terms.  Thus the full \(k\)-block remains unproved.

The weaker residual gate may now exclude every stratum for which
\(\min(E_{\rm prod},E_{\rm CS})\leq9/2\), but it must retain in
particular all \(\tau_k=0\) boxes.  This is a strict reduction, not a
closure.  The executable rational ledger verifies (9.347)--(9.350),
including the approximation loss \(u_{\tau_k}\), circle-band mass, high-gcd
boundary examples, and the entire quarter-power coprime grid.

### 9.54 The coprime packet as a $3\times2$ shifted convolution

The identity behind the remaining \(\tau_k=0\) packet can be stated
without any analytic approximation.  Record the smooth dyadic factors
as finite weights \(u_b,v_c,w_k,x_g,y_q\), keep the four Möbius signs
explicit, and extend the signed shift weight \(z_d\) by zero outside its
exact support.
Define

\[
 A(n)=\sum_{bck=n}\mu(b)\mu(c)u_bv_cw_k,
 \qquad
 C(s)=\sum_{gq=s}\mu(g)\mu(q)x_gy_q.
\tag{9.352}
\]

Then the precompletion determinant packet has the boundary-exact form

\[
\boxed{
 \sum_{b,c,k,g,q}\mu(b)\mu(c)\mu(g)\mu(q)
 u_bv_cw_kx_gy_q z_{bck-gq}
 =\sum_d z_d\sum_n A(n)C(n-d).}
\tag{9.353}
\]

There is no endpoint error in (9.353): the convention \(z_d=0\) outside
the finite shift set accounts for every truncated boundary.  The helper
`shifted_product_packet_sides` verifies the two sides directly for finite
integer weights.  Thus the dominant packet is literally a correlation
between a three-factor and a two-factor dyadic Möbius convolution, with

\[
 X=T^3,\qquad D=T^2=X^{2/3},\qquad
 T^{9/2}=X^{3/2}
\tag{9.354}
\]

as ambient, shift, and target scales.

This formulation makes the numerical strength of the nearest published
shifted-divisor estimates transparent.  Topacogullari, Theorem 1.2,
proves for the standard coefficients \(d_3,d\) and \(h\ll X^{2/3}\)
the smoothed fixed-shift error
\(X^{5/6+\theta/3+\varepsilon}\); see
[arXiv:1506.02608](https://arxiv.org/abs/1506.02608).  Summing the complete
shift block gives

\[
 D X^{5/6+\theta/3}
 =T^{9/2+\theta}.
\tag{9.355}
\]

With the unconditional exceptional-spectrum exponent
\(\theta=7/64\), this is \(T^{295/64}\), a deficit of \(T^{7/64}\).
The Selberg-eigenvalue endpoint \(\theta=0\) would touch, but not beat,
the required exponent.

The signed first-moment estimate of Baier--Browning--Marasingha--Zhao,
Theorem 1, is numerically stronger after averaging, although it concerns
the standard \(d_3\)--\(d_3\) error \(\Delta(X,d)\):

\[
 \sum_{d\leq D}\Delta(X,d)
 \ll \left(D^2+D^{1/2}X^{13/12}\right)X^\varepsilon.
\tag{9.356}
\]

At (9.354), the two terms have \(T\)-exponents \(4\) and \(17/4\),
so the latter is still \(T^{1/4}\) inside the target; see
[arXiv:1101.5464](https://arxiv.org/abs/1101.5464).  The exact proxy table is

| published shape | exponent after the $D=T^2$ shift block | margin below $T^{9/2}$ | applies to (9.353)? |
|---|---:|---:|---|
| smoothed $d_3$--$d$, fixed shift, \(\theta=7/64\) | \(295/64\) | \(-7/64\) | no: wrong coefficients, and its divisor Voronoi formula has no dyadic \(\mu*\mu\) replacement |
| same estimate at the Selberg endpoint \(\theta=0\) | \(9/2\) | \(0\) | conditional spectral endpoint and still wrong coefficients |
| signed first moment of the $d_3$--$d_3$ error | \(17/4\) | \(+1/4\) | no: both coefficient sequences and the singular main term are specific to \(\zeta^3\) |

Two broader dispersion results do not fill this coefficient gap.
Jiang--Lü, Theorem 1.1, permits a multiplicative \(f\) in
\(\sum f(n)\tau(n-1)\), under second-moment, sieve, and prime
Siegel--Walfisz hypotheses; see
[arXiv:2204.08221](https://arxiv.org/abs/2204.08221).  In (9.353), however,
\(A\) is a dyadically truncated factor convolution rather than one global
multiplicative function, while \(C\) is not \(\tau\).  Fouvry--Radziwill
allow an essentially arbitrary long sequence convolved with a short
Siegel--Walfisz sequence in an arithmetic-progression discrepancy; see
[arXiv:1811.08672](https://arxiv.org/abs/1811.08672), Theorem 1.1 and
Corollary 1.1.  Writing \(bck=gq+d\) as a congruence modulo \(g\) leaves
the coefficient \(\mu(q)=\mu((bck-d)/g)\) on the quotient.  Their
discrepancy main term has no such shifted quotient coefficient, so this
is not an admissible specialization.

Nor does averaged Chowla presently give the missing power.  Even for the
pointwise multiplicative Liouville or Möbius correlation, the quantitative
gain in Matomaki--Radziwill--Tao is logarithmic, of order roughly
\((\log\log D)/(\log D)\), not the fixed \(T^{1/2}\) needed here; see
[arXiv:1503.05121](https://arxiv.org/abs/1503.05121).  Moreover (9.352)
contains factor-restricted convolutions rather than a product of shifted
bounded multiplicative functions.

There is a second, independent obstruction: the shifted-divisor main term
cannot simply be omitted.  With

\[
 \mathcal A(\alpha)=\sum_n A(n)e(\alpha n),\quad
 \mathcal C(\alpha)=\sum_s C(s)e(\alpha s),\quad
 \mathcal Z(\alpha)=\sum_d z_de(\alpha d),
\]

equation (9.353) is
\(\int_0^1\mathcal A(\alpha)\mathcal C(-\alpha)
\mathcal Z(-\alpha)\,d\alpha\).  To isolate an actual finite zero mode,
choose $M>\max|n-s-d|$ on the finite supports and replace the integral
by the exact cyclic Fourier average over \(a\bmod M\).  Orthogonality has
no aliasing for this choice.  Its $a=0$ summand factors exactly as

\[
\boxed{
 \frac1M\mathcal A(0)\mathcal C(0)\mathcal Z(0)
 =\frac1M\left(\sum_b\mu(b)u_b\right)
  \left(\sum_c\mu(c)v_c\right)
  \left(\sum_k w_k\right)
  \left(\sum_g\mu(g)x_g\right)
  \left(\sum_q\mu(q)y_q\right)
  \left(\sum_d z_d\right).}
\tag{9.357}
\]

The helper `shifted_product_zero_mode_sides` verifies the numerator's
expanded and factored finite sums, including examples where (9.357) is
nonzero.  Since $M\asymp X$, the normalized zero summand has raw
exponent $X^2D/M=XD=T^5$, so isolating this frequency requires a fixed
half-power across the four dyadic Mertens blocks.  No algebraic factor in
(9.357) vanishes, and the classical zero-free-region estimate for Mertens
sums gives no fixed power.  This is a no-go statement for separating the
packet's main term; it is not a lower bound for the original coupled
kernel, whose dyadic pieces and other frequencies may still recombine.

The individual cyclic zero summand is not itself a sampling-invariant
object: choosing a much larger $M$ makes its factor $1/M$ smaller and
places proportionally more sample points in the same neighborhood of the
origin.  The invariant analytic obligation is therefore the complete
natural central cell

\[
 \boxed{\mathfrak C_X
 :=\int_{\|\alpha\|_{\mathbb R/\mathbb Z}\leq c/X}
 \mathcal A(\alpha)\mathcal C(-\alpha)
 \mathcal Z(-\alpha)\,d\alpha
 \ll X^{3/2+\varepsilon}.}
\tag{9.358}
\]

Absolute masses give $XD=X^{5/3}$, so (9.358) asks for the invariant
relative saving $X^{-1/6}=T^{-1/2}$.  Formula (9.357) is the exact
constant-value diagnostic inside that cell, not a claim that one
measure-zero point contributes to the continuous integral.  The July
2026 refinement of short-interval and averaged-Chowla bounds by Menon
improves the secondary logarithmic term to essentially the
$1/\log H$ limit of the Matomaki--Radziwill method, but still supplies
no fixed power; see
[arXiv:2607.15574](https://arxiv.org/abs/2607.15574), Theorems 1.4--1.5.
It also applies to pointwise multiplicative Liouville/Möbius weights, not
directly to both factor-restricted convolutions in (9.352).

Consequently the honest weaker interface exposed by the shifted-
convolution route has two parts:

1. evaluate and recombine the actual Möbius-weighted singular/central
   cell represented by (9.357)--(9.358), rather than importing the
   \(d_3\) main term;
2. prove the centered averaged \(3\times2\) convolution error at exponent
   \(T^{9/2+\varepsilon}\).

For standard divisor coefficients, (9.356) shows that the second item is
already numerically inside target.  For the actual coefficient pair
(9.352), neither item is a published theorem.  Thus this section replaces
the undifferentiated coprime half-power deficit by an exact main-term
obligation and a centered coefficient-transfer obligation, but does not
prove the coupled-kernel gate.  The executable
`shifted_divisor_proxy_ledger` records (9.355)--(9.358) and deliberately
returns `covered = False` here because neither coefficient applicability
nor algebraic central-mode vanishing is available.

### 9.55 Pairing each zeta variable with its mollifier before completion

There is one further exact regrouping which is invisible after the
common-gcd and Type-II decompositions.  It is tempting to use

\[
 \sum_{d\mid n}\mu(d)
 \left(1-\frac{\log d}{\log N}\right)
 =1_{n=1}+\frac{\Lambda(n)}{\log N}.
 \tag{9.359}
\]

Applied directly to (9.280), this is invalid: the factors
\(p_N(qr),p_N(qs)\) are weights on the free variables, not divisor
sums over the shifted argument.  Before expanding the two copies of
\(\zeta M_N\), however, a divisor sum really is present.

Put

\[
 B_{N,z}(x):=
 \sum_{\substack{d\mid x\\d\leq N}}
 \mu(d)\left(1-\frac{\log d}{\log N}\right)d^z.
 \tag{9.360}
\]

On the initial absolutely convergent AFE line, set \(x=nd\) and
\(y=me\).  Since

\[
 \frac{(mn)^{-z}}{\sqrt{demn}}
 =\frac{d^ze^z}{(xy)^{1/2+z}},
 \qquad
 \left(\frac{me}{nd}\right)^{it}=\left(\frac yx\right)^{it},
\]

the entire four-variable arithmetic sum in (2.6) has the exact product
form

\[
\boxed{
 \sum_{x,y\geq1}
 \frac{B_{N,z}(x)B_{N,z}(y)}{(xy)^{1/2+z}}
 \left(\frac yx\right)^{it}.}
 \tag{9.361}
\]

There is no endpoint error in (9.361).  For finite truncations it is
just the bijective regrouping \((d,n)\mapsto x=dn\) and
\((e,m)\mapsto y=em\); on the original \({\rm Re}\,z=2\) line the
finite \(d,e\)-sums and the two zeta sums are absolutely convergent.
The helper `zeta_mollifier_pairing_sides` verifies the corresponding
finite identity for arbitrary finite weights and an arbitrary nonzero
completely multiplicative Mellin model.

The zero Mellin frequency has a boundary-exact prime-plus-cofactor
description.  For every \(x\geq1\), completing the divisor sum and then
writing \(d=x/k\) in the omitted part gives

\[
\boxed{
\begin{aligned}
 B_{N,0}(x)
 ={}&1_{x=1}+\frac{\Lambda(x)}{\log N}\\
 &-\sum_{\substack{k\mid x\\kN<x}}
 \mu(x/k)\left(1-\frac{\log(x/k)}{\log N}\right).
\end{aligned}}
\tag{9.362}
\]

Thus \(B_{N,0}(x)=1_{x=1}+\Lambda(x)/\log N\) literally for
\(x\leq N\).  More generally, if \(x\leq NK\), every reflected
cofactor in (9.362) satisfies \(k<K\), with the strict endpoint
\(kN<x\) retained.  On squarefree \(x\), (9.362) may equivalently be
written

\[
 B_{N,0}(x)
 =1_{x=1}+\frac{\Lambda(x)}{\log N}
 -\mu(x)\sum_{\substack{k\mid x\\kN<x}}
 \mu(k)\left(1-\frac{\log x-\log k}{\log N}\right).
 \tag{9.363}
\]

The helper `truncated_selberg_divisor_sides` checks (9.362) with an
arbitrary completely additive formal logarithm, including every moving
floor boundary.  In the balanced AFE product range the reflected
cofactor is at most the zeta-variable scale \(T^{1/2+\varepsilon}\).
Consequently (9.361)--(9.363) replace the four visible Möbius factors by
a von-Mangoldt part and an explicitly short reflected tail at the
Mellin origin.  This is a genuine alternative to treating the four
signs as independent.

The origin is not the whole AFE integral.  If

\[
 P_x(z):=\prod_{p\mid x}(1-p^z),
\]

then the completed, untruncated coefficient is

\[
 \sum_{d\mid x}\mu(d)d^z
 \left(1-\frac{\log d}{\log N}\right)
 =P_x(z)-\frac{P_x'(z)}{\log N}.
 \tag{9.364}
\]

At \(z=0\), the order of vanishing of \(P_x\) leaves only prime
powers, which is (9.359).  At \(z=i\tau\ne0\), products with arbitrarily
many distinct prime factors are generically present.  The Gaussian AFE
factor localizes \(\tau\) to bounded size, not to a shrinking
neighborhood of zero, so Taylor expansion at \(z=0\) has no power
reserve.  Nor may one move the already reindexed long shifted energy
to a left Mellin line term by term: after such a move (9.361) is no
longer absolutely convergent.  A compact transition partition permits
Mellin inversion on \({\rm Re}\,z=0\), but it retains the entire family
\(B_{N,i\tau}\), including both reflected tails and their common
\(\tau\)-coupling.

This yields a sharper route boundary:

* the Selberg divisor identity **does** cross the original
  \(|\zeta M_N|^2\) expansion through (9.361);
* it does **not** cross the already completed packet (9.280) by a
  termwise substitution;
* the \(z=0\) slice reduces exactly to primes plus cofactors of length at
  most \(T^{1/2+\varepsilon}\) in the balanced transition;
* an unconditional proof still needs a uniform shifted estimate for the
  compact family \(B_{N,i\tau}\), or a new contour argument which
  recombines the transition before losing absolute convergence.

This caution is consistent with Radziwill's long-mollifier analysis:
the off-diagonal contribution is genuinely non-negligible, and under RH
is connected to Montgomery pair correlation; see
[arXiv:1207.6583](https://arxiv.org/abs/1207.6583).  That result does not
contradict an \(O(T^{1+\varepsilon})\) upper bound, but it rules out
treating the long-mollifier off-diagonal as an algebraically vanishing
error.  Bettin--Gonek give a useful precision on the logical strength.
For moments on \([0,T]\), their Theorem 1 says that the same upper bound
for every \(N\leq T^\theta\) excludes zeros in
\(\Re s>1/2+1/(2\theta)\), which at \(\theta=3\) would be the unknown
half-plane \(\Re s>2/3\).  The present moment is instead localized to
\([T,2T]\).  Their Theorem 2 gives only
\(\Re s>1/2+2/\theta\) in that setting, which is nontrivial only for
\(\theta>4\) and is vacuous at \(\theta=3\); see
[arXiv:1604.02740](https://arxiv.org/abs/1604.02740).  Thus their result
does not imply that the current local \(\theta=3\) target proves a new
zero-free region, while it does show why one must keep the window
normalization exact.  Equations (9.361)--(9.364) provide a new exact
coefficient-transfer interface, not a proof of the coupled-kernel gate.

### 9.56 Smooth double completion removes the artificial full-residue spectrum

The sharp-interval audit in Sections 9.29--9.30 deliberately retained
all residues because the transforms of \(1_{[1,H]}\) and \(1_{[1,L]}\)
have long \(1/\|a/s\|\) tails.  The actual kernel in (6.2) is different:
both factors are smooth and already carry their Fourier modulations.
For \(a,b\bmod s\), define

\[
\begin{aligned}
 \widehat U_{x,s}(a)
 &:=\sum_{h\in\mathbb Z}U(h/H)e(-hx)e_s(-ah),\\
 \widehat V_{y,s}(b)
 &:=\sum_{\delta\in\mathbb Z}V(\delta/L)
       e\left(\frac{\delta y}{2\pi}\right)e_s(-b\delta).
\end{aligned}
\tag{9.365}
\]

The same finite orthogonality calculation as (9.163), now with these
weights, gives the exact identity

\[
\boxed{
 \sum_{h,\delta\in\mathbb Z}U(h/H)V(\delta/L)
 e\left(-hx+\frac{\delta y}{2\pi}\right)
 e_s(-\bar r h\delta)
 =\frac1s\sum_{a,b\bmod s}
 \widehat U_{x,s}(a)\widehat V_{y,s}(b)e_s(rab).}
\tag{9.366}
\]

There is no endpoint error in (9.366).  Repeated discrete summation by
parts, with \(\|\cdot\|\) denoting distance to the nearest integer, gives
for every fixed \(A>0\)

\[
\begin{aligned}
 |\widehat U_{x,s}(a)|
 &\ll_{A,U}H\{1+H\|x+a/s\|\}^{-A},\\
 |\widehat V_{y,s}(b)|
 &\ll_{A,V}L\{1+L\|b/s-y/(2\pi)\|\}^{-A}.
\end{aligned}
\tag{9.367}
\]

Thus the first transform is centred at \(a\equiv-sx\pmod s\), with
width \(s/H\), and the second at \(b\equiv sy/(2\pi)\pmod s\), with
width \(s/L\).  Combining this with the actual centre ranges (6.1), the
two effective dual exponents are

\[
 \alpha=\max\{m,\sigma-h,0\},\qquad
 \beta=\max\{\sigma+1-m-\rho,\sigma-\ell,0\}.
\tag{9.368}
\]

The factors \(T^{O(\eta)}\) only enlarge these windows by a subpower.
Outside them, (9.367) may be used with arbitrarily large \(A\); after
summing the polynomially many dyadic and arithmetic parameters, the
discarded dual tail is \(O_{B,W}(T^{-B})\) for every fixed \(B\).
This is rapid decay, not literal compact support.  In particular, the
full-residue \(\nu=1\) rows of the sharp audit are not an obstruction for
the actual separated smooth kernel.

At the balanced transition corner

\[
 R=S=T^3,\qquad M=T^{1/2},\qquad H=L=T^{5/2},
\]

(9.368) gives

\[
 |a|,|b|\ll T^{1/2+O(\eta)},\qquad |ab|\ll T^{1+O(\eta)}.
\tag{9.369}
\]

Writing \(r=s+d\) in (9.366) changes the inner phase to
\(e_s(dab)\), without separating either outer sign:

\[
 \mu(s+d)\mu(s)\,
 \frac1s\sum_{a,b\bmod s}
 \widehat U_{x,s}(a)\widehat V_{y,s}(b)e_s(dab).
\tag{9.370}
\]

Consequently the only smooth dual block left at this corner is exactly
the lowest block already identified in (9.173)--(9.178).  Its circular
near range is

\[
 |d|\ll\frac{s}{|ab|}=T^{2+O(\eta)}=X^{2/3+O(\eta)},
 \qquad X=T^3.
\tag{9.371}
\]

The exponent ledger is unchanged where it matters: \(HL/s=T^2\), the
\((a,b)\)-count is \(T\), the \(s\)-count is \(T^3\), and the near
\(d\)-count is \(T^2\).  Hence the trivial exponent is \(8\), against the
local target \(RS=T^6\); a genuine \(T^2\) saving is still required.

The published-estimate coverage table now becomes strictly smaller:

| input | actual normalized length | exact outcome |
|---|---:|---|
| sharp full residue | \(\nu=1\) | removed from the actual smooth kernel by (9.367) |
| Blomer--Pascadi, Theorem 1.1 | \(\nu=(1/2)/3=1/6\) | margins \((-25/96,-19/96,-1/18)\); no power saving |
| one-modulus Parseval | two lengths \(T^{1/2}\) | exponent \(17/2\), gap \(5/2\) |
| averaged Chowla/Möbius correlation | shift \(X^{2/3}\) | logarithmic savings only; the ledger needs \(X^{2/3}=T^2\) |

For the second row, substituting \(N=c^\nu\) in
[Blomer--Pascadi, Theorem 1.1](https://arxiv.org/abs/2607.24311)
gives theorem exponents
\(29/32+\nu/8\), \(13/16+5\nu/16\), and
\(11/18+2\nu/3\), while the best elementary exponent at \(\nu=1/6\)
is \(2/3\).  Their published nontrivial interval
\(13/28<\nu<7/12\) therefore does not reach the smooth dual length.
This is already an optimistic scale comparison: (9.370) also retains
the moving shift, the product \(ab\), and both Möbius signs, so theorem
compatibility would require additional work even inside that interval.

The executable `weighted_additive_product_completion_sides` checks
(9.366) for arbitrary signed finite supports and arbitrary complex
weights.  The executable `smooth_additive_dual_support_ledger` records
(9.368)--(9.371) and the three exact Blomer--Pascadi margins.  The useful
advance is therefore a reduction of the gate, not its proof: arbitrary
full-residue and far-frequency estimates are unnecessary.  What remains
is a centred short-spectrum estimate for (9.370), uniform in the moving
smooth weights, which saves \(T^2\) while preserving
\(\mu(s+d)\mu(s)\) and the factorization \(ab\).

### 9.57 Reciprocity collapses the short dual block to weighted Chowla

There is a second completion adapted specifically to the near range
\(|d|=|r-s|\leq T^{2+O(\eta)}\).  It no longer uses the long modulus
\(s\).  Split the signs of \(d\), and first take \(d>0\).  Since
\((d,s)=1\), additive reciprocity gives

\[
\boxed{
 e_s(-\bar d_s h\delta)
 =e_d(\bar s_d h\delta)e\left(-\frac{h\delta}{ds}\right).}
\tag{9.372}
\]

Put all smooth factors, including the exact final factor in (9.372),
into

\[
 F_{s,d}(h,\delta)
 :=U(h/H)V(\delta/L)
 e\left(-hx+\frac{\delta y}{2\pi}-\frac{h\delta}{ds}\right),
\tag{9.373}
\]

and write its ordinary two-dimensional Fourier transform as
\(\widehat F_{s,d}(\xi,\eta)\).  Decomposing \(h,\delta\) into residue
classes modulo \(d\), applying Poisson summation on each class, and using

\[
 \sum_{u,v\bmod d}
 e_d(\bar s_d uv+ku+\ell v)
 =d\,e_d(-sk\ell)
\]

gives the exact identity

\[
\boxed{
 \sum_{h,\delta\in\mathbb Z}
 F_{s,d}(h,\delta)e_d(\bar s_d h\delta)
 =\frac1d\sum_{k,\ell\in\mathbb Z}
 \widehat F_{s,d}(k/d,\ell/d)e_d(-sk\ell).}
\tag{9.374}
\]

The finite helper shift_modulus_completion_sides verifies the residue
orthogonality underlying (9.372)--(9.374) for arbitrary signed finite
support and arbitrary complex pair weights.  Thus neither separability
of \(F\) nor deletion of the mixed archimedean phase is being assumed.

On the balanced near block,

\[
 s\asymp T^3,\qquad d\asymp T^2,\qquad H=L=T^{5/2}.
\]

The mixed phase is still smooth on the original scales, since
\(HL/(ds)\asymp1\).  Repeated integration by parts therefore gives

\[
 |\widehat F_{s,d}(k/d,\ell/d)|
 \ll_{A,W}HL
 \left(1+\frac{H|k|}{d}\right)^{-A}
 \left(1+\frac{L|\ell|}{d}\right)^{-A}.
\tag{9.375}
\]

Now \(H/d=L/d=T^{1/2}\).  Hence every nonzero \(k\) or \(\ell\) is
arbitrary-power small, and (9.374) becomes

\[
\boxed{
 \sum_{h,\delta}F_{s,d}(h,\delta)e_d(\bar s_dh\delta)
 =\frac1d\widehat F_{s,d}(0,0)
 +O_{A,W}\left(\frac{HL}{d}T^{-A}\right).}
\tag{9.376}
\]

The negative-\(d\) half has the identical conclusion after changing the
reciprocal signs.  Polynomially many outer parameters are absorbed by
increasing \(A\).  Thus the entire smooth lowest-dual block has no
remaining Kloosterman spectrum: it is an explicit archimedean zero mode
coupled to the two outer Möbius signs.

Normalize

\[
 \mathcal J_{s,d}:=(HL)^{-1}\widehat F_{s,d}(0,0).
\]

This is a bounded smooth function of the dyadic normalized variables,
with all moving endpoints retained in the outer weight.  At kernel
level, (9.376) reduces the balanced obstruction to

\[
\boxed{
 HL\sum_{\substack{s\asymp X,\ d\asymp D\\(s,d)=1}}
 \frac{\mu(s)\mu(s+d)}d\,\mathcal W(s/X,d/D)\mathcal J_{s,d},
 \qquad X=T^3,\quad D=T^2.}
\tag{9.377}
\]

Since \(HL/D=T^3\), reaching the local \(T^6\) target from (9.377)
requires the genuinely weaker arithmetic gate

\[
\boxed{
 \sum_{\substack{s\asymp X,\ d\asymp D\\(s,d)=1}}
 \mu(s)\mu(s+d)\mathcal W_0(s/X,d/D)
 \ll_\varepsilon T^{3+\varepsilon}
 =XD\,T^{-2+\varepsilon}.}
\tag{SC\(_{2/3}\)}
\]

Here \(\mathcal W_0\) ranges only over the bounded smooth family
produced by (9.373), rather than arbitrary coefficients.  The
shift_modulus_completion_ledger records exponents \(3\) for the zero-mode
amplitude, \(5\) for the \((s,d)\)-pair count, \(8\) trivially versus
target \(6\), and hence the exact missing pair saving \(T^2\).

This reduction explains both the opportunity and the barrier.  Theorem
1.1 of
[Matomäki--Teräväinen](https://arxiv.org/abs/1911.09076) applies
uniformly to a twisted Möbius sum on every interval of length
\(D=X^{2/3}\), but gives only a logarithmic relative saving.  The
averaged Chowla theorem likewise gives roughly logarithmic decay even
after averaging the shifts.  Either input leaves (9.377) at
\(T^{8-o(1)}\), not \(T^{6+\varepsilon}\).  Thus
\({\rm SC}_{2/3}\) is not proved by the cited literature.

Equations (9.372)--(9.377) nevertheless replace the coupled-kernel gate
on the decisive smooth face by a strictly simpler statement: no inverse
phase, no long-modulus dual spectrum, and no arbitrary \(a,b\)
coefficients remain.  The unresolved content is a fixed-power
two-dimensional Möbius correlation for shifts of length \(X^{2/3}\).
Proving \({\rm SC}_{2/3}\), or proving that the particular integral
family \(\mathcal J_{s,d}\) has an additional vanishing moment, would
close this balanced face.  Such vanishing is not a local algebraic
identity for the admitted smooth class.  Indeed, after scaling
\(h=Hp,\delta=Lq\) and taking \(x=y=0\), narrow nonnegative unit-mass
bumps around any fixed \(p_0q_0\ne0\) make
\(\mathcal J_{s,d}\) tend to
\(e(-HLp_0q_0/(ds))\ne0\).  Any zero moment must therefore come from a
global recombination of the actual AFE separation components, not from
(9.372) alone.  Neither that recombination nor
\({\rm SC}_{2/3}\) is asserted here.

### 9.58 The remaining saving is optimal short-Mertens mean square

The strength of \({\rm SC}_{2/3}\) can be measured without an
asymptotic argument.  Extend an arbitrary finite complex sequence
\((c_n)\) by zero, and let \(D\geq1\) be an integer.  Directly counting
the sliding intervals which contain an ordered pair gives

\[
\boxed{
 \sum_{x\in\mathbb Z}
 \left|\sum_{x<n\leq x+D}c_n\right|^2
 =
 \sum_{|h|<D}(D-|h|)
 \sum_{n\in\mathbb Z}c_n\overline{c_{n+h}}.}
\tag{9.378}
\]

There are no omitted edge terms in (9.378): a pair at distance
\(|h|<D\) belongs to exactly \(D-|h|\) of the displayed intervals.
The helper sliding_interval_energy_sides verifies this identity for
arbitrary complex finite coefficients, including windows longer than
the support.

Take \(c_n=\mu(n)1_{X<n\leq2X}\), with \(X=T^3\) and \(D=T^2\).
The diagonal \(h=0\) in (9.378) has order \(XD=T^5\).  The trivial
short-sum estimate gives \(XD^2=T^7\).  Consequently the optimal
diagonal-sized estimate

\[
\boxed{
 \sum_x\left|\sum_{x<n\leq x+D}\mu(n)1_{X<n\leq2X}\right|^2
 \ll_\varepsilon XD\,T^\varepsilon}
\tag{MS\(_{2/3}\)}
\]

would save exactly \(D=T^2\).  Dividing (9.378) by \(D\), it gives

\[
 \sum_{|h|<D}\left(1-\frac{|h|}{D}\right)
 \sum_n\mu(n)\mu(n+h)1_{X<n,n+h\leq2X}
 \ll_\varepsilon X\,T^\varepsilon,
\tag{9.379}
\]

which is precisely the \(T^3\) scale required in
\({\rm SC}_{2/3}\), for the Fejér shift kernel.  Smooth translated and
dyadic versions follow from the same identity after inserting the
corresponding window into \(c_n\).  A uniform version of
\({\rm MS}_{2/3}\) for the bounded family generated by (9.373) would
therefore be a sufficient replacement gate.

This does not prove that gate.  Present multiplicative-function
short-interval theorems show that the normalized short sum is small on
average, with logarithmic or qualitative decay.  They do not give the
diagonal-sized mean square \(XD\) in (MS\(_{2/3}\)).  Likewise, applying
Parseval to (9.378) merely rewrites the same correlation energy; it
cannot create the missing factor \(D\).  The executable
short_mertens_energy_ledger records exponents \(7\) trivially, \(5\) at
the optimal diagonal scale, and the resulting normalized target
exponent \(3\).

This matches the classical status of the short-Mertens moment problem.
Ng formulates the diagonal-sized moment as a Möbius-randomness
prediction and, even after assuming RH, records equivalences between
related moment formulations rather than a proof; the weaker conditional
estimate discussed there is only \(o(XD^2)\), not \(O(XD)\).  See
[The Möbius Function in Short Intervals, Section 4](https://www.cs.uleth.ca/~nathanng/RESEARCH/mobiusshort.pdf).

Thus the remaining \(T^2\) is no longer attributable to a Kloosterman
estimate, a completion tail, or a coefficient norm.  It is exactly the
gap between trivial and square-root mean square for Möbius sums in
length-\(X^{2/3}\) intervals.  This finite identity also explains why
elementary Selberg sieve cannot close the last face: doing so would
cross the parity barrier at the optimal mean-square scale.

### 9.59 The short-modulus zero mode is the equal-zeta-variable continuum

There is one last possible ambiguity in the preceding reduction.  The
zero frequency in (9.376) was created only after completing in \(h\) and
\(\delta\) modulo \(d=r-s\).  It could therefore conceivably be an
artifact which cancels the original \(h=0\) Poisson main term after all
dyadic pieces are recombined.  Keeping the pre-Poisson \(x\)-integral
settles this point exactly.

For \(d=r-s\ne0\), let \(\mathscr F_{r,s,\delta}(x)\) be the complete
integrand in (4.4) before the factor \(e(-hx/s)\), including the
\(t\)-integral.  First sum the complete smooth dyadic partitions in
\(h\) and \(\delta\), including the scales whose original integer
supports are empty.  Their zero dual coefficients then have the
continuous aggregate

\[
 \frac1{|d|}\int_{\mathbb R}\int_{\mathbb R}
 e\left(-\frac{h\delta}{ds}\right)
 \left\{\int_{\mathbb R}
 \mathscr F_{r,s,\delta}(x)e(-hx/s)\,dx\right\}
 dh\,d\delta .
\tag{9.380}
\]

All cutoffs may first be kept compact.  This order is essential: for one
fixed \(H\), the factor \(F_H(h)\) remains in (9.380), and Fourier
inversion gives a bump rather than a Dirac mass.  Only the complete
\(\sum_HF_H(h)=1\) aggregate gives

\[
 \int_{\mathbb R}e\left(-h\left(\frac xs+
                 \frac{\delta}{ds}\right)\right)dh
 =s\,\delta_0\left(x+\frac\delta d\right).
\tag{9.381}
\]

Thus (9.380) samples \(x=-\delta/d>0\).  At that point

\[
 \frac{xr+\delta}{s}=x,
 \qquad
 \exp\left(it\log\left(1+\frac\delta{xr}\right)\right)
 =\left(\frac sr\right)^{it}.
\tag{9.382}
\]

The same condition is visible without distributions.  If
\(\delta=m_1s-m_2r\), then

\[
 \boxed{\delta+(r-s)m_2=s(m_1-m_2).}
\tag{9.383}
\]

Consequently \(\delta=-(r-s)m_2\) is equivalent to \(m_1=m_2\).
Equation (9.381) is its continuous, post-Poisson version; it must not be
misstated as the original discrete \(m_1=m_2\) subsum, or as a
termwise identity for one \(H,L\)-box.  The nonzero dual frequencies
restore both the lattice and the empty-scale cancellation outside the
smooth regime in which (9.376) makes them negligible.

Now sum the zero coefficients before taking absolute values over all
outer gcd and dyadic partitions.  The factor \(s\) in (9.381) cancels
the \(s^{-1}\) in (4.5), while the change
\(\delta=-dx\) cancels \(|d|^{-1}\).  The arithmetic factor is therefore

\[
 \sum_{\substack{q,r,s\ge1\\(r,s)=1}}
 \frac{a_N(qr)a_N(qs)}{q\sqrt{rs}}
 \left(\frac sr\right)^{it}
 =\left|\sum_{n\leq N}\frac{a_N(n)}{n^{1/2+it}}\right|^2.
\tag{9.384}
\]

This is just the unique decomposition
\(q=(n_1,n_2),r=n_1/q,s=n_2/q\); it has no truncation error.  Since the
short-modulus completion has \(r\ne s\), its aggregate zero packet is
the right side of (9.384) minus the explicit diagonal
\(\sum_{n\leq N}a_N(n)^2/n\), multiplied by the common continuous
archimedean \(x\)-integral.

The balanced \(H=L=T^{5/2}\), \(|r-s|=T^2\) packet is only one
dyadic constituent of that aggregate.  Indeed \(HM/S\asymp1\), so its
fixed-\(H\) Fourier bump has \(x\)-width \(S/H\asymp M\), not a
power-smaller approximation to a point.  Thus (9.384) identifies the
globally recombined zero coefficients, but it neither replaces the
actual balanced weight \(\mathcal J_{s,d}\) by a Fejér kernel nor proves
that \({\rm MS}_{2/3}\) is necessary for every admitted weight.

This rules out identifying the two zero modes term by term.  The
original \(h=0\) mode is a zero frequency in the first Poisson
summation and combines with the AFE diagonal to give the LCM form in
(4.6).  The zero frequency in (9.380) is instead a major-arc component
of the off-diagonal long-mollifier square.  It is not identically zero;
after adding its explicit \(r=s\) diagonal it is a literal squared
modulus at the fully aggregated level.  A cancellation involving other
dyadic zero and nonzero frequencies is not excluded; it would have to be
proved by a global regrouping and is not an identity inside the single
balanced box (9.372)--(9.376).

The only exact regrouping presently known which crosses that boundary is
(9.361).  At Mellin frequency zero it uses

\[
 \sum_{d\mid n}\mu(d)
 \left(1-\frac{\log d}{\log N}\right)
 =1_{n=1}+\frac{\Lambda(n)}{\log N},
\tag{9.385}
\]

but the actual compact AFE contour contains the entire family
\(B_{N,i\tau}\), for which the many-prime terms in (9.364) return.  Hence
a genuinely weaker replacement for \({\rm MS}_{2/3}\) would be a uniform
shifted-energy estimate for \(B_{N,i\tau}\), including the reflected
cofactor boundary in (9.362), followed by contour recombination before
absolute convergence is lost.  The prime-power identity at
\(\tau=0\) alone is insufficient.

This boundary agrees with the established long-mollifier literature.
Farmer conjectures the mollified second-moment asymptotic for every fixed
\(\theta>0\), while the classical unconditional asymptotic for the
Conrey mollifier reaches only \(\theta<4/7\); see
[Farmer](https://doi.org/10.1112/S0025579300013723) and the summary in
[Bettin--Gonek, Section 1](https://arxiv.org/abs/1604.02740).  Radziwill
also proves that the long-mollifier off-diagonal is genuinely
non-negligible and relates it, under RH, to pair correlation; see
[arXiv:1207.6583](https://arxiv.org/abs/1207.6583).  These results do not
disprove the desired \(O(T^{1+\varepsilon})\) bound at \(\theta=3\), but
they show that it is a conjectural long-mollifier estimate rather than a
missing elementary completion lemma.

The executable helpers equal_zeta_index_shift_sides and
equal_zeta_index_gcd_factorization_sides verify (9.383)--(9.384) for
arbitrary finite complex coefficients and twists.  The helper
formal_mobius_log_divisor_coefficients verifies (9.385) in the free
\(\log p\) basis, so no floating-point logarithmic relation is being used.
Together they give a directly formalizable finite interface:

\[
 \boxed{
 \sum_{\rm all\ dyadic\ shift\ zero\ coefficients}
 =
 {\rm continuous\ equal\!-\!index\ mollifier\ square}
 -
 {\rm explicit\ diagonal}.}
\tag{9.386}
\]

Equation (9.386) is exact.  Separately, the balanced constituent is
bounded by \({\rm SC}_{2/3}\), and the Fejér specialization of that gate
is supplied by \({\rm MS}_{2/3}\).  No converse or final mean-square
estimate is asserted.

### 9.60 Density centering leaves the entire moving product boundary

The compact \(B_{N,i\tau}\) route in Section 9.55 has one more tempting
shortcut: subtract the mean coefficient, cancel the pole of \(\zeta\),
and shift the product-variable contour.  The finite boundary calculation
shows exactly what this does and does not remove.

Put

\[
 \mathcal M_{N,z}(w):=
 \sum_{d\leq N}\mu(d)
 \left(1-\frac{\log d}{\log N}\right)d^{z-w}.
\tag{9.387}
\]

On \({\rm Re}\,w>1\), absolute convergence and divisor convolution give

\[
 \boxed{
 \sum_{n\geq1}\frac{B_{N,z}(n)}{n^w}
 =\zeta(w)\mathcal M_{N,z}(w).}
\tag{9.388}
\]

Let

\[
 \beta_N(z):=\mathcal M_{N,z}(1),\qquad
 \widetilde B_{N,z}(n):=B_{N,z}(n)-\beta_N(z).
\]

Then the infinite Dirichlet series has the formally pole-cancelled form

\[
 \sum_{n\geq1}\frac{\widetilde B_{N,z}(n)}{n^w}
 =\zeta(w)\{\mathcal M_{N,z}(w)-\mathcal M_{N,z}(1)\}.
\tag{9.389}
\]

The bracket vanishes at \(w=1\).  This is an exact cancellation of the
principal density, but it is not an estimate for a finite product band.
For every integer \(X\geq1\), complete multiplicativity gives the
boundary-exact identity

\[
\boxed{
\begin{aligned}
 \sum_{n\leq X}\frac{\widetilde B_{N,z}(n)}{n^w}
={}&\{\mathcal M_{N,z}(w)-\beta_N(z)\}
       \sum_{m\leq X}\frac1{m^w}\\
 &-\sum_{d\leq N}
   \frac{\mu(d)(1-\log d/\log N)d^z}{d^w}
   \sum_{X/d<m\leq X}\frac1{m^w}.
\end{aligned}}
\tag{9.390}
\]

There is no asymptotic or omitted endpoint in (9.390).  In particular,
at \(w=1\) the separated first line is exactly zero, and the whole
centered prefix equals the negative moving product boundary in the
second line.  Thus pole centering migrates the arithmetic obligation to
the endpoint; it does not delete it.  This is the product-variable
counterpart of the reflected cofactor in (9.362).

The balanced transition also explains why a bare contour shift gives no
power.  Here

\[
 X=NM=T^{7/2},\qquad |\Delta|=X/T=T^{5/2}.
\tag{9.391}
\]

Moving a smooth short-product Perron integral from
\({\rm Re}\,w=1\) to \(1-c\), \(0\leq c\leq1/2\), gives the geometric
ratio

\[
 (N/X)^c=T^{-c/2}.
\]

The Mellin height of a relative \(T^{-1}\) product window is
\(|{\rm Im}\,w|\asymp T\).  The convexity bound for
\(\zeta(1-c+iv)\) costs \(T^{c/2+\varepsilon}\), exactly cancelling
that geometric gain.  On the critical line this ledger reads
\(T^{-1/4}\cdot T^{1/4+\varepsilon}=T^\varepsilon\).
Pointwise subconvexity leaves a small fixed saving, but a standalone
length-\(X\), width-\(X/T\) pair energy needs the full diagonal saving
\(X/T=T^{5/2}\).  The subconvex saving therefore does not close the
two-coefficient correlation.

The published long-polynomial comparison has the same boundary:

| input | what it proves | outcome for \(B_{N,i\tau}\) |
|---|---|---|
| exact density centering | cancels the \(w=1\) pole in (9.389) | the complete finite edge remains in (9.390) |
| zeta convexity on \(1-c\) | costs \(T^{c/2+\varepsilon}\) | exactly cancels \((N/X)^c\) |
| zeta pointwise subconvexity | improves one contour factor by a small fixed power | far short of diagonal-sized shifted energy |
| Goldston--Gonek long-polynomial formula | expresses the mean value through uniform coefficient correlations | requires, rather than proves, the correlation estimate for \(B_{N,i\tau}\) |
| Conrey--Keating length-\(T^3\) Type II framework | organizes long energies for divisor coefficients | does not transfer to the reciprocal Möbius coefficient without a new correlation theorem |

For the last two rows see
[Goldston--Gonek](https://doi.org/10.4064/aa-84-2-155-192) and
[Conrey--Keating](https://link.springer.com/article/10.1007/s40993-016-0056-4).
The former explicitly takes coefficient correlations as input; the
latter studies divisor-sum coefficients, whose automorphic/additive
divisor structure is absent from the inverse Euler factor in
\(B_{N,i\tau}\).

Consequently the compact-Mellin alternative is now an exact gate, not
an informal escape:

\[
\boxed{
\begin{aligned}
 {\rm CME}_{3}:\quad
 \int_{\mathbb R}(1+|\tau|)^{-A}
 \left|
 \sum_{0<|h|\ll H}\sum_{n\asymp X}
 \widetilde B_{N,i\tau}(n)
 \widetilde B_{N,i\tau}(n+h)
 \mathcal W_{\tau,h}(n/X)
 \right|d\tau
 \ll_{\varepsilon,A}XT^\varepsilon,\\
 X=T^{7/2},\qquad H=X/T=T^{5/2},
\end{aligned}}
\tag{9.392}
\]

uniformly for the bounded smooth family
\(\mathcal W_{\tau,h}\) produced by the compact AFE separation, together
with the three density/cross terms obtained by expanding
\(B=\widetilde B+\beta_N\) and the exact boundary term in (9.390).
The right side \(X\) is the diagonal scale; the unsigned pair count is
\(XH\), so (9.392) asks for the full saving \(H=T^{5/2}\).

The implication
\({\rm CME}_{3}\Rightarrow\) the balanced precompletion product packet
is a finite Mellin-inversion reduction: the factor \(1/X\) from
\((xy)^{-1/2}\) and the \(T\)-scale time transform turn the right side
of (9.392) into \(O(T^{1+\varepsilon})\).  No cited theorem proves
\({\rm CME}_{3}\), and (9.390)--(9.391) show why elementary pole
centering plus convexity does not do so.  This gate is an alternative
global formulation of the remaining long-mollifier correlation, not a
proved replacement for \({\rm SC}_{2/3}\).

The helper centered_selberg_product_boundary_sides verifies (9.390)
for arbitrary finite rational mollifier weights, arbitrary completely
multiplicative rational spectral weights, repeated divisor entries, and
every moving floor boundary.  Its pole-density test checks that the
bulk vanishes while the boundary survives exactly.

### 9.61 Mellin \(L^2\) returns the same long-polynomial problem

One might try to improve the pointwise convexity row above by using the
mean square of \(\zeta\) on the shifted \(w\)-line.  A finite Fourier
identity shows that this is not an independent input.

Let \(V\) be a fixed smooth cutoff on \([1/2,2]\), and define the finite
product polynomial

\[
 F_{z,X}(t):=
 \sum_{n\geq1}
 \frac{B_{N,z}(n)}{n^{1/2+it}}V(n/X).
\tag{9.393}
\]

For the Gaussian time weight, termwise integration is finite and gives

\[
\boxed{
\begin{aligned}
 &\int_{\mathbb R}e^{-t^2/(2T^2)}
 F_{z,X}(t)F_{z,X}(-t)\,dt\\
 &\quad=\sqrt{2\pi}\,T
 \sum_{m,n\geq1}
 \frac{B_{N,z}(m)B_{N,z}(n)}{\sqrt{mn}}
 V(m/X)V(n/X)
 \exp\left\{-\frac{T^2}{2}\log^2\frac mn\right\}.
\end{aligned}}
\tag{9.394}
\]

There is no positivity assumption in (9.394): the two coefficients have
the same \(z\), exactly as in (9.361).  The Gaussian restricts the right
side to

\[
 |\log(m/n)|\ll T^{-1},
 \qquad |m-n|\ll X/T=H,
\tag{9.395}
\]

up to arbitrary-power tails.  A general compact \(W(t/T)\) gives the
same finite bilinear identity with its Fourier transform in place of the
Gaussian.

Applying Cauchy--Schwarz to the left side of (9.394) asks for the
ordinary \(L^2\) norm of the length-\(X\) polynomial \(F_{z,X}\).
Opening \(B_{N,z}\) by (9.360) returns the same zeta-index times
mollifier-divisor product from (9.361), with the product cutoff retained.
Thus a sharp \(L^2\) theorem for \(F_{z,X}\) is already the compact
long-mollifier estimate one is trying to prove.

The general Montgomery--Vaughan mean-value inequality has scale
\((T+X)\sum|c_n|^2\).  Since \(X/T=H=T^{5/2}\), its long-polynomial term
loses exactly the window factor which \({\rm CME}_3\) must save.
Goldston--Gonek replace that loss by coefficient correlations, but for
the present coefficients those correlations are the right side of
(9.394).  Hence Mellin \(L^2\), general large sieve, and the
long-polynomial correlation formula form a closed circle; none is a
strictly weaker proved input.

Equations (9.393)--(9.395) do not rule out a coefficient-specific
bilinear argument which keeps both Möbius signs and \(h\delta\).  They
do rule out claiming that a standard zeta mean square, applied after
compact-Mellin centering, proves \({\rm CME}_3\).

### 9.62 Integer-gap rigidity on the pre-Poisson short-shift lattice

There is an exact refinement of the equal-index identity (9.383) on the
decisive short-shift support.  It is useful only if the distinction
between the original integer lattice and one fixed post-Poisson
frequency box is retained.

Put \(r=s+d\) in the original equation \(m_1s-m_2r=\delta\).  Suppose a
finite support satisfies

\[
 s\geq s_0,\qquad m_2\leq M_0,\qquad |d|\leq D_0,\qquad
 |\delta|\leq L_0,\qquad s_0>L_0+M_0D_0.
\tag{9.396}
\]

Then (9.383) gives the endpoint-exact inequality

\[
 |m_1-m_2|s=|\delta+m_2d|
 \leq L_0+M_0D_0<s_0\leq s.
\tag{9.397}
\]

Because \(m_1-m_2\) is an integer, (9.397) forces

\[
 \boxed{m_1=m_2=:m,\qquad \delta=-md.}
\tag{9.398}
\]

The strict inequality in (9.396) is essential; equality at the endpoint
does not force the integer gap to vanish.  In the dyadic notation used
above, \(s\geq S/2\), \(m_2\leq2M\), \(|d|\leq2D\), and
\(|\delta|\leq2L\), so the literal sufficient condition is

\[
 \frac S2>2L+4MD.
\tag{9.399}
\]

At the balanced short-shift corner,

\[
 S=T^3,\qquad M=T^{1/2+o(1)},\qquad
 D=T^{2+o(1)},\qquad L=T^{5/2+o(1)},
\]

(9.399) holds for all sufficiently large \(T\).  This includes the
fixed polylogarithmic enlargements in (5.3)--(5.8), because their right
side is \(T^{5/2}\log^{O_B(1)}T=o(T^3)\).  Thus every *original integer
solution* which contributes to this short-\(d\) support has equal zeta
indices.  Boxes with disjoint \(K\)- and \(M\)-supports are consequently
empty after the complete Poisson spectrum is recombined.

On the equal-index slice the inverse phase and the retained product
linearize without approximation.  Since \((r,s)=1\) and \(r=s+d\), one
has \((d,s)=1\) and \(d\bar r\equiv1\pmod s\).  Therefore

\[
 \boxed{
 e_s(-h\delta\bar r)
 =e_s(hmd\bar r)=e_s(hm),\qquad h\delta=-hmd.}
\tag{9.400}
\]

In particular, this slice has no oscillation in the shift \(d\).  Nor
does the remaining \(h,m\)-phase have a hidden power parameter:

\[
 \frac{HM}{S}=T^{5/2+1/2-3+o(1)}=T^{o(1)}.
\tag{9.401}
\]

After unit-scale normalization it is a bounded-frequency phase
\(e(cuv)\), so integration by parts cannot supply a fixed power of
\(T\).  To state precisely what may be linearized after Poisson, let
\(G_L,G_H\) denote the actual signed dyadic cutoff functions in
\(\delta,h\), extended by zero.
For one fixed \(q,R,S,K,M,L,H\) box, define its equal-index
divisibility subpacket by

\[
\begin{aligned}
 \mathcal E^{=}_{q;R,S,K,M,L,H}
 :={}&\frac2q
 \sum_{\substack{s,d\in\mathbb Z\\s\geq1,\ s+d\geq1\\(s,d)=1}}
 \frac{a_N(q(s+d))a_N(qs)F_R(s+d)F_S(s)}
      {\sqrt{s(s+d)}\,s}\\
 &\times
 \sum_{m\geq1}\sum_{h\in\mathbb Z}
 G_L(-md)G_H(h)e_s(hm)\,
 \mathscr K_{R,S,K,M}(s+d,s;-md,h).
\end{aligned}
\tag{9.402}
\]

All zero extensions in \(a_N,F_R,F_S,\mathscr K\) remain in force, so
(9.402) has no suppressed endpoint term.  It is an exact subpacket of
(4.5), with \(h\delta=-hmd\) retained, not a new estimate and not yet
the whole post-Poisson box.

The scope restriction is decisive.  In (4.5), after Poisson summation,
\(x\) is continuous and \(m_1=(xr+\delta)/s\) need not be an integer.
Consequently a fixed \(h\)-box still contains terms with
\(\delta\ne-md\); (9.397) cannot be applied to those terms separately.
Only summing the complete \(h\)-spectrum restores the original residue
class, at which point (9.398) applies and the complementary
\(\delta\ne-md\) packet cancels exactly by Poisson inversion.  This is
consistent with the fixed-\(H\) Fourier-width warning after (9.384).

Hence the new finite fact does not prove \({\rm SC}_{2/3}\),
\({\rm MS}_{2/3}\), or \({\rm CME}_3\).  It sharpens the location of the
obstruction: after complete \(h\)-recombination the balanced short-shift
face is a band-limited equal-zeta-index form with the naked pair
\(\mu(s)\mu(s+d)\); if one remains post-Poisson, the same obstruction is
split between (9.402) and its exactly cancelling frequency complement.
There is neither an extra \(m_1,m_2\) average nor a \(d\)-Kloosterman
phase available for the missing \(T^2\) saving.

The helpers balanced_short_shift_forces_equal_zeta_index and
equal_index_inverse_phase_sides verify (9.396)--(9.400) on arbitrary
finite integer inputs, including signed shifts and frequencies, the
strict support endpoint, and the modulus-one convention.

### 9.63 Keeping the common Mellin integral is an exact AFE loop

The compact-Mellin gate (9.392) took an absolute value before integrating
in \(\tau\).  Retaining that integral is genuinely weaker, but one must
check whether its common spectral parameter supplies a new
orthogonality.  A finite identity shows that it does not do so by itself.

Write

\[
 a_N(d):=\mu(d)\left(1-\frac{\log d}{\log N}\right)1_{d\leq N}
\]

and, for finite product cutoffs, expand the two factors in (9.361):

\[
\begin{aligned}
 &B_{N,i\tau}(x)B_{N,i\tau}(y)(xy)^{-i\tau}\\
 &\quad=
 \sum_{\substack{d\mid x\\e\mid y}}
 a_N(d)a_N(e)
 \left(\frac{de}{xy}\right)^{i\tau}\\
 &\quad=
 \sum_{\substack{x=dn\\y=em}}
 a_N(d)a_N(e)(nm)^{-i\tau}.
\end{aligned}
\tag{9.403}
\]

Thus both mollifier twists cancel against the *single* factor
\((xy)^{-i\tau}\).  If \(\Omega\) is a Schwartz function and

\[
 \widehat\Omega(u):=\int_{\mathbb R}\Omega(\tau)e^{-i\tau u}\,d\tau,
\]

finite termwise integration gives

\[
\boxed{
\begin{aligned}
 &\int_{\mathbb R}\Omega(\tau)
 B_{N,i\tau}(x)B_{N,i\tau}(y)(xy)^{-i\tau}\,d\tau\\
 &\qquad=
 \sum_{\substack{x=dn\\y=em}}
 a_N(d)a_N(e)\widehat\Omega(\log(nm)).
\end{aligned}}
\tag{9.404}
\]

There is one Fourier constraint in (9.404), on the product \(nm\).
There are not two constraints on \(d,e\), nor a condition \(d=e\) or
\(n=m\).  Repeated divisor representations of \(x\) and \(y\) are
retained on both sides.

For the actual AFE contour, first split the \(z=0\) residue from the
remaining vertical integral and insert finite cutoffs.  The boundary
value of the gamma/Mellin factor is an \(\Omega_t(\tau)\) of the form
used in (9.404), with the usual limiting interpretation at the split
residue.  Mellin inversion then says exactly

\[
 \widehat\Omega_t(\log(nm))=V_t(nm)
\tag{9.405}
\]

with the residue contribution included according to (2.3).  Consequently
the two surviving finite conditions are

\[
 x=dn,\qquad y=em,\qquad y-x=\Delta,\qquad nm\asymp T,
\tag{9.406}
\]

which are precisely the original shifted-divisor and AFE product
conditions (3.3)--(3.7).  On the balanced transition
\(n,m\asymp T^{1/2}\), the normalized phase
\(\log(nm/T)\) is of bounded size; it contains no parameter on which
integration by parts yields a fixed power.

This gives an exact logical comparison.  If the \(\tau\)-integral is
kept coupled to the shifted correlation, triangle inequality shows that
the resulting statement is weaker than \({\rm CME}_3\).  But (9.403)--
(9.406) reverse it to the original balanced AFE packet, so it is not an
independently proved replacement gate.  Any saving obtained while
retaining \(\tau\) must simultaneously exploit the two Möbius signs,
the shift equation, and the common product constraint; “Mellin
orthogonality” alone contributes no power.

The helper common_mellin_product_constraint_sides is the finite Laurent
model of (9.403).  For arbitrary rational mollifier and zeta weights,
an arbitrary pair kernel \(W(x,y)\), arbitrary positive and negative
common Mellin modes, and an arbitrary nonzero completely multiplicative
rational model \(\chi\), it checks

\[
\begin{aligned}
 &\sum_{d,e,n,m}a_da_ez_nz_mW(dn,em)
   \sum_k c_k\chi(nm)^{-k}\\
 &\quad=
 \sum_kc_k\sum_{x,y}W(x,y)
 \frac{
  \left(\sum_{dn=x}a_dz_n\chi(d)^k\right)
  \left(\sum_{em=y}a_ez_m\chi(e)^k\right)}
 {\chi(xy)^k}.
\end{aligned}
\tag{9.407}
\]

This is a directly formalizable finite-sum proposition.  Its tests use
both positive and negative modes, a nonsymmetric product-pair kernel,
and hand-computed rational values, so deleting the common
\((xy)^{-k}\) factor, dropping the shifted kernel, or replacing \(nm\)
by a divisor product is detected.

### 9.64 Long-polynomial large values see the same resolution cell

After (9.398), fix one smooth separated component of the pre-Poisson
equal-index band; the Selberg taper, fixed gcd stratum, and separated
archimedean factors may be absorbed into a bounded dyadic weight \(w\).
That component has the following long Dirichlet-polynomial energy
model.  This is sufficient for a direct applicability audit of the
coefficient-agnostic Guth--Maynard theorem; it is not a claim that every
unseparated moving weight is one product.

Let \(\Phi\) be smooth and compactly supported, put

\[
 D_X(t):=\sum_{s\asymp X}
 \frac{\mu(s)w(s/X)}{\sqrt{s}}s^{-it},
 \qquad
 \widehat\Phi(u):=\int_{\mathbb R}\Phi(v)e^{-iuv}\,dv.
\tag{9.408}
\]

Finite termwise Fourier inversion gives

\[
\boxed{
 \int_{\mathbb R}\Phi(t/T)|D_X(t)|^2\,dt
 =
 T\sum_{r,s\asymp X}
 \frac{\mu(r)\mu(s)w(r/X)\overline{w(s/X)}}{\sqrt{rs}}
 \widehat\Phi\!\left(T\log\frac rs\right).}
\tag{9.409}
\]

There is no endpoint error in (9.409); zero extension of \(w\) includes
both dyadic edges.  Rapid decay restricts the off-diagonal to

\[
 |r-s|\ll X/T,
\tag{9.410}
\]

up to arbitrary-power tails.  Conversely, one Fourier resolution cell
contains \(X/T\) adjacent coefficients.  At the decisive scale

\[
 X=T^3,\qquad X/T=T^2,
\tag{9.411}
\]

so the Fourier-cell multiplicity is exactly the missing
\({\rm SC}_{2/3}\) power.

For the coefficients in (9.408),
\(\sum_{s\asymp X}|w(s/X)|^2/s\asymp1\).  The diagonal scale in
(9.409) is therefore \(T\), whereas the classical Dirichlet-polynomial
mean-value theorem gives

\[
 (T+X)\sum_{s\asymp X}\frac{|w(s/X)|^2}{s}
 \ll T+X\asymp X=T^3.
\tag{9.412}
\]

Thus its exact normalized loss is \(X/T=T^2\).  Before the
\(s^{-1/2}\) normalization the same ledger reads \(TX=T^4\) on the
diagonal and \((T+X)X=T^6\) classically.

Guth--Maynard, Theorem 1.1, is an arbitrary-\(1\)-bounded-coefficient
large-value estimate.  In their reduction they state explicitly that
when the polynomial length \(N_{\rm GM}\geq T_{\rm GM}\), their theorem
already follows from the classical first term; the new argument is
used after reducing to \(N_{\rm GM}<T_{\rm GM}\).  See
[Guth--Maynard, proof of Theorem 1.1](https://arxiv.org/abs/2405.20552).
Here \(N_{\rm GM}=X=T^3\) and \(T_{\rm GM}=T\), so the theorem is on
that classical side of its range.  Its coefficient hypothesis accepts
\(\mu(s)w(s/X)\), but the conclusion is coefficient-agnostic and does
not exploit the Möbius sign to remove the coherent \(X/T\) block.

Consequently the new large-value theorem does not improve (9.412) at
this face.  This is stronger than saying that its published
applications concern shorter polynomials: the theorem's own first-term
reduction lands exactly at exponent \(3\) after normalization, against
the required exponent \(1\).  A usable large-value input would need a
new coefficient-specific estimate

\[
 \int\Phi(t/T)|D_X(t)|^2\,dt\ll_\varepsilon T^{1+\varepsilon}
\tag{9.413}
\]

for this Selberg--Möbius family.  By (9.409), (9.413) is the same
banded two-Möbius energy already isolated by
\({\rm SC}_{2/3}\)/\({\rm MS}_{2/3}\), not a weaker theorem currently
provided by large-value technology.

The helper long_polynomial_mean_value_ledger records the two exact
normalizations.  At polynomial exponent \(3\) and time exponent \(1\)
it returns resolution-cell exponent \(2\), unnormalized diagonal and
classical exponents \(4,6\), normalized exponents \(1,3\), and marks
both the Guth--Maynard long-range reduction and the absence of a
published Möbius-specific \(T^2\) saving.

### 9.65 The zero-Mellin balanced product is a pure reflected boundary

The zero-frequency decomposition (9.362) has a stronger exact form on
the products which actually occur in the balanced mollifier block.  Let

\[
 1<m<d\leq N,\qquad \mu(d)\ne0,\qquad x=dm.
\]

Then \(x\) is not a prime power.  Indeed, if \(x=p^j\), squarefreeness
and \(d>1\) force \(d=p\).  Since \(m>1\), one has \(j\geq2\) and hence
\(m=p^{j-1}\geq p=d\), contradicting \(m<d\).  Thus
\(\Lambda(dm)=0\), and (9.362) becomes the boundary-exact identity

\[
\boxed{
 B_{N,0}(dm)
 =-\sum_{\substack{k\mid dm\\kN<dm}}
 \mu(dm/k)\left(1-\frac{\log(dm/k)}{\log N}\right),
 \qquad k<m.}
\tag{9.414}
\]

The last inequality is also strict and exact: \(kN<dm\) and \(d\leq N\)
give \(k<dm/N\leq m\).  On the decisive scale

\[
 d\asymp N=T^3,\qquad m\asymp T^{1/2},
\]

the hypotheses of (9.414) hold for all sufficiently large \(T\).
Consequently the von-Mangoldt part of the compact coefficient is absent,
not merely small, at \(\tau=0\) on this balanced product support.  This
statement concerns \(B_{N,0}(dm)\); it does not remove the distinct
\(B=1\) prime slice of the Type-I/II principal density in Sections
9.40--9.42.

The energy expansion must still retain every boundary cross term.  Extend
the tapered formula algebraically to \(D>N\), and put

\[
 c_N(D):=\mu(D)\left(1-\frac{\log D}{\log N}\right),\qquad
 R_N(x):=\sum_{\substack{D\mid x\\D>N}}c_N(D),
\]

so that (9.362) is \(B_{N,0}=F_0-R_N\), where
\(F_0(x)=1_{x=1}+\Lambda(x)/\log N\).  For an arbitrary finite, possibly
nonsymmetric pair kernel \(W(x,y)\), bilinearity gives

\[
\boxed{
 \mathcal E_W(B,B)
 =\mathcal E_W(F_0,F_0)
 -\mathcal E_W(F_0,R_N)
 -\mathcal E_W(R_N,F_0)
 +\mathcal E_W(R_N,R_N).}
\tag{9.415}
\]

The two middle terms in (9.415) are different for a nonsymmetric kernel.
Thus neither may be merged or discarded before the actual AFE kernel has
been recombined.  On a support consisting only of products in (9.414),
the corresponding values of \(F_0\) vanish; this does not assert that the
global cross terms vanish on the remaining product ranges.

The boundary--boundary term has an exact two-short-cofactor unfolding.
For every integer \(X\geq1\), zero-extending \(W\) outside
\([1,X]^2\) gives

\[
\boxed{
\begin{aligned}
 \mathcal E_{R,W}(X)
 &:=\sum_{x,y\leq X}W(x,y)R_N(x)R_N(y)\\
 &=\sum_{D,E>N}c_N(D)c_N(E)
   \sum_{k\leq X/D}\sum_{\ell\leq X/E}W(Dk,E\ell),
 \qquad k,\ell<\frac XN .
\end{aligned}}
\tag{9.416}
\]

There is no floor or endpoint error in (9.416).  The strict cofactor
bounds follow from \(D,E>N\).  At
\(X=NM=T^{7/2}\), both cofactors have length

\[
 K=X/N=T^{1/2}.
\tag{9.417}
\]

The diagonal of (9.416) is elementary.  Taking
\(W(x,y)=1_{x=y}\) gives

\[
\boxed{
 \sum_{x\leq X}R_N(x)^2
 =\sum_{D,E>N}c_N(D)c_N(E)
   \left\lfloor\frac{X}{[D,E]}\right\rfloor .}
\tag{9.418}
\]

Only squarefree \(D,E\) contribute.  Write
\(q=(D,E),D=qr,E=qs\).  Then \(q,r,s\) are pairwise coprime and every
active term in (9.418) satisfies

\[
 q>\frac{N^2}{X},\qquad r,s<\frac XN.
\tag{9.419}
\]

For \(N=T^3,X=T^{7/2}\), this is
\(q>T^{5/2}\) and \(r,s<T^{1/2}\).  Formula (9.418), including its
literal floor, is therefore another reciprocal-LCM quadratic form to
which the finite gcd/LCM diagonalization applies.

The restriction (9.419) is **diagonal only**.  If the kernel in (9.416)
is supported on \(0<|x-y|\leq H\), an off-diagonal term instead obeys

\[
 Dk-E\ell=h,\qquad 0<|h|\leq H,\qquad k,\ell<K.
\tag{9.420}
\]

There is no condition \([D,E]\leq X\) in (9.420), so the high-gcd lower
bound in (9.419) cannot be imported.  Put
\(g=(k,\ell),k=gk_0,\ell=g\ell_0\), with
\((k_0,\ell_0)=1\).  Necessarily \(g\mid h\), and after choosing one
solution \((D_0,E_0)\), all solutions lie on

\[
\boxed{
 D=D_0+\ell_0t,\qquad E=E_0+k_0t,qquad
 k_0D_0-\ell_0E_0=h/g.}
\tag{9.421}
\]

Thus the exact reflected route reduces the nonzero shifted energy to a
weighted product
\(\mu(D_0+\ell_0t)\mu(E_0+k_0t)\), summed jointly over
\(g,k_0,\ell_0,h\) and the original smooth kernel.  This is a
two-Möbius affine correlation, not an elementary one-variable sieve
remainder.  At (9.417) the slopes have length \(T^{1/2}\), the long
variables have height \(T^3\), and the largest slopes leave a
\(T^{5/2}\)-length \(t\)-interval, the same transition scale as the
coupled-kernel obstruction.

Published truncated-divisor correlations do not cover this high level.
Goldston--Yıldırım define
\(\Lambda_R(n)=\sum_{d\mid n,d\leq R}\mu(d)\log(R/d)\), which is
\((\log R)B_{R,0}(n)\), and their moment range is
\(R=X^{\theta_k}\) with \(\theta_k<1/k\); for the second moment this is
\(R<X^{1/2}\).  See
[Goldston--Yıldırım, (1.2), Corollary 1](https://arxiv.org/abs/math/0412366).
Here \(R=N=T^3=X^{6/7}\), so that theorem does not estimate (9.416).
The reflected identity lowers the cofactors to \(T^{1/2}\), but it
leaves the two long Möbius factors in (9.421).  Existing averaged-Chowla
inputs provide qualitative or logarithmic cancellation, not the fixed
power required here.

The newer all-interval higher-uniformity theorem does enter the length
range but not the required strength or coefficient class.  Matomäki,
Shao, Tao, and Teräväinen prove Möbius--nilsequence discorrelation
\(\ll_A H(\log X)^{-A}\) for
\(H\geq X^{5/8+\varepsilon}\); see
[Higher uniformity I, Theorem 1.1](https://arxiv.org/abs/2204.03754).
The weighted-Chowla window has \(D=X^{2/3}\), and the shortest affine
\(t\)-interval in (9.421) has exponent \(5/6\) relative to the long
variable, so both pass the theorem's **length** threshold.  But the
second Möbius factor in (9.421) is not a fixed nilsequence.  Even if one
optimistically replaced the whole two-Möbius average by the theorem's
logarithmic factor, the pair exponent would remain
\(XD=T^{5-o(1)}\), whereas \({\rm SC}_{2/3}\) requires
\(T^{3+\varepsilon}\).  Arbitrarily high fixed logarithmic savings do
not supply the missing relative power \(T^{-2}\).

The finite helpers `balanced_selberg_reflection_sides`,
`reflected_pair_kernel_energy_sides`,
`reflected_boundary_pair_kernel_sides`, and
`reflected_boundary_diagonal_sides` verify (9.414)--(9.419) with exact
rational formal logarithms, arbitrary finite pair kernels, both distinct
cross terms, every moving endpoint, and the literal LCM floor.  These
identities close the zero-Mellin prime-support ambiguity and the diagonal
boundary energy.  They do **not** prove an estimate for (9.420)--(9.421),
nor do they control the nonzero compact Mellin frequencies in (9.364).
The already tested `determinant_line_coordinates` gives the exact finite
parametrization (9.421), including the divisibility condition \(g\mid h\).

### 9.66 The Perron--zeta-ratio escape enters the possible-zero region

The full zero-frequency coefficient cannot be discarded: (9.380)--(9.386)
identify it exactly with a continuous equal-index long-mollifier square minus
the explicit diagonal.  A different possible global treatment is to keep the
tapered mollifier intact and use Perron inversion.  Put \(L=\log N\).  For
\(s=\sigma+it\) and \(c>\max(0,1-\sigma)\), absolute convergence of
\(1/\zeta(s+w)\) gives the exact identity

\[
 \boxed{
 M_N(s):=\sum_{d\leq N}\frac{\mu(d)}{d^s}
              \left(1-\frac{\log d}{L}\right)
 =\frac1L\frac1{2\pi i}\int_{(c)}
       \frac{N^w}{w^2\zeta(s+w)}\,dw .}
\tag{9.422}
\]

Indeed, the inverse Mellin kernel is literally

\[
 \frac1{2\pi i}\int_{(c)}\frac{(N/d)^w}{w^2}\,dw
 =\begin{cases}\log(N/d),&d<N,\\0,&d\geq N,\end{cases}
\tag{9.423}
\]

so the endpoint \(d=N\) contributes zero and there is no truncation error.
On the critical line the absolute Dirichlet-series contour must satisfy
\(c>1/2\), and

\[
 \zeta(s)M_N(s)
 =\frac1L\frac1{2\pi i}\int_{(c)}
       \frac{N^w}{w^2}\frac{\zeta(s)}{\zeta(s+w)}\,dw .
\tag{9.424}
\]

This representation does not by itself remove the long-polynomial loss.  On
the limiting absolute-convergence line \(c=1/2+\eta\), a direct second-moment
estimate pays the square of \(N^c\).  Thus for \(N=T^3\), up to logarithms,

\[
 T\,N^{2c}=T^{\,1+6c}
           =T^{\,4+6\eta},
 \qquad
 \underbrace{(4)-(1)}_{\text{power gap}}=3.
\tag{9.425}
\]

More generally, to reach \(T^{1+\varepsilon}\) through this direct contour
ledger one needs \(c\leq\varepsilon/6\).  Hence the contour must be moved from
the half-plane of absolute convergence into a region where off-critical-line
zeros are not unconditionally excluded.  Every zero met during such a shift
produces a reciprocal-zeta pole at \(w=\rho-s\).  If \(\rho\) is simple, its
exact residue is

\[
 \boxed{
 \operatorname*{Res}_{w=\rho-s}
 \frac{\zeta(s)N^w}{Lw^2\zeta(s+w)}
 =\frac{\zeta(s)N^{\rho-s}}
        {L(\rho-s)^2\zeta'(\rho)} .}
\tag{9.426}
\]

For a multiple zero one must use the corresponding higher-order residue;
(9.426) is not valid.  A zero-density theorem can count possible crossed
zeros but does not bound the inverse derivative in (9.426), nor does it
supply the required higher-order residue control.  The available upper-bound
literature does not supply the
needed unconditional all-zero input: Bui--Florea--Milinovich obtain
*conditional* upper bounds for negative moments of \(\zeta'(\rho)\) over a
subfamily expected to have full density, not the unconditional weighted
residue sum here; see
[their abstract](https://arxiv.org/abs/2310.03949).  Gao--Zhao's lower-bound
results likewise assume RH and simple zeros; see
[their abstract](https://arxiv.org/abs/2208.06922).

The finite helper `perron_zeta_ratio_ledger` tests the power accounting in
(9.425): cutoff exponent \(3\), time exponent \(1\), and limiting contour
\(1/2\) give contour-square cost \(3\), direct exponent \(4\), target
exponent \(1\), and target contour ceiling \(0\) when no fixed power loss is
allowed.  This is an exact obstruction certificate, not a proof that every
possible zero-sensitive contour argument must fail.  It shows precisely what
this proposed escape would have to add: cancellation of the complete weighted
zero-residue family (or a different reciprocal-zeta estimate of equivalent
strength).  No such unconditional estimate has been proved here, so the
coupled-kernel gate remains open.

### 9.67 Conditional RH closure through shifted negative moments

Although Section 9.66 does not give an unconditional bound, it can be closed
under RH with a published negative-moment theorem.  This separates the
zero-sensitive obstruction from the finite two-Möbius algebra.

Fix \(0<c<1/2\).  Under RH, every zero \(\rho\) has
\(\Re(\rho-s)=0\) when \(\Re s=1/2\).  Therefore the rectangle between the
original line \(c_0>1/2\) in (9.424) and the line \(c>0\) contains no pole of
\(1/\zeta(s+w)\); the pole at \(w=0\) is also to its left.  The RH pointwise
lower bound used by Bui--Florea gives, for fixed \(c\),
\(1/\zeta(1/2+c+iu)=|u|^{o(1)}\).  Consequently the \(w^{-2}\) factor kills
the horizontal sides along a sequence of growing rectangles, and (9.424)
holds on \(\Re w=c\):

\[
 \zeta(s)M_N(s)
 =\frac1L\frac1{2\pi i}\int_{(c)}
       \frac{N^w}{w^2}\frac{\zeta(s)}{\zeta(s+w)}\,dw
 \qquad (\mathrm{RH}).
\tag{9.427}
\]

The required reciprocal-zeta input is now available.  Bui--Florea,
[Theorem 1.2](https://arxiv.org/abs/2302.07226), under RH and with their
\(k=2\), implies for every fixed \(c>0\)

\[
 \frac1U\int_U^{2U}
 \left|\zeta\!\left(\frac12+c+iu\right)\right|^{-4}du
 \ll_c (\log\log U)^2(\log U)^4.
\tag{9.428}
\]

This is exactly the fourth negative moment needed after Hölder, not merely
the \(k<1/2\) asymptotic range quoted in the abstract.  Combine (9.428) with
the classical fourth moment

\[
 \int_T^{2T}|\zeta(1/2+it)|^4dt\ll T(\log T)^4.
\tag{9.429}
\]

For \(v\in\mathbb R\), let \(U_v=2+T+|v|\).  Decompose the interval
\([T+v,2T+v]\), after reflection when necessary, into dyadic intervals of
height at most \(U_v\).  Their geometric lengths sum to \(O(U_v)\), and the
extra logarithmic number of intervals is absorbed below.  Hölder gives

\[
 \left\|
 \frac{\zeta(1/2+it)}
      {\zeta(1/2+c+i(t+v))}
 \right\|_{L^2(T,2T)}
 \ll_c (TU_v)^{1/4}(\log U_v)^{O(1)}.
\tag{9.430}
\]

Minkowski is now harmless because the Perron kernel retains its full
\((c^2+v^2)^{-1}\) decay.  Splitting at \(|v|=3T\), (9.430) gives

\[
 \begin{aligned}
 &\int_{\mathbb R}\frac1{c^2+v^2}
 \left\|
 \frac{\zeta(1/2+it)}
      {\zeta(1/2+c+i(t+v))}
 \right\|_2\,dv \\
 &\hspace{35mm}\ll_c T^{1/2}(\log T)^{O(1)},
 \end{aligned}
\tag{9.431}
\]

since the far tail is bounded by
\(T^{1/4}\int_T^\infty v^{-7/4}(\log v)^{O(1)}dv\).
Equations (9.427) and (9.431) therefore prove the conditional estimate

\[
 \boxed{
 \int_T^{2T}|\zeta(1/2+it)M_N(1/2+it)|^2dt
 \ll_c N^{2c}T(\log T)^{O(1)}
 \qquad (\mathrm{RH}).}
\tag{9.432}
\]

For \(N=T^\theta\), choose \(c=\varepsilon/(4\theta)\).  Then
\(N^{2c}=T^{\varepsilon/2}\), so the logarithms are absorbed and (9.432)
is \(\ll_{\varepsilon,\theta}T^{1+\varepsilon}\).  In particular the full
mollified second moment, and hence its off-diagonal contribution after the
already proved main-term bound, has the target size at \(\theta=3\)
**conditional on RH**.  The helper `rh_perron_negative_moment_ledger`
verifies the rational power calculation: for target epsilon \(1/100\) and
\(\theta=3\), it selects \(c=1/1200\), spends \(1/200\), and retains
power margin \(1/200\).  Its unconditional-coverage flag is deliberately
false.

### 9.68 The known zero-free consequence is vacuous at dyadic \(\theta=3\)

There is a precise published calibration of how close the desired estimate
is to RH.  Bettin--Gonek use the same tapered mollifier and write

\[
 I_N(T_1,T_2):=
 \int_{T_1}^{T_2}|M_N(1/2+it)|^2|\zeta(1/2+it)|^2dt.
\tag{9.433}
\]

Their
[Theorems 1 and 2](https://arxiv.org/abs/1604.02740) prove the following
one-way implications.  If, for every \(\varepsilon>0\), the bound
\(I_N\ll_\varepsilon T^{1+\varepsilon}\) holds **uniformly for every**
\(2\leq N\leq T^\theta\), then

\[
 \begin{array}{rcl}
 I_N(0,T)\ll T^{1+\varepsilon}
 &\Longrightarrow&
 \zeta(\rho)\ne0\quad\text{for }
 \Re\rho>\dfrac12+\dfrac1{2\theta},\\[2mm]
 I_N(T,2T)\ll T^{1+\varepsilon}
 &\Longrightarrow&
 \zeta(\rho)\ne0\quad\text{for }
 \Re\rho>\dfrac12+\dfrac2\theta.
 \end{array}
\tag{9.434}
\]

The interval is decisive.  At \(\theta=3\), (9.434) becomes

\[
 [0,T]:\quad \Re\rho\leq\frac23,
 \qquad
 [T,2T]:\quad \Re\rho\leq\frac76.
\tag{9.435}
\]

The second conclusion is outside the critical strip and is therefore
vacuous.  In fact the dyadic consequence becomes nontrivial only when
\(\theta>4\).  Thus Bettin--Gonek do **not** show that the present dyadic
\(\theta=3\) target implies RH or even a new zero-free region.  Their
\(\theta=\infty\) consequence implies RH only because the boundary in
(9.434) tends to \(1/2\) as arbitrarily long mollifiers are admitted.

Their single-fixed-off-line-zero model also displays the dyadic displacement
that the crude fixed-line Perron estimate loses.  Under the hypothetical
configuration stated in their introduction, a simple
\(\rho_0=\beta_0+i\gamma_0\), \(\beta_0>1/2\), contributes

\[
 \begin{aligned}
 I_N(T,2T)
 ={}&c_1\frac{N^{2\beta_0-1}}{T^3}
       \frac{\log T}{\log^2N}
 \left(1+\Re\!\left(
 N^{2i\gamma_0}\frac{|\zeta'(\rho_0)|^2}{\zeta'(\rho_0)^2}
 \right)+o(1)\right)\\
 &+O\!\left(T^{1+\varepsilon}
       +\frac{N^{\beta_0-1/2+\varepsilon}}T\right).
 \end{aligned}
\tag{9.436}
\]

Formula (9.436) is a model under their explicit zero-configuration
assumption, not an unconditional expansion over all zeros.  Its
\(T^{-3}\) factor nevertheless identifies a concrete requirement for a
useful residue treatment: retain the separation between the fixed zero
height and the dyadic observation window.  Replacing the shifted ratio by a
global negative moment discards precisely this geometry.

The exact helper `long_mollifier_zero_free_ledger` records (9.434).  At
\(\theta=3\) it returns \(2/3\) for \([0,T]\), \(7/6\) for \([T,2T]\),
and marks only the first as nontrivial.  This neither proves the desired
upper bound nor makes the Perron zero residues harmless; it rules out the
incorrect meta-objection that the dyadic \(\theta=3\) estimate is already
known to imply RH.

### 9.69 A boundary-exact master for the secondary zero modes

The first zero mode must not be counted twice.  The original Poisson
frequency \(h=0\) in Section 4 is already combined with the explicit
diagonal in (4.6), giving \(T\mathcal Q_{N,T}\) and the archimedean
correction in (4.8).  The present subsection concerns only zero or
singular modes created by the later completion, reflection, and dyadic
recombination of the original \(h\ne0\) remainder.

Fix a finite product box \(1\leq x,y\leq X\).  Let

\[
 \mathfrak P_X=\{\pi=(\sigma,h,\delta,\nu)\}
\tag{9.437}
\]

be a supplied finite packet family at that stage: \(\sigma\)
is the AFE direction, \(h\ne0\) is the original shifted-divisor frequency,
\(\delta\in\mathbb Z\) is the unrestricted additive shift, and \(\nu\)
records every dyadic scale.  Write \(W_\pi(x,y)\) for the original smooth
weight,
including its sign and all endpoint cutoffs, and put

\[
 W(x,y):=\sum_{\pi\in\mathfrak P_X}W_\pi(x,y),
 \qquad W_\pi(x,y)=0\quad\text{outside }[1,X]^2.
\tag{9.438}
\]

No absolute value is taken in (9.438).  Formula (2.4) uses the symmetric
AFE and has already folded its two functional-equation directions into
the factor \(2\).  If that formula is unfolded instead, both values of
\(\sigma\) must occur in \(\mathfrak P_X\) before (9.438) is formed.

Let \(F(x)\) be the completed zero-Mellin coefficient.  To allow the two
reflected sides to remain genuinely nonsymmetric, take finite long-divisor
weights \(c_D^{\rm L},c_E^{\rm R}\), and define

\[
 \begin{aligned}
 R_{\rm L}(x)&:=\sum_{\substack{D\mid x\\D>N}}c_D^{\rm L},
 &B_{\rm L}(x)&:=F(x)-R_{\rm L}(x),\\
 R_{\rm R}(y)&:=\sum_{\substack{E\mid y\\E>N}}c_E^{\rm R},
 &B_{\rm R}(y)&:=F(y)-R_{\rm R}(y).
 \end{aligned}
\tag{9.439}
\]

For the finite explicit-diagonal weights \(d_x\), the whole secondary-zero
packet is

\[
 \mathcal R^{(0)}_{\rm sec}
 :=\sum_{\pi\in\mathfrak P_X}\sum_{x,y\leq X}
 W_\pi(x,y)B_{\rm L}(x)B_{\rm R}(y)
 -\sum_{x\leq X}d_xB_{\rm L}(x)B_{\rm R}(x).
\tag{9.440}
\]

Thus (9.440) retains both AFE directions, all \(h,\delta,\nu\), the
original smooth weights, and the explicit diagonal in one formula.  Its
four reflected pieces are exactly

\[
 \mathcal R^{(0)}_{\rm sec}
 =E_W(F,F)-E_W(F,R_{\rm R})-E_W(R_{\rm L},F)
  +E_W(R_{\rm L},R_{\rm R})-\mathcal D_B.
\tag{9.441}
\]

The two cross terms in (9.441) are distinct; no symmetry is used to merge
them.  The reflected--reflected term has the boundary-exact unfolding

\[
 \begin{aligned}
 E_W(R_{\rm L},R_{\rm R})
 &=\sum_{D>N}\sum_{E>N}c_D^{\rm L}c_E^{\rm R}K(D,E),\\
 K(D,E)&:=
 \sum_{1\leq k\leq\lfloor X/D\rfloor}
 \sum_{1\leq \ell\leq\lfloor X/E\rfloor}W(Dk,E\ell).
 \end{aligned}
\tag{9.442}
\]

The floors and the zero extension in (9.438) contain every finite endpoint;
there is no boundary or truncation error in (9.439)--(9.442).  The earlier
AFE archimedean error remains the already isolated
\(\mathcal E_{\rm arch}\) in (4.8), not a new term in this master identity.

Now choose finite density weights \(p_D,q_E\) on the two long-divisor
supports, with \(\sum_Dp_D=\sum_Eq_E=1\).  Define

\[
 \rho_D:=\sum_Eq_EK(D,E),\qquad
 \kappa_E:=\sum_Dp_DK(D,E),\qquad
 m:=\sum_{D,E}p_Dq_EK(D,E),
\tag{9.443}
\]

and center only once:

\[
 K^\circ(D,E):=K(D,E)-\rho_D-\kappa_E+m.
\tag{9.444}
\]

Then the weighted row and column sums vanish identically,

\[
 \sum_Eq_EK^\circ(D,E)=0,
 \qquad
 \sum_Dp_DK^\circ(D,E)=0.
\tag{9.445}
\]

Put \(C_{\rm L}=\sum_Dc_D^{\rm L}\) and
\(C_{\rm R}=\sum_Ec_E^{\rm R}\).  The full resonant projection of the
reflected boundary is the explicit three-term expression

\[
 \begin{aligned}
 \mathcal P_{\rm res}
 &:=(c^{\rm L})^{\!t}(K-K^\circ)c^{\rm R}\\
 &=C_{\rm R}\sum_Dc_D^{\rm L}\rho_D
  +C_{\rm L}\sum_Ec_E^{\rm R}\kappa_E
  -mC_{\rm L}C_{\rm R}.
 \end{aligned}
\tag{9.446}
\]

Consequently define

\[
 \begin{aligned}
 \mathcal M_{\rm res}
 &:=
 E_W(F,F)-E_W(F,R_{\rm R})-E_W(R_{\rm L},F)
 +\mathcal P_{\rm res}-\mathcal D_B,\\
 \mathcal R_{\rm cent}
 &:=(c^{\rm L})^{\!t}K^\circ c^{\rm R}.
 \end{aligned}
\tag{9.447}
\]

Equations (9.441)--(9.447) give the finite exact master identity

\[
 \boxed{\mathcal R^{(0)}_{\rm sec}=\mathcal M_{\rm res}+\mathcal R_{\rm cent}.}
\tag{9.448}
\]

This is the finite algebraic part of the first required milestone, but not
yet its complete analytic instantiation or an estimate.  Arbitrary
probability weights \(p,q\) give an algebraically valid centering; the next
analytic task is to derive the *actual* principal density from the fully
recombined AFE packet and then decide which of the following occurs:

1. \(\mathcal M_{\rm res}\) is another reciprocal-LCM form and is
   \(O(T^{1+\varepsilon})\);
2. it cancels with the other AFE direction or the explicit diagonal;
3. it is a genuine secondary main term missing from the present asymptotic.

No one of these alternatives is asserted here.  Likewise, (9.448) by
itself gives no power saving for \(\mathcal R_{\rm cent}\).  The finite
helper `zero_frequency_reflected_master_sides` verifies (9.438)--(9.448)
over exact rational data, rejects original \(h=0\), retains the packet
labels, and checks both identities in (9.445).  A second finite fixture
changes \(p,q\) and proves that \(\mathcal M_{\rm res}\) and
\(\mathcal R_{\rm cent}\) separately change while their sum (9.448) does
not.  Thus an arbitrary centering cannot be advertised as the canonical
principal-mode extraction; deriving the AFE density is a genuine analytic
step.  Moreover, the helper accepts the kernels \(W_\pi\) as data: it does
not construct the analytic adapter from (4.5), through every later
completion and reflection, to a proved exhaustive \(\mathfrak P_X\).
Equation (4.5) remains the complete uncompleted \(h,\delta\) master; the
packet-by-packet adapter into (9.437)--(9.440) is still to be written.

### 9.70 The centered operator gate and the global TT* split

Let \(\mathbf c_{\rm L},\mathbf c_{\rm R}\) be the two reflected coefficient
vectors.  The elementary operator inequality is

\[
 |\mathcal R_{\rm cent}|
 \leq \|K^\circ\|_{2\to2}
       \|\mathbf c_{\rm L}\|_2\|\mathbf c_{\rm R}\|_2.
\tag{9.449}
\]

For the balanced normalization used in Sections 9.43--9.64, the raw
coupled sum has exponent \(5\), while the required local target has
exponent \(3\).  After keeping the same coefficient norms and packet
normalization on both sides of (9.449), the centered-operator gate must
therefore save

\[
 T^{5-3}=T^2.
\tag{9.450}
\]

For the one fixed Möbius vector, such a \(2\to2\) estimate is a sufficient
condition.  It is literally equivalent to the bilinear estimate only when
the latter is required uniformly over both Euclidean unit balls.  After
squaring by \(TT^*\), (9.450) becomes a \(T^4\) saving in the quadratic
norm.  The exact exponent helper records this as
`required_operator_saving_exponent=2` and
`required_ttstar_saving_exponent=4`; it does not assert either estimate.

The point of preserving all outer indices is that \(TT^*\) must be formed
globally.  After the affine-line parametrization, let

\[
 u=(g,k_u,\ell_u,h,\delta,\nu,\sigma),
 \qquad \mathcal T_{u,t}
\tag{9.451}
\]

denote one row of the centered coupled operator.  Only after summing all
such rows do we expand

\[
 \|\mathcal T^*a\|_2^2
 =\sum_{u,v}a_u\overline{a_v}
   \sum_t\mathcal T_{u,t}\overline{\mathcal T_{v,t}}.
\tag{9.452}
\]

The cross-row incidence invariant is

\[
 \det(u,v)=k_u\ell_v-k_v\ell_u.
\tag{9.453}
\]

Thus (9.452) has the exact, pre-estimate split

\[
 \|\mathcal T^*a\|_2^2
 =\mathfrak G_{\det=0}(a)+\mathfrak G_{\det\ne0}(a).
\tag{9.454}
\]

The \(\det=0\) parallel-slope orbit is resonant.  Its estimate must use
the same exact reflection data as \(\mathcal M_{\rm res}\), the explicit
diagonal, and both reflected cross terms; it is not legitimate to discard
it by centering alone.  These terms are not literally added:
\(\mathcal M_{\rm res}\) is a pre-Cauchy bilinear term, whereas
\(\mathfrak G_{\det=0}\) is part of the squared \(TT^*\) norm of
\(\mathcal R_{\rm cent}\).  Only \(\mathfrak G_{\det\ne0}\) is a candidate for reciprocity,
Poisson/Voronoi completion, Kuznetsov, or a Deshouillers--Iwaniec type
spectral large sieve.  This ordering also explains why decomposing one
Möbius factor can help only *inside* the global dispersion: decomposing a
fixed affine line first returns the unavailable pointwise Chowla problem.

The helper `coupled_ttstar_determinant_split_sides` verifies (9.452)--(9.454)
as a finite matrix identity.  It supplies no spectral estimate and makes no
claim that the determinant-zero term has already recombined correctly with
(9.447).  The three correctly normalized remaining tasks are:

\[
 \boxed{
 \text{evaluate }\mathcal M_{\rm res}\text{ before Cauchy},\quad
 \text{bound }\mathfrak G_{\det=0}\text{ in the }TT^*\text{ norm},\quad
 \text{then prove the }T^4\text{ TT* saving on }
 \mathfrak G_{\det\ne0}.}
\tag{9.455}
\]

### 9.71 The actual zero-mode projector has rank above product centering

Equations (9.384) and (9.394) determine the canonical aggregate more
precisely than an arbitrary choice of \(p,q\).  Let \(\Omega(t)\) denote
the common time/archimedean weight after the complete \(h,\delta\), dyadic,
and AFE recombination, and use the convention

\[
 \widehat\Omega(\xi):=\int_{\mathbb R}\Omega(t)e^{it\xi}\,dt.
\tag{9.456}
\]

The equal-index factorization (9.384), including its explicit diagonal,
then gives the finite Fourier Gram

\[
 \mathcal Z_\Omega+\mathcal D_\Omega
 =\sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{\sqrt{de}}\,
   \widehat\Omega\!\left(\log\frac ed\right).
\tag{9.457}
\]

Hence the secondary zero packet after subtracting that diagonal is exactly

\[
 \boxed{
 \mathcal Z_\Omega
 =\sum_{\substack{d,e\leq N\\d\ne e}}
   \frac{a_N(d)a_N(e)}{\sqrt{de}}\,
   \widehat\Omega\!\left(\log\frac ed\right).}
\tag{9.458}
\]

There is no asymptotic, endpoint deletion, or coefficientwise absolute
value in (9.457)--(9.458).  For the Gaussian specialization
\(\Omega_T(t)=e^{-t^2/(2T^2)}\),

\[
 \widehat\Omega_T(\xi)
 =\sqrt{2\pi}\,T e^{-T^2\xi^2/2}.
\tag{9.459}
\]

Remove the common positive factor \(\sqrt{2\pi}T\), restrict to the three
indices \(1,2,4\), and put

\[
 u:=e^{-T^2(\log2)^2/2}\in(0,1).
\tag{9.460}
\]

The principal Gram and its diagonal-removed kernel are respectively

\[
 G_T=
 \begin{pmatrix}
 1&u&u^4\\
 u&1&u\\
 u^4&u&1
 \end{pmatrix},
 \qquad
 G_T^{\ne}=
 \begin{pmatrix}
 0&u&u^4\\
 u&0&u\\
 u^4&u&0
 \end{pmatrix}.
\tag{9.461}
\]

Direct expansion gives

\[
 \boxed{
 \det G_T=(1-u^2)^3(1+u^2)>0,
 \qquad
 \det G_T^{\ne}=2u^6>0.}
\tag{9.462}
\]

Thus both matrices in (9.461) have rank \(3\).  By contrast, every
row/column/grand projection produced by (9.443)--(9.446) has the form

\[
 K-K^\circ=\rho\,\mathbf1^t+\mathbf1\,\kappa^t
             -m\mathbf1\mathbf1^t,
 \qquad
 \operatorname{rank}(K-K^\circ)\leq2.
\tag{9.463}
\]

Consequently no product-density double centering can move the whole
aggregate (9.457), or even its diagonal-removed Gaussian specialization
(9.458), into \(\mathcal M_{\rm res}\).  The canonical resonant object is
the full time-Fourier projector

\[
 \Pi_\Omega(d,e):=\widehat\Omega\!\left(\log\frac ed\right),
\tag{9.464}
\]

not one constant row or column mode.  This resolves the density ambiguity
in the following precise sense: the actual principal object is known, but
it is a high-rank banded operator.  Subtracting it would merely name the
entire correlation in (9.458) as a secondary term; estimating that term is
the long-polynomial/short-Mertens gate (9.409)--(9.413), not an elementary
LCM diagonal.

The calculation does not exclude cancellation with nonzero completion
frequencies after a still larger global identity.  It does prove that the
explicit diagonal and any row/column product-density projection alone
cannot provide that cancellation.  The exact helper
`equal_index_geometric_gram_rank_ledger` records (9.462): at the rational
formal value \(u=1/2\), the two determinants are \(135/256\) and \(1/32\),
while the projection-rank cap is \(2\).

### 9.72 Determinant zero means equal primitive slope

The determinant-zero term in (9.454) simplifies further on the actual
affine-line support.  Every row comes from

\[
 k=gk_0,\qquad \ell=g\ell_0,\qquad
 k_0,\ell_0\geq1,\qquad (k_0,\ell_0)=1.
\tag{9.465}
\]

Hence, for two rows \(u,v\),

\[
 k_u\ell_v=k_v\ell_u
 \quad\Longrightarrow\quad
 (k_u,\ell_u)=(k_v,\ell_v).
\tag{9.466}
\]

Indeed, coprimality of \(k_u,\ell_u\) first gives \(k_u\mid k_v\);
interchanging \(u,v\) gives \(k_v\mid k_u\), so the positive \(k\)'s
are equal, and then so are the \(\ell\)'s.  Therefore the zero-determinant
Gram term is exactly

\[
 \boxed{
 \mathfrak G_{\det=0}(a)=\sum_{(k,\ell)=1}
 \sum_t\left|
   \sum_{\substack{u:\,(k_u,\ell_u)=(k,\ell)}}
   a_u\mathcal T_{u,t}
 \right|^2.}
\tag{9.467}
\]

There are no collisions between distinct primitive slopes in (9.467).
The term is positive semidefinite, but it is not diagonal in the remaining
\(g,h,\delta,\nu,\sigma\) labels: those rows must still be recombined
*inside* the square for each fixed \((k,\ell)\).  Thus determinant zero
cannot cancel against another slope after \(TT^*\); any reduction must
come from the AFE signs, \(h\)-average, common-factor average, or an exact
same-slope identity before the square is estimated.

This changes the resonant subproblem in (9.455) to the sharper finite gate

\[
 \boxed{
 \sum_{(k,\ell)=1}
 \left\|\sum_{u:\,\operatorname{slope}(u)=(k,\ell)}
 a_u\mathcal T_{u,\bullet}\right\|_2^2
 \quad\text{with all outer signs retained}.}
\tag{9.468}
\]

The helper `coupled_ttstar_determinant_split_sides` now rejects
nonprimitive or nonpositive slopes.  Its finite test includes two distinct
rows with the same primitive slope and verifies that these, and only these,
enter the determinant-zero cross block.  Formula (9.468) is an exact
reduction, not a bound.

### 9.73 Type expansion does not diagonalize a resonant orbit

There are two unrelated letters which must not be conflated in the next
dispersion step.  The product carried by the original AFE packet is

\[
 a_{\mathrm{AFE}}=h\delta,
\tag{9.469}
\]

whereas a Fourier character introduced to separate \(M\) Farey/Beatty
sectors will be denoted

\[
 \xi\in\mathbb Z/M\mathbb Z.
\tag{9.470}
\]

In particular, \(\xi\) is not a replacement for \(h\delta\).  In the global
master (9.451), the row label still contains
\((h,\delta,\nu,\sigma)\), and the AFE weight, sign, and phase remain inside
\(\mathcal T_{u,t}\).  If one Möbius factor is decomposed, the enlarged row
may be recorded schematically as

\[
 u_{\rm Type}=(g,k,\ell,h,\delta,\nu,\sigma;d,m,s,b,\xi).
\tag{9.471}
\]

No sum over \(h\) or \(\delta\), and no absolute value over the corresponding
packets, is taken in the identities below.

Here is the exact integer skeleton of a common-sector \(TT^*\) pair.  Its
Farey/Type-entry determinant is different from the global row-slope
determinant \(\det(u,v)\) in (9.453).  Put

\[
 r_i=d_im_i,\qquad w_i=r_i-ks_i\geq0,\qquad
 b_i=\left\lfloor\frac{Qw_i}{s_i}\right\rfloor.
\tag{9.472}
\]

Euclidean division of the *original* numerator gives

\[
 Qr_i=B_is_i+\rho_i,\qquad
 B_i=\left\lfloor\frac{Qr_i}{s_i}\right\rfloor,\qquad
 0\leq\rho_i<s_i.
\tag{9.473}
\]

Because \(kQ\) is an integer,

\[
 b_i=B_i-kQ.
\tag{9.474}
\]

Consequently \(b_1=b_2\) if and only if \(B_1=B_2\).  For

\[
 \Delta_{\rm Type}=r_1s_2-r_2s_1=w_1s_2-w_2s_1
\tag{9.475}
\]

one has, before imposing a common sector,

\[
 Q\Delta_{\rm Type}
 =(B_1-B_2)s_1s_2+\rho_1s_2-\rho_2s_1.
\tag{9.476}
\]

Thus the common-sector pair satisfies the sharper exact identity

\[
 \boxed{Q\Delta_{\rm Type}=\rho_1s_2-\rho_2s_1,
 \qquad |Q\Delta_{\rm Type}|<s_1s_2.}
\tag{9.477}
\]

If the two \((r_i,s_i)\) are primitive, \(\Delta_{\rm Type}=0\) forces
\((r_1,s_1)=(r_2,s_2)\).  This still does **not** force
\((d_1,m_1)=(d_2,m_2)\): for example \(r_1=r_2=10\) contains the two
prime-power Type factorizations \((d,m)=(5,2)\) and \((2,5)\).  These are
genuine cross terms inside the same resonant orbit.

They must be recombined before Cauchy--Schwarz.  Coordinatewise in the
formal basis \(\{\log p\}\), the exact identity

\[
 -\mu(n)\log n=\sum_{dm=n}\mu(d)\Lambda(m)
\tag{9.478}
\]

is

\[
 \sum_{j=1}^{v_p(n)}\mu(n/p^j)=-\mu(n)v_p(n).
\tag{9.479}
\]

After retaining the other Möbius sign, its prime-coordinate vector is

\[
 \boxed{
 \sum_{j=1}^{v_p(n)}\mu(s)\mu(n/p^j)
 =-\mu(s)\mu(n)v_p(n).}
\tag{9.480}
\]

Therefore the full \(TT^*\) cross-factorization matrix is the outer
product of the *summed* vectors in (9.480), including all
\((j_1,j_2)\) cross terms.  Applying Cauchy separately to the Type blocks
would replace this exact outer product by a larger blockwise majorant and,
for nonsquarefree \(n\), would even destroy cancellations such as the two
\(p=2\) terms for \(n=12\).

The finite helper farey_type_ttstar_euclidean_ledger checks
(9.472)--(9.477), including the same-sector example
\((Q,k;r_1,s_1;r_2,s_2)=(11,1;10,7;13,9)\), for which
\(b_1=b_2=4\), \((\rho_1,\rho_2)=(5,8)\), and
\(\Delta_{\rm Type}=-1\).
The helper mobius_log_type_diagonal_recombination checks
(9.478)--(9.480) in every prime coordinate and expands the complete outer
product before comparing it with the recombined target.  These are finite
exact propositions suitable for later formalization.

More explicitly, let \(\lambda=(h,\delta,\nu,\sigma,\ldots)\) denote all
outer packet labels.  On the balanced support \(n>1\), absorb
\((\log n)^{-1}\) into the corresponding vector packet and denote the
result by \(\widetilde V_{\lambda,n,s}\).  On primitive entries, the complete
\(\Delta_{\rm Type}=0\) contribution after expanding one Möbius factor is
exactly

\[
\begin{aligned}
 \mathfrak G^{\rm Type}_{0}
 &=
 \sum_{(n,s)=1}
 \left\|
   \sum_{\lambda:\,\operatorname{entry}(\lambda)=(n,s)}
   c_\lambda\,
   \mu(s)\!\sum_{dm=n}\mu(d)\Lambda(m)\,
   \widetilde V_{\lambda,n,s}
 \right\|_2^2\\
 &=
 \sum_{(n,s)=1}
 \left\|
   \sum_{\lambda:\,\operatorname{entry}(\lambda)=(n,s)}
   c_\lambda[-\mu(s)\mu(n)\log n]\,
   \widetilde V_{\lambda,n,s}
 \right\|_2^2.
\end{aligned}
\tag{9.481}
\]

Thus the Type-internal diagonal has no separate factorization loss.  But
the \(\lambda_1\ne\lambda_2\) cross terms on one original entry remain
inside (9.481).  The finite helper
labelled_type_zero_determinant_recombination verifies (9.481) with signed
rational vector packets while recording every \(h\delta\).  Formula
(9.481) does not prove or remove the global same-slope gate (9.468);
it only restores that gate to the original-entry coefficient before it is
estimated.

There is nevertheless one genuine reduction of the remaining sector
square function.  If \(D_{\rm cont}:=\sum_e|\alpha_e|^2\|G_e\|_2^2\)
is its original-entry self diagonal, nonprincipal sector orthogonality
gives

\[
 \boxed{\mathcal N_{\ne0}=\left(1-\frac1M\right)D_{\rm cont}+\mathcal N_{\ne0}^{\rm off}.}
\tag{9.482}
\]

The character is trivial on \(e=f\).  By primitivity and (9.481), the
\(\Delta_{\rm Type}=0\) part of a one-factor Type expansion is exactly
the first term in (9.482), not a new factorization diagonal.  In the
continuous wave-packet normalization its exponent is already the target
diagonal exponent \(2\).  Hence the extra one-power obstruction in that
sector model lies entirely in
\(\mathcal N_{\ne0}^{\rm off}\), where
\(\Delta_{\rm Type}\ne0\).  This statement does not estimate the
offdiagonal term and does not identify it with the different global
nonzero-slope determinant in (9.454).

No Type-I/II estimate is proved by these identities.  They remove one
invalid route: determinant zero cannot be bounded factorization by
factorization.  The remaining analytic tasks are (i) the
\(\Delta_{\rm Type}\ne0\) sector-offdiagonal estimate, (ii) a global
same-slope estimate after recombining all Type factorizations and all
original \((h,\delta,\nu,\sigma)\) packets inside the square, and
(iii) the \(T^4\) global \(TT^*\) saving for the nonzero row-slope
determinant, with \(\xi\ne0\) used only as an auxiliary sector character.

### 9.74 The scalar metric-Beatty adapter fails, but the labelled Type Gram splits exactly

The metric theorem of Technau--Zafeiropoulos keeps one arithmetic function
\(f(r)\) fixed while the Beatty slope varies.  The present coefficient does
not have that form.  There is already an exact collision at
\(Q=6,k=1\):

\[
 (b,s,w,r)=(1,6,1,7),\qquad(2,5,2,7),
 \tag{9.483}
\]

but

\[
 \mu(6)\mu(7)=-1\ne1=\mu(5)\mu(7).
 \tag{9.484}
\]

Thus no scalar value \(f(7)\) represents both moving slopes.  This is
independent of the additional rational-grid sampling loss in
(4.652)--(4.654) of the alternative-routes note.  A new pair-valued or
vector-valued theorem could evade (9.484), but the published scalar
continuous-slope estimate cannot be inserted into (9.482).

The actual finite nonprincipal Gram can instead be written without this
adapter.  For a labelled packet \(P\), put

\[
 b(P)=\left\lfloor\frac{Q(n_P-ks_P)}{s_P}\right\rfloor,
 \qquad
 \kappa_M(b,b')=\mathbf1_{b=b'}-\frac1M.
 \tag{9.485}
\]

After expanding one Möbius factor by (9.478), let \(t=(d,m)\),
\(dm=n_P\), and retain

\[
 C_{P,t}=c_P\mu(s_P)\mu(d)\Lambda(m)\widetilde V_P,
 \tag{9.486}
\]

where \(c_P\) still contains every \((h,\delta,\nu,\sigma)\) label and
the original product \(a_{\rm AFE}=h\delta\).  Then character
orthogonality and a Type cutoff \(U\) give the exact pre-Cauchy split

\[
 \boxed{
 \mathcal N_{\ne0}^{\rm Type}
 =\sum_{X,Y\in\{\mathrm I,\mathrm{II}\}}
 \left(\mathcal N_{X,Y}^{\Delta=0}
       +\mathcal N_{X,Y}^{\Delta\ne0}\right),
 \quad
 \Delta=n_Ps_{P'}-n_{P'}s_P.}
 \tag{9.487}
\]

Here Type I means \(\min(d,m)\le U\); all I/I, I/II, II/I, and II/II
cross terms remain signed inside (9.487).  Summing all four zero-determinant
blocks before estimating recombines every internal factorization and gives
the original-entry diagonal (9.481).  Hence the exact remaining analytic
object is the *joint* sum of the four \(\Delta\ne0\) blocks, not four
separate absolute-value bounds.

Because the recombined original-entry diagonal already has exponent two,
a convenient sufficient local estimate for the supplied sector packet is

\[
 \boxed{
 \mathrm{JNT}_{2}^{\rm abs}:\qquad
 \left|\sum_{X,Y\in\{\mathrm I,\mathrm{II}\}}
 \mathcal N_{X,Y}^{\Delta\ne0}\right|
 \ll_{\varepsilon,W}T^{2+\varepsilon}.}
 \tag{9.488}
\]

Formula (9.488) is one joint signed gate; it does not ask for four
blockwise absolute-value estimates.  It becomes a replacement for the
corresponding sector portion of the coupled-kernel gate only after the
analytic packet-exhaustion map has been proved.

There is a further exact weakening.  After the internal Type
factorizations have recombined, put

\[
 X_b:=\sum_{P:\,b(P)=b}c_P A_P\widetilde V_P,
 \qquad
 A_P=-\mu(s_P)\mu(n_P)\log n_P.
\]

The complete nonprincipal character kernel is an orthogonal projector,
so its signed energy is the square sum

\[
 \boxed{
 \mathcal N_{\ne0}^{\rm Type}
 =\sum_{b=0}^{M-1}\|X_b\|_2^2
   -\frac1M\left\|\sum_{b=0}^{M-1}X_b\right\|_2^2
 =\frac1M\sum_{0\leq b<c<M}\|X_b-X_c\|_2^2\geq0.}
 \tag{9.489}
\]

Write

\[
 D:=\sum_{X,Y}\mathcal N_{X,Y}^{\Delta=0},
 \qquad
 J:=\sum_{X,Y}\mathcal N_{X,Y}^{\Delta\ne0}.
 \tag{9.490}
\]

Then (9.487) and (9.489) give
\(\mathcal N_{\ne0}^{\rm Type}=D+J\geq0\).  Consequently, once the
already diagonal-sized estimate \(D\leq C_0T^{2+\varepsilon}\) is
available, the genuinely weakest signed estimate needed for an upper
bound on this complete sector energy is

\[
 \boxed{
 \mathrm{JNT}_{2}^{+}:\qquad
 J\leq C_1T^{2+\varepsilon}.}
 \tag{9.491}
\]

Indeed,

\[
 \boxed{
 \left|\mathcal N_{\ne0}^{\rm Type}\right|
 =\mathcal N_{\ne0}^{\rm Type}
 =D+J\leq(C_0+C_1)T^{2+\varepsilon}.}
 \tag{9.492}
\]

Thus \({\rm JNT}_{2}^{+}\) is strictly weaker than
\({\rm JNT}_{2}^{\rm abs}\): it asks only for an upper bound on the
joint nonzero-determinant sum, not a lower bound.  The positivity used in
(9.492) belongs to the *complete* nonprincipal projector energy; it does
not assert \(J\geq0\), nor may it be applied after discarding any Type or
outer-packet cross term.

There is also no unused orthogonality hidden merely in the retained label
\(a_{\rm AFE}=h\delta\).  Before the Type split, exact character
orthogonality in the \(h\)-residue class gives

\[
 \boxed{
 \sum_{h\bmod s}e_s\!\left(h(v-\delta\bar w)\right)
 =s\,\mathbf1_{wv\equiv\delta\;({\rm mod}\ s)}
 =s\sum_{j\in\mathbb Z}\mathbf1_{wv-js=\delta}.}
 \tag{9.493}
\]

Equation (9.493) is the residue-class skeleton of the full \(h\)-Poisson
identity (4.450) in the alternative-routes note.  It shows exactly where
the product phase is spent: after dualization it is the determinant-line
incidence, not a remaining oscillator capable of supplying another
half-power.  The smooth transformed weight still retains \(\delta\) and
all outer labels, so this observation neither separates the packet nor
estimates \({\rm JNT}_{2}^{+}\).  The finite helper
h_product_phase_character_orthogonality verifies (9.493) and explicitly
records that no automatic power saving follows.

The scalar coefficient obstruction (9.484) can nevertheless be removed
at a different coordinate level.  On primitive support put \(n=rs\),
\(r=ks+w\), and \(A=kQ+b\).  Then

\[
 \mu(r)\mu(s)=\mu(n),
 \qquad
 As^2\leq Qn<(A+1)s^2.
 \tag{9.494}
\]

For fixed \((n,b)\), the possible integer denominators therefore lie in

\[
 \boxed{
 \sqrt{\frac{Qn}{A+1}}<s\leq\sqrt{\frac{Qn}{A}}.}
 \tag{9.495}
\]

This fiber has bounded multiplicity on the critical face by a purely
integer argument.  If \(s_1<s_2\) both satisfy (9.494), then

\[
 A(s_2-s_1)(s_1+s_2)<s_1^2.
\]

Hence, under the critical scale hypothesis \(s\leq CA\),

\[
 \boxed{s_2-s_1<\frac{s_1}{A}\leq C,\qquad
 \#\{s:(9.494)\}\leq C.}
 \tag{9.496}
\]

In particular \(s\leq A\) makes the integer fiber unique.  Thus the
complete sector vector can be reindexed exactly as

\[
 \boxed{
 X_b=\sum_n\mu(n)
 \sum_{\substack{s\mid n,\ (s,n/s)=1\\
                 As^2\leq Qn<(A+1)s^2}}
 B_{b,n,s},}
 \tag{9.497}
\]

with only \(O(1)\) inner terms at the critical scale.  Every original
\((h,\delta,\nu,\sigma)\) label remains inside \(B_{b,n,s}\).
This is a genuine fixed scalar Möbius coefficient \(\mu(n)\), so the
moving-slope collision (9.484) no longer applies to that coefficient.
It is not yet a one-Möbius theorem adapter: \(B_{b,n,s}\) still depends
on the divisor \(s\), both endpoint tapers, and the vector-valued tube.
Neither bounded multiplicity nor the fold \(\mu(r)\mu(s)=\mu(n)\) proves
square-root cancellation in the sparse product sequence.

The rational slope grid itself is no longer an additional power
obstruction.  The generic bandwidth estimate (4.652)--(4.654) in the
alternative-routes note ignores the actual Beatty Fourier coefficients.
For a fixed Hilbert-valued family they have the form

\[
 F(\lambda)=\sum_{m\leq X}g_m
 \sum_{1\leq |j|\leq J}c_j e(mj\lambda),
 \qquad |c_j|\ll |j|^{-1},\qquad J=X^{1/2}.
 \tag{9.498}
\]

For \(h\)-separated nodes and \(\sigma>1/2\), scaled Sobolev sampling
gives

\[
 \boxed{
 h\sum_\beta\|F(\lambda_\beta)\|_{\mathcal H}^2
 \ll_\sigma \|F\|_2^2
 +h^{2\sigma}\bigl\||D|^\sigma F\bigr\|_2^2.}
 \tag{9.499}
\]

If

\[
 a_k=\sum_{mj=k}g_mc_j,
 \tag{9.500}
\]

then divisor Cauchy and \(|c_j|\ll |j|^{-1}\) imply

\[
 \begin{aligned}
 \sum_k\|a_k\|_{\mathcal H}^2
 &\ll_\eta (XJ)^\eta\sum_m\|g_m\|_{\mathcal H}^2,\\
 \sum_k|k|^{2\sigma}\|a_k\|_{\mathcal H}^2
 &\ll_\eta (XJ)^\eta
 \sum_m m^{2\sigma}\|g_m\|_{\mathcal H}^2
 \sum_{j\leq J}j^{2\sigma-2}.
 \end{aligned}
 \tag{9.501}
\]

At \(X=Q=T\), \(h\asymp Q^{-1}\), choose
\(\sigma=1/2+\eta\).  Since

\[
 h^{2\sigma}X^{2\sigma}\asymp1,\qquad
 \sum_{j\leq T^{1/2}}j^{2\sigma-2}\ll_\eta T^\eta,
 \tag{9.502}
\]

the nonuniform reciprocal grid satisfies the proved estimate

\[
 \boxed{
 \sum_{\beta\leq Q}\|F(\lambda_\beta)\|_{\mathcal H}^2
 \ll_\varepsilon T^{1+\varepsilon}
 \sum_{m\leq T}\|g_m\|_{\mathcal H}^2.}
 \tag{9.503}
\]

Therefore a fixed coefficient family with diagonal energy \(T^{1+o(1)}\)
has sampled energy \(T^{2+\varepsilon}\); the former generic
\(T^{1/2}\) alias loss is not present.  This closes the *sampling* row of
the metric-Beatty coverage audit.  It does not close the packet row:
the actual coefficient at a Beatty value changes with its denominator
preimage, while the product-coordinate repair (9.497) has ambient
coefficient energy \(T^{2+o(1)}\) and factorization-dependent vectors.
Constructing a length-\(T\), slope-independent Hilbert family from the
global Type I/II packet remains unproved.

The helpers farey_scalar_beatty_fixed_coefficient_collision and
labelled_type_nonprincipal_determinant_split verify (9.483)--(9.487) with
exact integer/rational data.  The latter fixture retains three distinct
AFE packets, product frequencies \(6,-5,-8\), all Type-pair blocks, and
nonzero determinants \(\pm5\).  It also verifies (9.489): both sides are
\(6327/5\).  The helper joint_nonprincipal_one_sided_upper_bound verifies
the finite implication (9.490)--(9.492).  With
\(D=16587/5\), \(J=-2052\), and \(C_1T^{2+\varepsilon}=0\) in the
fixture, the one-sided hypothesis holds while \(|J|\leq0\) fails, giving
an exact strictness witness.  Neither helper proves the uniform analytic
\({\rm JNT}_{2}^{+}\) estimate or the exhaustive analytic packet map.
The helper farey_product_sector_fiber_ledger verifies
(9.494)--(9.497), including the cardinality bound and the fixed
\(\mu(n)\) coefficient, while keeping
vector_weight_still_factorization_dependent true and
cancellation_estimate_proved false.
The adapter structured_beatty_sobolev_sampling_audit verifies the exponent
ledger in (9.498)--(9.503), including arbitrary separated nodes and
Hilbert-valued fixed coefficients.  It keeps
actual_packet_fixed_across_slopes and
moving_two_mobius_vector_adapter_constructed false.
The finite helper beatty_divisor_fourier_coefficient_sides constructs
(9.500) over exact rational vectors and verifies the Hilbert
divisor-Cauchy majorant in (9.501) frequency by frequency.

### 9.75 The centered moving-Beatty projector is the positive one-sided gate

There is a more direct positive sufficient condition than estimating the
signed nonzero-determinant sum.  Let \(\lambda\) index every retained
\((h,\delta,\nu,\sigma)\) and Type-factorization label and define

\[
 \boxed{
 X_b=\sum_{\substack{s\le Q,\ 0\le w<s,
                     \\ (ks+w,s)=1\\
                     \lfloor Qw/s\rfloor=b}}
 \mu(s)\mu(ks+w)\sum_\lambda G_{s,w,\lambda}.}
 \tag{9.504}
\]

This is the complete pre-Cauchy vector, not a scalar surrogate.  The
finite sector-character projector is

\[
 \boxed{
 \mathcal E_{\ne0}
 =\sum_b\|X_b\|_{\mathcal H}^2
  -\frac1Q\left\|\sum_bX_b\right\|_{\mathcal H}^2.}
 \tag{9.505}
\]

After all internal \(dm=r\) factorizations have been recombined, write

\[
 \mathcal E_{\ne0}=D_{\Delta=0}+J_{\Delta\ne0},
 \qquad D_{\Delta=0}\ge0.
 \tag{9.506}
\]

Then positivity alone gives the exact one-sided implication

\[
 \boxed{
 J_{\Delta\ne0}\le\mathcal E_{\ne0}
 \le\sum_b\|X_b\|_{\mathcal H}^2.}
 \tag{9.507}
\]

It is therefore enough to prove the centered positive estimate

\[
 \boxed{
 {\rm BC}^{\rm mov,cent}_{\mathcal H}(2):\qquad
 \sum_{b<Q}\|X_b\|_{\mathcal H}^2
 -\frac1Q\left\|\sum_{b<Q}X_b\right\|_{\mathcal H}^2
 \ll_{\varepsilon,W}T^{2+\varepsilon}.}
 \tag{9.508}
\]

The uncentered sector-square bound obtained by deleting the principal
subtraction is a stronger sufficient condition; it is not called the
weakest gate here.

In a scalar projection the sector entry is

\[
 ks+\left\lceil\frac{bs}{Q}\right\rceil
 =\left\lfloor
   \left(k+\frac bQ\right)s+\frac{Q-1}{Q}
  \right\rfloor,
 \tag{9.509}
\]

so (9.508) contains a centered power-strength moving-rational-grid Beatty--Chowla
estimate.  Coherent energy has exponent three and the target exponent is
two: one needs a full power in energy, or \(T^{1/2}\) before squaring.

Crnčević--Hernández--Rizk--Sereesuchart--Tao,
[arXiv:2211.15830v4](https://arxiv.org/abs/2211.15830), Theorem B, prove a
qualitative logarithmic limit only for a fixed positive irrational
slope.  Teräväinen--Walker,
[arXiv:2303.12574v1](https://arxiv.org/abs/2303.12574), Theorem 1.2,
subsumes that result, permits two fixed inhomogeneous Beatty slopes, and
classifies the fixed rational-ratio Liouville resonance.  Neither result
gives a power rate uniform over the moving \(Q\)-grid or a Hilbert-valued
packet square function.  The rational resonance is precisely why
\(D_{\Delta=0}\) must be extracted before invoking cancellation; it is
not a bound for \(J_{\Delta\ne0}\).

The helper farey_beatty_chowla_projector_sides verifies (9.504)--(9.507)
over exact rational vectors, including all supplied packet labels and
both Möbius coefficients.  The helper beatty_chowla_power_gate_audit
records the half-power deficit and the fixed- versus moving-slope
mismatch.  It keeps analytic_square_function_bound_proved and
covers_one_sided_joint_type_gate false.  Thus (9.508) is a strictly
clearer positive gate, but remains unproved.

### 9.76 Exact sector Fourier completion and the closed primitive boundary

For \(0<\xi<Q\), let

\[
 F_{\xi,Q}(x)=e\!\left(\frac{\xi\lfloor Qx\rfloor}{Q}\right),
 \qquad 0\le x<1,
 \tag{9.510}
\]

with the right-continuous convention inherited from the sector
definition.  Direct integration over the \(Q\) step intervals gives
zero mean and, for \(a=\xi+jQ\),

\[
 \widehat F_{\xi,Q}(a)
 =\frac{Q(1-e(-\xi/Q))}{2\pi ia};
 \tag{9.511}
\]

all other Fourier coefficients vanish.  Restoring the half-jump omitted
by pointwise Fourier convergence yields the exact identity

\[
 \boxed{
 F_{\xi,Q}(x)
 =\sum_{j\in\mathbb Z}
 \frac{Q(1-e(-\xi/Q))}{2\pi i(\xi+jQ)}
 e((\xi+jQ)x)
 +\frac{1-e(-\xi/Q)}2e(\xi x)
  \mathbf1_{Qx\in\mathbb Z}.}
 \tag{9.512}
\]

For a Type entry \(dp=ks+w\), every continuous harmonic
\(a=\xi+jQ\) satisfies

\[
 \boxed{e(aw/s)=e(adp/s),}
 \tag{9.513}
\]

because \(ak\) is integral.  Thus the completed phase is a direct linear
fraction.  No \(h,\delta\) label or Möbius coefficient is used up in
this identity.

The jump correction is an exactly diagonal-sized family.  Indeed,
\((ks+w,s)=(w,s)=1\), so \(s\mid Qw\) forces \(s\mid Q\).  More precisely,

\[
 \boxed{
 b\mapsto
 \left(\frac Q{(b,Q)},\frac b{(b,Q)}\right)
 }
 \tag{9.514}
\]

is a bijection from \(0\le b<Q\) to the primitive pairs
\(1\le s\le Q,0\le w<s,s\mid Qw\).  Hence there are exactly
\(\sum_{s\mid Q}\varphi(s)=Q\) boundary entries and one in each sector.
After recombining all labels on an original entry, their vectors \(Y_b\)
satisfy

\[
 0\le
 \sum_b\|Y_b\|^2-Q^{-1}\left\|\sum_bY_b\right\|^2
 \le\sum_b\|Y_b\|^2=D_{\partial}\le D_{\rm cont}.
 \tag{9.515}
\]

The half-jump scalar in (9.512) has modulus at most one, and
\(D_{\rm cont}\ll T^{2+\varepsilon}\) was already established.  Therefore
every Fourier endpoint is within target; the remaining analytic problem
may be restricted to \(s\nmid Qw\).

This completion does not make a standard Type-I estimate sufficient.
If \(s\asymp T^\sigma,Q\asymp T^q,d\asymp T^\delta\), then
\(p\asymp T^{\sigma-\delta}\).  Even under an optimistic separation of
the prime coefficient, Cauchy in \(s\) and the additive Farey large sieve
give the fixed-\(d\) exponent

\[
 (\sigma-q)+\max(\sigma-\delta,2\sigma)
 +(\sigma-\delta).
 \tag{9.516}
\]

At \(\sigma=q=1\) this is \(3-\delta\).  Perfect orthogonality over the
\(T^\delta\) divisors still gives exponent three, while the target is two;
ordinary divisor Cauchy gives \(3+\delta\).  Thus termwise harmonic
completion plus the standard additive large sieve retains the full
one-power energy deficit.  A successful estimate must use joint
Möbius/divisor or determinant dispersion before these Cauchy steps.

The finite helpers primitive_beatty_fourier_boundary_sides and
beatty_sector_fourier_type_phase_ledger verify (9.513)--(9.515), including
the exact sector bijection and recombination of multiple packet labels.
The exponent helper beatty_type_i_additive_large_sieve_audit verifies
(9.516).  It deliberately keeps the continuous Type-I/II coverage flag
false; only the Fourier-boundary row has now been closed.

### 9.77 The continuous harmonic restores the full Kloosterman phase

The direct phase in (9.513) must not be estimated after discarding the
phase already present in the AFE packet.  Put

\[
 \alpha=\xi+jQ,\qquad A=h\delta,\qquad r=dp=ks+w.
\]

Since \((r,s)=1\), both \(d\) and \(p\) are units modulo \(s\).  The
product of the sector harmonic and the original Poisson phase is exactly

\[
 \boxed{
 e_s(\alpha w-A\bar r)
 =e_s(\alpha dp-A\bar d\bar p).}
 \tag{9.517}
\]

Thus, after fixing the Type divisor \(d\), the prime-bearing factor is
not a merely additive sum.  Its actual scalar core is

\[
 \boxed{
 \sum_p\Lambda(p)V(p/P)
 e_s(Bp+C\bar p),\qquad
 B=\alpha d,\quad C=-A\bar d.}
 \tag{9.518}
\]

Both Möbius factors \(\mu(s)\mu(d)\), the factorization
\(A=h\delta\), and every outer packet label remain outside this displayed
prime sum.  Moreover multiplication by the unit \(d\) gives the exact
conductor condition

\[
 \boxed{(BC,s)=1\quad\Longleftrightarrow\quad(\alpha A,s)=1.}
 \tag{9.519}
\]

Nonunit strata therefore require their genuine reduced modulus; they
cannot be inserted into a unit-coefficient theorem by deleting a gcd.

This exact phase permits a sharper published-coverage audit.  Write

\[
 s=T^\sigma,\qquad d=T^u,\qquad P=T^\pi,
 \qquad \pi=\sigma-u.
 \tag{9.520}
\]

Korolev's composite-modulus prime-Kloosterman theorem
(arXiv:1911.09981, Theorem 1) applies on the unit stratum when
\(3\sigma/4<\pi\leq3\sigma/2\).  Ignoring the theorem's fixed positive
endpoint epsilon, its relative saving exponent is

\[
 \eta_{\rm Kor}(\sigma,u)
 =\min\left(\frac{\sigma/4-u}{7},
             \frac{\sigma-3u}{35}\right)
 =\begin{cases}
 (\sigma-3u)/35,&0\leq u\leq\sigma/8,\\
 (\sigma/4-u)/7,&\sigma/8\leq u\leq\sigma/4.
 \end{cases}
 \tag{9.521}
\]

In particular its most favorable full-length saving is only
\(\eta_{\rm Kor}(\sigma,0)=\sigma/35\).

For prime \(s\), the phase \(e_s(Bx+C\bar x)\), with \(C\ne0\), is a
bounded-conductor nonexceptional trace weight.  The smoothed form of
Fouvry--Kowalski--Michel Theorem 1.5 gives, for every \(\eta<1/24\),

\[
 \sum_{p\ \mathrm{prime}}e_s(Bp+C\bar p)V(p/P)
 \ll P(1+s/P)^{1/6}s^{-\eta}.
 \tag{9.522}
\]

Consequently its *limiting*, not attained, saving exponent on the left
Type-I wing is

\[
 \boxed{
 \eta_{\rm FKM}(\sigma,u)
 =\frac{\sigma}{24}-\frac u6,qquad 0\leq u<\sigma/4.}
 \tag{9.523}
\]

The Möbius version of the same theorem gives the symmetric prime-modulus
right wing \(3\sigma/4<u\leq\sigma\), after fixing the prime-bearing
factor.  Prime powers of exponent at least two in \(\Lambda\) must be
removed separately; their support has square-root cardinality and is not
part of the prime theorem.

The central prime-modulus band is not wholly absent from the literature.
Fouvry--Kowalski--Michel Theorem 1.17 accepts arbitrary dyadic
coefficients in
\(\sum_{d,p}\alpha_d\beta_pK(dp)\).  Orient its two variables so that
\(v=\min(u,\sigma-u)\) is the shorter exponent.  Its three relative
terms give the exact saving

\[
 \boxed{
 \eta_{\rm FKM}^{\rm II}(\sigma,v)
 =\min\left(\frac\sigma4,\frac v2,
             \frac\sigma4-\frac v2\right).}
 \tag{9.523a}
\]

This is positive for \(0<v<\sigma/2\), reaches its maximum
\(\sigma/8\) at \(v=\sigma/4\), and degenerates exactly to zero at the
balanced point \(u=\sigma/2\).  Near \(v=0\), the one-variable bounds
in (9.523) are stronger; the two prime-modulus envelopes cross at
\(v=\sigma/16\), with saving \(\sigma/32\).

The exact one-factor coverage table is therefore:

| modulus and Type range | published input | best pointwise saving | status for the coupled gate |
|---|---|---:|---|
| composite squarefree \(s\), \(0\leq u<\sigma/4\), \((\alpha A,s)=1\) | Korolev prime-Kloosterman | at most \(T^{\sigma/35}\) | quantitatively insufficient; no joint \(s,\alpha,A\) moment |
| prime \(s\), \(0\leq u<\sigma/4\) | FKM prime trace theorem | supremum \(T^{\sigma/24}\) | quantitatively insufficient and covers no composite-modulus aggregate |
| prime \(s\), \(3\sigma/4<u\leq\sigma\) | FKM Möbius trace theorem | supremum \(T^{\sigma/24}\) | same mismatch after fixing the short prime factor |
| prime \(s\), \(0<u<\sigma\) | FKM bilinear trace Theorem 1.17 | at most \(T^{\sigma/8}\), zero at \(u=\sigma/2\) | fixed-prime sub-slices only; still below the half-power |
| prime \(s\), \(u=\sigma/2\) | formal substitution in FKMS 2026 gallant formula | \(T^{\sigma/224}\) only under a gallant-strength rank-one moment bound | direct equal-shift pole collisions violate that moment count; not a valid coverage row |
| composite \(s\), \(3\sigma/4<u\leq\sigma\) | Korolev multiplicative-coefficient theorem | logarithmic in the uniform composite case | no power coverage |
| composite \(s\), \(\sigma/4\leq u\leq3\sigma/4\) | genuinely bilinear trace Type II | no applicable composite-modulus theorem | **unproved central band** |

At the critical face \(\sigma=1\), the coupled projector needs a
half-power before squaring.  Even the best prime-modulus pointwise row
leaves

\[
 \frac12-\frac1{24}=\frac{11}{24},
 \tag{9.524}
\]

while the uniform composite row leaves
\(1/2-1/35=33/70\).  Applying these estimates independently on the two
sides of the energy doubles both the obtained and required exponents and
does not change the deficit.  More importantly, termwise application
would sum over \(s,\alpha,h,\delta\) absolutely and discard the exact
coupling which the target is required to exploit.

Even the best registered fixed-prime bilinear point \(v=\sigma/4\)
leaves \(1/2-1/8=3/8\), and the older proved estimate at exact balance
leaves the full \(1/2\).  Section 9.78 records why the apparent
rank-one \(1/224\) substitution is obstructed by a larger Type-II
exceptional family and therefore is not a currently valid route.

Hence (9.517) changes the correct analytic interface but does not prove
the gate.  After removing the boundary already controlled in (9.515),
the corresponding positive continuous gate can now be stated more
narrowly.  With \(c_{\xi,j}\) as in (9.511), it is

\[
 \boxed{
 \frac1Q\sum_{\xi=1}^{Q-1}
 \left\|
 \sum_s\mu(s)\sum_{h,\delta}\sum_{dp\asymp s}
 \mu(d)\Lambda(p)\sum_{j\in\mathbb Z}c_{\xi,j}
 \mathcal W_{s,\xi,j,h,\delta,d,p}
 e_s((\xi+jQ)dp-h\delta\bar d\bar p)
 \right\|_{\mathcal H}^{2}
 \ll T^{2+\varepsilon}.}
 \tag{9.525}
\]

Here \(\mathcal W\) includes the original smooth dyadic and reflected
packet labels, the relation \(dp=ks+w\), and the nonboundary condition
\(s\nmid Qw\).  Expanding the norm produces all four signed Type cross
blocks; none has been removed before the final square.  Formula (9.525)
is the exact Fourier form of the continuous part of the supplied
centered sector gate, not a scalar surrogate and not yet an exhaustive
adapter from every packet in (4.5).  The composite-modulus middle band
and the exact balanced prime slice form its irreducible Type-II part.
The outer wings are not independently disposable because their
published savings do not pay the global half-power.

The finite helper beatty_afe_type_kloosterman_phase_ledger verifies
(9.517)--(9.519), including the equivalence of the unit conditions.  The
helpers korolev_prime_kloosterman_type_i_audit and
fkm_prime_modulus_kloosterman_type_i_audit verify (9.521)--(9.524), and
fkm_prime_modulus_bilinear_type_ii_audit verifies (9.523a), over exact
rational exponents.  All keep the coupled-gate coverage flags false.

### 9.78 Product-trace completion and the rank-one theorem boundary

It is tempting to Fourier-complete the product trace in (9.517) and
then insert one of the recent bilinear theorems for *classical*
Kloosterman sums.  The exact finite completion shows both what this
gains and why it is not yet an adapter.  For a prime \(q\), put

\[
 K(x)=\begin{cases}
 e_q(Bx+C\bar x),&(x,q)=1,\\
 0,&q\mid x,
 \end{cases}
 \qquad
 \widehat K(h)=\sum_{x\bmod q}K(x)e_q(-hx).
\]

Then, with the unnormalised classical convention for \(S(a,b;q)\),

\[
 \boxed{\widehat K(h)=S(B-h,C;q)},
 \qquad
 K(x)=\frac1q\sum_{h\bmod q}S(B-h,C;q)e_q(hx).
 \tag{9.526}
\]

Consequently every fixed-modulus Type-II form has the exact identity

\[
 \boxed{
 \mathcal B=\sum_{d,p}\alpha_d\beta_pK(dp)
 =\frac1q\sum_{h\bmod q}S(B-h,C;q)A(h),
 \quad
 A(h)=\sum_{d,p}\alpha_d\beta_p e_q(hdp).}
 \tag{9.527}
\]

This is not a bilinear form with two short Kloosterman arguments.  The
second argument \(C\) is fixed, \(B-h\) traverses all \(q\) residues,
and its coefficient is the complete additive transform \(A(h)\) of the
original product sequence.  In particular the exact Parseval identities
are

\[
 \sum_{h\bmod q}|S(B-h,C;q)|^2=q(q-1),
 \tag{9.528}
\]

and

\[
 \sum_{h\bmod q}|A(h)|^2
 =q\!\sum_{d_1p_1\equiv d_2p_2\ (q)}
 \alpha_{d_1}\beta_{p_1}
 \overline{\alpha_{d_2}\beta_{p_2}}.
 \tag{9.529}
\]

Even at the diagonal lower bound for the multiplicative incidence
energy, Cauchy--Parseval gives no power saving over the original
balanced form.  Termwise Weil is worse by a half-power.  The theorems
of [Pascadi](https://arxiv.org/abs/2511.08445),
[Blomer--Pascadi](https://arxiv.org/abs/2607.24311), and
[Milićević--Qin--Wu](https://arxiv.org/abs/2511.07550) instead estimate
bilinear forms in classical Kloosterman sums with two independently
short argument families.  Formula (9.527) has one fixed argument and
one complete argument carrying a product-additive transform, so those
theorems cannot be inserted without a new operator estimate for
\(A(h)\).  Taking absolute values in \(h\) discards exactly the
two-Möbius coupling sought by (9.525).

There is an apparent newer improvement on the *prime* balanced slice,
but a direct exceptional-locus audit shows that it is not presently a
valid route.  The quantitative Type-II estimate in
Fouvry--Kowalski--Michel--Sawin Theorem 1.3(2) is stated for gallant
sheaves.  Their definition forces rank at least two, whereas
\(x\mapsto e_q(Bx+C/x)\) is a rank-one Artin--Schreier trace.  Therefore
Theorem 1.3(2) does not directly apply.  Section 9.11 discusses
rank-one functions \(\chi(f(x))\psi(g(x))\) and explains why an inverse
pole such as \(g=1/X\) controls the first one-variable moment family.  It
does not state a quantitative rank-one Type-II theorem or verify the
second exceptional family required by Proposition 5.3(2).

That distinction is substantive.  In the second moment family, let
\(m\) denote the moment order, put
\(\epsilon_j=1\) for \(1\leq j\leq m\) and
\(\epsilon_j=-1\) for \(m<j\leq2m\), and write the two dilation arrays
as \(a_j,b_j\).  The Type-II restriction is \(a_j\ne b_j\) for every
\(j\).  On the locus where all translations equal one common value
\(r_j=r\), the complete one-variable phase is

\[
 F(v)=B(v+r)L+\frac{C}{v+r}R,
 \quad
 L=\sum_{j=1}^{2m}\epsilon_j(a_j-b_j),
 \quad
 R=\sum_{j=1}^{2m}\epsilon_j(a_j^{-1}-b_j^{-1}).
 \tag{9.530}
\]

Hence the open subvariety

\[
 \mathcal E_m:\quad L=R=0,\qquad a_jb_j(a_j-b_j)\ne0
 \tag{9.531}
\]

has constant phase at every \(v\ne-r\), and the one-variable sum has
size \(q-1\).  It has \(4m\) dilation variables and the common shift
\(r\), cut out by only two equations.  At every rank-two Jacobian point,

\[
 \boxed{\dim\mathcal E_m\geq4m-1>3m\qquad(m\geq2).}
 \tag{9.532}
\]

The gallant proof of Proposition 5.3(2) needs only
\(O(q^{3m})\) exceptional parameter tuples, corresponding to dimension
at most \(3m\).  The excess in (9.532) is \(m-1\).  This is not merely a
dimension heuristic: for \(q=11,m=2\),

\[
 (a_1,a_2,a_3,a_4)=(1,1,1,1),\qquad
 (b_1,b_2,b_3,b_4)=(2,9,3,8)
 \tag{9.533}
\]

satisfies every pointwise exclusion, has \(L=R=0\), and the two
defining equations have Jacobian rank two.  Thus its local family has
dimension seven, while the gallant count permits only six.  The direct
rank-one Type-II pole stratification fails; a different argument would
have to exploit or subtract this whole collision family.

For calibration only, blindly substituting the gallant formula at
\(M=N=q^{1/2}\) gives

\[
 \left(q^{-1/2}
 +q^{(-1/4+7/(4\ell))/\ell}\right)^{1/2}.
 \tag{9.534}
\]

For integers \(\ell>7\), its second term saves
\((\ell-7)/(8\ell^2)\); this is maximized at \(\ell=14\), giving

\[
 \boxed{\eta_{\rm FKMS,route}(1,14)=\frac1{224}},
 \qquad
 \frac12-\frac1{224}=\frac{111}{224}.
 \tag{9.535}
\]

Because (9.532) invalidates the moment input used to derive this formula,
\(1/224\) is a formal substitution, not a currently valid route
exponent.  Even if a new treatment recovered it, it would remain far
below the required half-power, pointwise in one prime modulus, and
would supply none of the joint \(s,\xi,h\delta\) moment.  It is therefore
not entered in the proved-coverage column.  The prime balanced slice and
the composite central band remain unproved in every case.

The finite helper product_trace_additive_completion_audit verifies
(9.526)--(9.529), including both Parseval identities and an arbitrary
finite bilinear coefficient packet.  The helper
fkms_rank_one_type_ii_collision_witness verifies (9.530)--(9.533),
including the rank-two finite Jacobian witness.  The helper
fkms_rank_one_prime_type_ii_route_audit verifies the formal calibration
(9.534)--(9.535), computes the collision excess
\(\lceil\ell/3\rceil-1\), and keeps both the direct route and the
proved-coverage flags false.

### 9.79 Squarefree CRT transfer and its sharp cofactor cost

The outer coefficient \(\mu(s)\) restricts the active moduli to
squarefree \(s\), so a prime-factor transfer should be audited before
declaring the composite middle band irreducible.  Let \(s=qr\) with
\((q,r)=1\), write \(\bar r_q\) for the inverse of \(r\bmod q\) and
\(\bar q_r\) for the inverse of \(q\bmod r\), and put

\[
 K_s(x)=e_s(Bx+C\bar x),
 \quad
 K_q^{(r)}(x)=e_q\!\left(\bar r_q(Bx+C\bar x)\right),
 \quad
 K_r^{(q)}(x)=e_r\!\left(\bar q_r(Bx+C\bar x)\right).
\]

CRT gives the exact product, with no completion or loss,

\[
 \boxed{K_{qr}(x)=K_q^{(r)}(x)K_r^{(q)}(x).}
 \tag{9.536}
\]

For the unit group modulo \(r\), define

\[
 \widehat K_r(\chi)
 =\sum_{u\in(\mathbb Z/r\mathbb Z)^\times}
 K_r^{(q)}(u)\overline{\chi(u)}.
\]

Multiplicative Fourier inversion then separates the cofactor in every
product Type-II form:

\[
 \boxed{
 \begin{aligned}
 \sum_{d,p}\alpha_d\beta_pK_{qr}(dp)
  =\frac1{\varphi(r)}\sum_{\chi\bmod r}\widehat K_r(\chi)
  \sum_{d,p}&\alpha_d\chi(d)\,\beta_p\chi(p)\\
  &\times K_q^{(r)}(dp).
 \end{aligned}}
 \tag{9.537}
\]

In the application, \(B=\alpha\) and \(C=-h\delta\).  Thus (9.537)
retains \(h\delta\), the outer sign \(\mu(qr)\), and the Type sign
\(\mu(d)\); it only twists the two coefficient arrays by the same
multiplicative character.

The exact Parseval cost is

\[
 \sum_{\chi\bmod r}|\widehat K_r(\chi)|^2
 =\varphi(r)\sum_{u\in(\mathbb Z/r\mathbb Z)^\times}|K_r^{(q)}(u)|^2
 =\varphi(r)^2.
 \tag{9.538}
\]

Consequently triangle plus Cauchy in the character variable has the
sharp coefficient-independent ceiling

\[
 \boxed{
 \frac1{\varphi(r)}\sum_{\chi\bmod r}|\widehat K_r(\chi)|
 \leq\varphi(r)^{1/2}.}
 \tag{9.539}
\]

There is an exact alternative to paying this \(L^1\) ceiling.  Put
\(w_\chi=\widehat K_r(\chi)/\varphi(r)\), and denote the inner
prime-modulus form in (9.537) by \(\mathcal B_\chi\).  Parseval gives

\[
 \boxed{\sum_{\chi\bmod r}|w_\chi|^2=1,\qquad
 |\mathcal B_{qr}|^2\leq
 \sum_{\chi\bmod r}|\mathcal B_\chi|^2.}
 \tag{9.539a}
\]

Character orthogonality converts the square function into one explicit
product-incidence energy.  If

\[
 z_{d,p}=\alpha_d\beta_pK_q^{(r)}(dp),
\]

then

\[
 \boxed{
 \sum_{\chi\bmod r}|\mathcal B_\chi|^2
 =\varphi(r)
 \sum_{\substack{d_1p_1\equiv d_2p_2\pmod r\\
                 (d_1p_1d_2p_2,r)=1}}
 z_{d_1,p_1}\overline{z_{d_2,p_2}}.}
 \tag{9.539b}
\]

Thus the factor \(\varphi(r)^{1/2}\) is unavoidable only for a
coefficient-independent pointwise treatment.  Keeping the character
family inside the square replaces it by (9.539b), whose diagonal,
uniform-residue principal part, and centered off-diagonal must be
estimated jointly with the two Möbius weights and \(h\delta\).  No such
global incidence estimate is supplied by Parseval itself.

More explicitly, put

\[
 C_u=\sum_{\substack{d,p\\dp\equiv u\pmod r}}z_{d,p},
 \qquad
 \overline C=\frac1{\varphi(r)}
 \sum_{u\in U(r)}C_u.
\]

Then the incidence energy has the exact principal/centered split

\[
 \boxed{
 \varphi(r)\sum_{u\in U(r)}|C_u|^2
 =\left|\sum_{u\in U(r)}C_u\right|^2
  +\varphi(r)\sum_{u\in U(r)}|C_u-\overline C|^2.}
 \tag{9.539c}
\]

The first term is the uniform cofactor-character mode and must be put
on the same principal ledger as (9.555).  Only the second term is a
genuinely centered product-residue operator.

Suppose optimistically that a fixed-prime Type-II theorem accepts every
twisted coefficient array in (9.537) and saves \(q^{-\kappa}\).  Equations
(9.537)--(9.539) transfer only the factor

\[
 r^{1/2}q^{-\kappa}.
 \tag{9.540}
\]

Writing \(q=T^\lambda,r=T^{\sigma-\lambda}\), the transferred saving is

\[
 \eta_{\rm CRT}(\sigma,\lambda;\kappa)
 =\max\!\left(0,\kappa\lambda-\frac{\sigma-\lambda}{2}\right),
 \qquad
 \lambda>\frac{\sigma}{1+2\kappa}
 \tag{9.541}
\]

for a strict power gain.  The strongest registered FKM fixed-prime
bilinear exponent is only \(\kappa=1/8\).  Even ignoring all of its
length restrictions, CRT transfer therefore requires

\[
 \lambda>\frac45\sigma.
\]

At the illustrative point \(\sigma=1,\lambda=9/10\),

\[
 \boxed{\eta_{\rm CRT}(9/10)=\frac{9}{80}-\frac1{20}
 =\frac1{16}},
 \qquad
 \frac12-\eta_{\rm CRT}=\frac7{16}.
 \tag{9.542}
\]

As \(\lambda\to\sigma\), the gain never exceeds \(1/8\).  Hence this
exact CRT transfer can certify a small pointwise saving only on an
extreme large-prime-factor subface, and does not close any part of the
half-power coupled gate.  It also supplies no outer \(s\)-average, no
sector-character moment, and no joint \(h\delta\) moment.  Avoiding the
\(r^{1/2}\) cost in (9.539) requires keeping the character family inside
the global square before Cauchy; that is a new coupled operator estimate,
not a consequence of the fixed-prime theorem.

This is already the optimum over the whole squarefree factorization
polytope.  If \(s=\prod_iq_i\) and \(q_i=T^{\lambda_i}\), then choosing
the best one prime factor gives

\[
 \boxed{
 \max_i\left(\kappa\lambda_i-\frac{\sigma-\lambda_i}{2}\right)_+
 \leq\sup_{0\leq\lambda\leq\sigma}
 \left(\kappa\lambda-\frac{\sigma-\lambda}{2}\right)_+
 =\kappa\sigma.}
 \tag{9.542a}
\]

For every nontrivial finite factorization the last boundary value is
strictly unattained.  Thus \(\kappa=1/8\) cannot reach a half-power even
in the limiting one-large-prime corner, and balanced factorizations
give no power saving at all.

The finite helper squarefree_product_trace_crt_character_audit verifies
(9.536)--(9.539), including the CRT phases, character reconstruction,
bilinear identity, and Parseval norm for an arbitrary squarefree
cofactor \(r\), not only for one prime cofactor.  It constructs the full
product character group

\[
 \widehat{U(r)}=\prod_{p\mid r}\widehat{\mathbb F_p^\times}.
\]

The same helper also checks (9.539a)--(9.539c) on arbitrary finite
bilinear coefficient packets and keeps the global product-incidence
bound explicitly false.

The exact-rational helper
squarefree_prime_factor_transfer_audit verifies (9.540)--(9.542) and
the helper squarefree_prime_factor_polytope_audit verifies (9.542a);
both keep every global coupled-moment flag false.

### 9.80 Exact rank-one resonance subtraction

The equal-shift family in (9.530)--(9.533) is not an isolated accident.
For the present product trace, every constant-phase parameter tuple can
be classified explicitly.  This gives a more useful next interface than
trying to force the kernel into the gallant theorem.

Let \(q\) be prime, let \(B,C\in\mathbb F_q^\times\), and keep the signs
\(\epsilon_j=1\) for \(j\leq m\) and \(\epsilon_j=-1\) for \(j>m\).
For \(2m\) shifts \(r_j\) and two dilation arrays \(a_j,b_j\in
\mathbb F_q^\times\), with \(a_j\ne b_j\), put

\[
 A_j=\epsilon_j(a_j-b_j),\qquad
 R_j=\epsilon_j(a_j^{-1}-b_j^{-1}),
 \tag{9.543}
\]

and, for every distinct shift \(\rho\), put

\[
 L=\sum_{j=1}^{2m}A_j,
 \qquad R(\rho)=\sum_{j:r_j=\rho}R_j.
 \tag{9.544}
\]

The complete one-variable phase occurring after the Type-II moment
exchange has the exact partial-fraction expansion

\[
 \boxed{
 F(v)=BLv+B\sum_jA_jr_j
       +C\sum_{\rho}\frac{R(\rho)}{v+\rho}.}
 \tag{9.545}
\]

It follows immediately, as an identity of rational functions, that

\[
 \boxed{F\text{ is constant}\quad\Longleftrightarrow\quad
 L=0\ \text{ and }\ R(\rho)=0\text{ for every }\rho.}
 \tag{9.546}
\]

The phrase “as an identity of rational functions” is essential.  For a
small prime, too few nonpole points may make a nonconstant rational
function take the same value at every available \(\mathbb F_q\)-point.
That finite-value alias is not a resonant component and is absorbed by
the fixed-\(m\) constant in (9.548); it must not be used to redefine
(9.546).

If \(k=|\{r_j\}|\), the corresponding complete nonpole sum is therefore
not merely large but exactly

\[
 \boxed{
 \sum_{v\ne-r_j}e_q(F(v))
 =(q-k)e_q\!\left(B\sum_jA_jr_j\right).}
 \tag{9.547}
\]

After subtracting (9.547), every remaining phase is nonconstant.  If
some \(R(\rho)\ne0\), it has a genuine simple pole and hence cannot be
of Artin--Schreier form \(G^q-G+\mathrm{constant}\); if all residues
vanish but \(L\ne0\), the remaining phase is nonconstant linear.  The
standard Weil bound consequently gives, uniformly for fixed \(m\),

\[
 \sum_{v\ne-r_j}e_q(F(v))
 -\mathbf 1_{\rm res}(q-k)e_q\!\left(B\sum_jA_jr_j\right)
 \ll_m q^{1/2}.
 \tag{9.548}
\]

Thus the square-root estimate itself is not the missing rank-one
input.  The missing input is an estimate for the explicit resonant
projector in (9.546)--(9.547).

The size of that projector explains exactly why the ordinary FKMS
Hölder route cannot simply absorb it.  Fix a partition of the \(2m\)
indices into \(k\) equal-shift blocks.  A singleton block is impossible
under \(a_j\ne b_j\), since then its single \(R_j\) is nonzero.  On every
remaining nonempty partition stratum there are \(4m+k\) dilation and
shift variables, and (9.546) imposes \(k+1\) equations.  Hence

\[
 \boxed{\dim\mathcal E_{m,\mathcal P}\geq4m-1,}
 \tag{9.549}
\]

independently of the partition.  The equal-shift example was only the
\(k=1\) stratum; for \(q=11,m=2\), the two-block choice

\[
 (r_1,r_2,r_3,r_4)=(0,0,1,1),\quad
 (a_1,a_2,a_3,a_4)=(1,1,1,1),\quad
 (b_1,b_2,b_3,b_4)=(2,8,2,8)
 \tag{9.550}
\]

also satisfies (9.546), every Type-II exclusion, and has the exact
nine-term value (9.547).  At \(m=\lceil\ell/3\rceil\), the positive
moment proof allows only dimension \(3m\); (9.549) exceeds it by
\(m-1\).  Equivalently, a term-counting proof would need an additional
factor \(q^{m-1}\) from the resonant family.

This identifies the precise place where the application-specific signs
must enter.  In the published arbitrary-coefficient proof, the
incidence weight \(\nu(r,s_1,s_2)\) is replaced by its absolute value
before Hölder, so (9.547) contributes positively and no Möbius
cancellation remains.  For the mollifier one must instead retain

\[
 \mu(qr)\,\mu(d),\qquad A=h\delta,qquad
 (\xi,j),\quad\text{and all dyadic/reflected packet labels}
 \tag{9.551}
\]

through the resonant projection.  After also applying the exact CRT
identity (9.537), the remaining analytic task has two parts:

1. prove the required signed \(q^{m-1}\) cancellation for the explicit
   equations (9.546), jointly over \(q,r,\chi,h,\delta\) and the outer
   packets;
2. keep the nonresonant remainder (9.548) and the cofactor characters
   inside the same global square, so that the pointwise
   \(\varphi(r)^{1/2}\) loss in (9.539) is never paid.

Call this pair of estimates the **resonance-subtracted coupled
character gate**, \(\operatorname{RSCCG}_3\).  It is narrower than asking
for a new arbitrary-kernel Type-II theorem: its principal piece is the
explicit finite projector (9.546)--(9.547), and its centered piece
already has the one-variable square-root bound (9.548).  It is not yet
proved, and an exhaustive adapter from every packet of (9.525) is still
required before one may assert
\(\operatorname{RSCCG}_3\Rightarrow\operatorname{CK}_{\rm ub}(3)\).
What has been proved here is the exact algebraic split and the fact that
all constant-phase failure in this Type-II moment family is concentrated
on the stated resonant projector.  Other steps of a full rank-one
analytic adapter, including the deepest diagonal stratum, are not
asserted here.

The finite helper rank_one_type_ii_resonance_audit checks
(9.543)--(9.547) on supplied finite data, including a two-shift resonant
example and exact subtraction of its nonpole main term.  It reports the
rational-function criterion separately from constancy of the sampled
finite values, with a \(q=5\) alias regression.  The general bound
(9.548) is the standard Weil input, not a floating-point test result.
The helper
rank_one_type_ii_resonance_partition_audit verifies the dimension ledger
(9.549) for every supplied shift partition and rejects singleton blocks
under the Type-II exclusion.

### 9.81 Zero dual frequency of the resonant projector

The projector in (9.546) itself admits the “principal first, centered
second” split required by the global strategy.  Fix one admissible
equal-shift partition \(\mathcal P\), with \(k\) blocks, and attach two
arbitrary coefficient families \(u_j(a)\), \(v_j(b)\) to every local
Type-II pair.  The phase in (9.547) can be absorbed into these local
families, since

\[
 e_q\!\left(B\sum_jA_jr_j\right)
 =\prod_j e_q(B\epsilon_jr_ja_j)
          e_q(-B\epsilon_jr_jb_j).
\]

The exact additive-orthogonality identity is

\[
 \boxed{
 \mathbf 1_{L=0}\prod_{\rho\in\mathcal P}\mathbf 1_{R(\rho)=0}
 =\frac1{q^{k+1}}
  \sum_{\lambda\bmod q}\ \sum_{(\eta_\rho)\bmod q}
  e_q\!\left(\lambda L+\sum_\rho\eta_\rho R(\rho)\right).}
 \tag{9.552}
\]

Consequently the weighted resonant sum factors completely:

\[
 \boxed{
 \mathfrak R_{\mathcal P}
 =\frac1{q^{k+1}}\sum_{\lambda,(\eta_\rho)}
   \prod_{j=1}^{2m}\mathcal L_j(\lambda,\eta_{r_j}),}
 \tag{9.553}
\]

where

\[
 \mathcal L_j(\lambda,\eta)
 =\sum_{\substack{a,b\in\mathbb F_q^\times\\a\ne b}}
 u_j(a)v_j(b)
 e_q\!\left(\epsilon_j\{
 \lambda(a-b)+\eta(a^{-1}-b^{-1})\}\right).
 \tag{9.554}
\]

No coefficient has been replaced by an absolute value.  In particular,
the zero dual frequency is explicit:

\[
 \boxed{
 \mathfrak R_{\mathcal P}^{(0)}
 =\frac1{q^{k+1}}\prod_{j=1}^{2m}
 \left\{
 \left(\sum_a u_j(a)\right)
 \left(\sum_b v_j(b)\right)
 -\sum_a u_j(a)v_j(a)
 \right\}.}
 \tag{9.555}
\]

The last term is precisely the local \(a=b\) Type-II diagonal removed
from the product of the two total masses.  Thus (9.555) is the genuine
nonoscillatory account; it is not part of the Weil remainder (9.548).
All other modes satisfy

\[
 (\lambda,(\eta_\rho))\ne(0,\mathbf0)
 \tag{9.556}
\]

and form the centered resonant spectrum.

This split does not yet bound either piece, but it removes an ambiguity
about what must happen next.  The principal expression (9.555) contains
short/long Möbius total masses and local diagonal corrections.  It must
be put back together across both AFE directions, every reflected
boundary packet, the explicit diagonal, all \(h,\delta\), and all
dyadic scales.  It can then be small, cancel, or produce a missing
secondary main term; no one of these outcomes is asserted here.
Termwise Mertens estimates would return the known unavailable power.

The centered modes (9.556) are again product-trace factors, now with at
least one genuine dual frequency.  They must be combined with the
squarefree CRT characters of (9.537) inside one global square.  Taking
absolute values in \((\lambda,\eta_\rho,\chi)\) would reintroduce the
same \(\varphi(r)^{1/2}\) and resonance-dimension losses already
isolated above.  Hence the remaining gate is now explicitly ordered:

1. globally evaluate the finite principal resonant master (9.555);
2. prove the centered, nonzero-dual coupled character operator bound.

The finite helper rank_one_resonance_orthogonality_audit evaluates the
direct congruence-state sum and the full dual sum independently, checks
(9.552)--(9.555) numerically on exact finite coefficient data, and keeps
both coefficient families signed.  Its proof-status flags leave both
the global principal evaluation and the centered operator estimate
false.

### 9.82 Pre-Poisson product-incidence orthogonality

There is one exact way to combine the retained \(h\delta\) phase with
the cofactor square function (9.539b).  It is an alternative ordering of
the \(h\)-orthogonality in (9.493), not a second saving available after
\(h\)-Poisson.

Let \(s=qr\) be squarefree, with \((q,r)=1\), and consider one cross term
in (9.539b) at a fixed common outer label \((h,\delta)\).  Put
\(x_i=d_ip_i\in U(s)\).  The cofactor character
orthogonality has already imposed

\[
 x_1\equiv x_2\pmod r.
 \tag{9.557}
\]

In the inverse part of the two \(q\)-traces the common AFE label leaves
the exact cross phase

\[
 \boxed{
 e_q\!\left(-\overline r_qh\delta
       (\overline{x_1}-\overline{x_2})\right).}
 \tag{9.558}
\]

Write

\[
 g=(x_1-x_2,q),\qquad Q=\frac qg.
 \tag{9.559}
\]

Because \(x_1,x_2\) are units, the gcd of
\(\overline{x_1}-\overline{x_2}\) with \(q\) is also \(g\).  Thus (9.558)
is \(e_Q(ch\delta)\) for a unit \(c\bmod Q\).  Moreover (9.557) and
\(x_1\equiv x_2\pmod g\) give the stronger collision

\[
 \boxed{x_1\equiv x_2\pmod{rg},\qquad rg=s/Q.}
 \tag{9.560}
\]

The conductor-one stratum is therefore exactly the full product
diagonal \(x_1\equiv x_2\pmod s\).  If \(q\) is prime, these are the only
two possibilities: \(Q=q\) off the full diagonal and \(Q=1\) on it.  For
composite \(q\), every small-conductor stratum is accompanied by the
stronger congruence (9.560).

For arbitrary finite coefficient arrays \(f_h,g_\delta\), group them by
residue modulo \(Q\):

\[
 F_a=\sum_{h\equiv a\ (Q)}f_h,\qquad
 G_b=\sum_{\delta\equiv b\ (Q)}g_\delta.
\]

The finite Fourier matrix then gives

\[
 \boxed{
 \begin{aligned}
 \mathcal S_Q(f,g)
   &:=\sum_h\sum_\delta f_hg_\delta e_Q(ch\delta)\\
   &=\sum_{a,b\bmod Q}F_aG_be_Q(cab),\\
 |\mathcal S_Q(f,g)|
   &\leq Q^{1/2}
      \left(\sum_{a\bmod Q}|F_a|^2\right)^{1/2}
      \left(\sum_{b\bmod Q}|G_b|^2\right)^{1/2}.
 \end{aligned}}
 \tag{9.561}
\]

This is just Cauchy and Parseval for a primitive additive Fourier
matrix, but no \(x_i,h,\delta\) cross term has been discarded.  If the
two supports are integer intervals of cardinalities \(H,L\), and both
coefficient arrays are one-bounded, residue multiplicity gives the
fully explicit ceiling

\[
 \boxed{
 |\mathcal S_Q(f,g)|
 \leq
 \{QHL\lceil H/Q\rceil\lceil L/Q\rceil\}^{1/2}.}
 \tag{9.562}
\]

Write \(Q=T^\lambda,H=T^h,L=T^\ell\), ignoring endpoint constants.
Relative to the trivial \(HL\), (9.562) saves the exact exponent

\[
 \boxed{
 \eta_{h\delta}(\lambda)
 =\frac12\{h+\ell-\lambda
 -(h-\lambda)_+-(\ell-\lambda)_+\}.}
 \tag{9.563}
\]

On the original balanced maximal box, not the later normalized
Type/Farey packet,

\[
 s\asymp T^3,\qquad H=L=T^{5/2}.
\]

Hence

\[
 \eta_{h\delta}(\lambda)=
 \begin{cases}
 \lambda/2,&0\leq\lambda\leq5/2,\\
 (5-\lambda)/2,&5/2\leq\lambda,
 \end{cases}
\]

so every reduced conductor \(T\leq Q\leq T^3\) supplies at least a
half-power on this isolated \(h,\delta\) operator.  This has the correct
numerical size to pay the final half-power in the later residual ledger
only if the preceding reductions and this ordering can be made
simultaneously.  No such compatibility is asserted by (9.563).

It does **not** yet prove the coupled-kernel gate.  Four adapters remain:

1. A squarefree \(s\asymp T^3\) has a divisor \(q\) between \(T\) and
   \(T^3\): take a prime factor at least \(T\), or multiply factors below
   \(T\) until their product first crosses \(T\).  But this controls
   \(q\), not the reduced conductor \(Q=q/(x_1-x_2,q)\).  The stronger
   collision strata (9.560) still need a joint divisor-incidence bound.
2. The original AFE weight is a smooth function of both \(h/H\) and
   \(\delta/L\), not necessarily one rank-one tensor \(f_hg_\delta\).
   It must be given a uniform finite/Fourier separable decomposition whose
   projective norm costs only \(T^\varepsilon\), while all other packet
   labels remain inside the same square.
3. Formula (9.493) completes one original \(h\)-sum and spends the phase
   on a determinant-line incidence.  Formula (9.561) instead acts on a
   cross term after cofactor-character orthogonality and **before** that
   completion.  Applying both estimates sequentially would double-count
   the same orthogonality.  A packet-exhaustion map must choose this
   ordering globally and rederive the diagonal/reflection ledger.
4. Most importantly, the full global Gram has two outer labels
   \((h_1,\delta_1)\) and \((h_2,\delta_2)\).  Its inverse cross phase is
   \[
   e_q\!\left(-\overline r_q
      (h_1\delta_1\overline{x_1}
       -h_2\delta_2\overline{x_2})\right),
   \]
   whereas (9.558) is only the equal-label slice.  The unequal-label
   cross terms must stay in the same pre-Cauchy operator.  Bounding the
   equal-label slice alone does not bound the full Gram.  Section 9.83
   derives the correct full finite Gram, but not its required estimate.

The finite helper hdelta_product_incidence_fourier_audit verifies
(9.557)--(9.562), including prime, composite reduced-conductor, and full
diagonal examples.  The exact-rational helper
hdelta_fourier_exponent_audit verifies the isolated ledger (9.563) at
\(\lambda=1,5/2,3\).  Both keep the low-conductor incidence estimate,
the unequal-label Gram, the smooth packet adapter, and the coupled-kernel
conclusion explicitly false.

### 9.83 The full unequal-label CRT character Gram

The missing algebra in the fourth item above can be completed exactly.
It changes the shape of the residual operator: the full outer-label
square is not the product-incidence energy (9.539b), but one cofactor
Kloosterman correlation which retains both labels.

Let \(\mathcal A\) be a finite set of outer product labels
\(a=h\delta\).  For \(s=qr\), \((q,r)=1\), and a unit \(B\bmod s\), put

\[
 K_{m,a}^{(t)}(x)=e_m\!\left(t(Bx-a\overline x)\right),
\]

with \(t=1\) for \(m=s\), \(t=\overline r_q\) for \(m=q\), and
\(t=\overline q_r\) for \(m=r\).  Given arbitrary signed coefficient
families \(c_a(x)\) on \(U(s)\), define

\[
 \mathcal B_s
 =\sum_{a\in\mathcal A}\sum_xc_a(x)K_{s,a}^{(1)}(x).
\]

For each label, take the multiplicative Fourier transform only in the
cofactor:

\[
 \widehat K_{r,a}(\chi)
 =\sum_{u\in U(r)}K_{r,a}^{(\overline q_r)}(u)\overline{\chi(u)},
 \qquad
 \mathcal B_{q,a,\chi}
 =\sum_xc_a(x)\chi(x)K_{q,a}^{(\overline r_q)}(x).
\]

CRT and Fourier inversion give the exact reconstruction

\[
 \boxed{
 \mathcal B_s
 =\frac1{\varphi(r)}
   \sum_{\chi\bmod r}\sum_{a\in\mathcal A}
   \widehat K_{r,a}(\chi)\mathcal B_{q,a,\chi}.}
 \tag{9.564}
\]

Make one Cauchy step in \(\chi\), with the complete \(a\)-sum still
inside:

\[
 \boxed{
 |\mathcal B_s|^2
 \leq\frac1{\varphi(r)}
 \sum_{\chi\bmod r}
 \left|\sum_{a\in\mathcal A}
 \widehat K_{r,a}(\chi)\mathcal B_{q,a,\chi}\right|^2.}
 \tag{9.565}
\]

Unlike the pointwise use of (9.539), this pays no
coefficient-independent \(\varphi(r)^{1/2}\) multiplier cost.  Expanding
the right side of (9.565) and using character orthogonality gives an
exact four-index kernel.  Put

\[
 z_a(x)=c_a(x)K_{q,a}^{(\overline r_q)}(x),
 \qquad y=x_1\overline{x_2}\pmod r.
\]

Then

\[
 \boxed{
 \begin{aligned}
 \frac1{\varphi(r)}\sum_\chi
 \left|\sum_a\widehat K_{r,a}(\chi)\mathcal B_{q,a,\chi}\right|^2
 =\sum_{\substack{a_1,a_2\in\mathcal A\\x_1,x_2}}
 z_{a_1}(x_1)\overline{z_{a_2}(x_2)}
 \mathcal C_r(a_1,a_2;y),
 \end{aligned}}
 \tag{9.566}
\]

where

\[
 \boxed{
 \begin{aligned}
 \mathcal C_r(a_1,a_2;y)
 &=\sum_{v\in U(r)}
 K_{r,a_1}^{(\overline q_r)}(vy)
 \overline{K_{r,a_2}^{(\overline q_r)}(v)}\\
 &=\sum_{v\in U(r)}
 e_r\!\left(\overline q_r\left\{
 B(y-1)v+(a_2-a_1\overline y)\overline v
 \right\}\right).
 \end{aligned}}
 \tag{9.567}
\]

Thus the full unequal-label character square collapses to one explicit
Kloosterman-type trace.  Since \(B\) is a unit, its simultaneous
direct/inverse principal mode is classified exactly:

\[
 \boxed{
 \begin{aligned}
 B(y-1)&\equiv0\pmod r,\qquad
 a_2-a_1\overline y\equiv0\pmod r\\
 &\Longleftrightarrow
 y\equiv1\pmod r,\qquad a_1\equiv a_2\pmod r,
 \end{aligned}
 \qquad
 \mathcal C_r=\varphi(r).}
 \tag{9.568}
\]

This principal set is larger than equality of the individual
\((h,\delta)\) labels: distinct products \(a_1,a_2\) remain resonant
whenever they are congruent modulo \(r\).  It must be recombined with the
zero dual mode (9.555), both AFE directions, reflection, and the explicit
diagonal.  Off (9.568), (9.567) is the centered cofactor Kloosterman
operator in the sense of being globally coefficient-nonprincipal.
For composite \(r\), this does **not** guarantee pointwise square-root
cancellation: individual CRT factors may still be locally principal,
and finite aliases can make \(\mathcal C_r=\varphi(r)\) even when the
two coefficients in (9.567) are not both zero modulo \(r\).  For example,
with
\[
 q=5,\quad r=6,\quad B=1,\quad y=5,\quad a_1=0,\quad a_2=2,
\]
the two coefficients are \(2,4\bmod6\), but
\(\mathcal C_6=\varphi(6)=2\).  These local-principal aliases remain
inside the coefficient-nonprincipal operator and must be stratified
prime by prime.  Full-amplitude aliases can have either sign: for
\(q=3,r=10,B=1,y=1,a_1=0,a_2=5\), one has
\(\mathcal C_{10}=-4=-\varphi(10)\).  A pointwise Weil estimate would
both miss this issue
and discard the outer labels; the required result must estimate (9.566)
jointly with the \(q\)-phase, both Möbius weights, and every dyadic packet.

The finite helper squarefree_crt_unequal_outer_character_gram_audit
verifies (9.564)--(9.568) independently by character expansion and by
the collapsed \(v\)-sum.  Its test includes distinct labels
\(a_1=2,a_2=9\) modulo \(r=7\), which lie on the principal set, a
coefficient-nonprincipal pair \(a_1=2,a_2=3\), and the composite
\(r=6\) finite alias above.  The principal reassembly and the centered
Kloosterman operator estimate remain explicitly false.

### 9.84 Prime-by-prime conductor of the cofactor kernel

The composite aliases in Section 9.83 can be isolated completely.  Put

\[
 A=B(y-1),\qquad C=a_2-a_1\overline y,\qquad
 g=(A,C,r),\qquad R_0=\frac r g.
 \tag{9.569}
\]

Since \(r\) is squarefree, CRT factors (9.567) into prime-modulus
Kloosterman traces:

\[
 \boxed{
 \mathcal C_r(a_1,a_2;y)
 =\prod_{p\mid r}
 \sum_{v\in\mathbb F_p^\times}
 e_p\!\left(t_p(Av+C\overline v)\right),
 \qquad
 t_p=\overline q_r\,\overline{(r/p)}_p.}
 \tag{9.570}
\]

For \(p\mid g\), the local factor is exactly \(p-1\).  For
\(p\nmid g\), if exactly one of the two local coefficients vanishes,
the factor is the Ramanujan sum \(-1\).  If both are nonzero, the
classical prime Kloosterman bound gives at most \(2\sqrt p\); for
\(p=2,3\) retain the sharper trivial ceiling \(p-1\).  Therefore, with

\[
 R_{\rm sm}=(R_0,6),\qquad R_{\rm lg}=R_0/R_{\rm sm},
\]

one obtains the unconditional squarefree-conductor estimate

\[
 \boxed{
 |\mathcal C_r(a_1,a_2;y)|
 \leq
 \varphi(g)\varphi(R_{\rm sm})
 2^{\omega(R_{\rm lg})}R_{\rm lg}^{1/2}
 \ll_\varepsilon
 \varphi(g)R_0^{1/2+\varepsilon}.}
 \tag{9.571}
\]

This includes every \(2\)- and \(3\)-adic finite alias from Section
9.83.  Relative to the coefficient-independent trivial scale
\(\varphi(r)=\varphi(g)\varphi(R_0)\), it gives square-root cancellation
in the genuine cofactor conductor \(R_0\).

The complementary low-conductor strata also carry exact incidence.
Since \(B\) is a unit and \(g\mid A,C\),

\[
 \boxed{
 y\equiv1\pmod g,\qquad a_1\equiv a_2\pmod g.}
 \tag{9.572}
\]

Thus no composite exception is left unclassified: either \(R_0\) is
large and (9.571) supplies a square-root kernel saving, or \(R_0\) is
small and (9.572) forces simultaneous product-ratio and outer-product
congruences modulo the large divisor \(g=r/R_0\).

This is still not the global coupled estimate.  Summing the
\(g,R_0\)-strata without losing (9.571), and exploiting (9.572) together
with the \(q\)-phase and both Möbius weights, is precisely the remaining
cofactor-conductor operator problem.  The finite helper
squarefree_crt_unequal_outer_character_gram_audit verifies the CRT
factorization, all one-zero Ramanujan values, the local
Weil/trivial ceilings, (9.571), and (9.572) for every supplied finite
packet.  It does not mark the global conductor-stratified operator bound
as proved.

### 9.85 Exact outer-label Fourier operator and the primitive product spectrum

Pointwise conductor stratification is not the strongest way to retain the
outer labels.  Fix a unit product ratio \(y\bmod r\), and regard (9.567) as
the complete \(r\times r\) matrix

\[
 C_y(a,b)=\sum_{v\in U(r)}
 e_r\!\left(\overline q_r
 \{B(y-1)v+(b-a\overline y)\overline v\}\right),
 \qquad a,b\bmod r.
 \tag{9.573}
\]

For the additive Fourier vector \(e_k(b)=e_r(kb)\), summing first over
\(b\) forces
\(\overline q_r\overline v+k\equiv0\pmod r\).  Hence there is no solution
when \((k,r)>1\), while for \(k\in U(r)\) the unique solution is
\(v=-\overline k\,\overline q_r\).  Substitution gives the exact action

\[
 \boxed{
 C_y e_k(a)=
 \begin{cases}
 r\,e_r\!\left(-B(y-1)\overline k\,\overline q_r^{\,2}\right)
       e_r(a\overline y k),&(k,r)=1,\\[2mm]
 0,&(k,r)>1.
 \end{cases}}
 \tag{9.574}
\]

Thus \(C_y\) is \(r\) times a phase-permutation on the primitive additive
frequencies and is zero on their orthogonal complement.  In particular,

\[
 \operatorname{rank}C_y=\varphi(r),\qquad
 \operatorname{Spec}_{\rm sing}(C_y)
 =\{r^{[\varphi(r)]},0^{[r-\varphi(r)]}\},\qquad
 \sum_bC_y(a,b)=\sum_aC_y(a,b)=0.
 \tag{9.575}
\]

Let \(P_r^{\rm prim}\) be additive Fourier projection onto
\((k,r)=1\).  For arbitrary residue arrays \(u,v\), (9.574) gives the
strictly sharper pre-Cauchy estimate

\[
 \boxed{
 \left|\sum_{a,b\bmod r}u_a\overline{v_b}C_y(a,b)\right|
 \le r\,\|P_r^{\rm prim}u\|_2\,
          \|P_r^{\rm prim}v\|_2.}
 \tag{9.576}
\]

Consequently the coefficient-principal entries and every composite
full-amplitude alias from Section 9.83 cancel inside complete rows and
columns before absolute values.  The remaining analytic input is not the
full residue energy.  For separated outer coefficients \(f_h,g_\delta\),
put

\[
 U_\rho=\sum_{h\delta\equiv\rho\,(r)}f_hg_\delta,
 \qquad
 \mathcal E_r^{\rm prim}(f,g)
 :=\|P_r^{\rm prim}U\|_2^2
 =\frac1r\sum_{\substack{k\bmod r\\(k,r)=1}}
 \left|\sum_{h,\delta}f_hg_\delta e_r(kh\delta)\right|^2.
 \tag{9.577}
\]

There is an exact elementary ceiling, but it does not exploit either
Möbius sign.  If \(M_g(m)\) is the maximum number of elements of
\(\operatorname{supp}g\) in one class modulo \(m\), then Cauchy in \(h\),
followed by full additive Parseval, gives

\[
 \mathcal E_r^{\rm prim}(f,g)
 \le \|f\|_2^2\|g\|_2^2
 \min\!\left\{
 \sum_{h\in\operatorname{supp}f}M_g\!\left(\frac r{(h,r)}\right),
 \sum_{\delta\in\operatorname{supp}g}M_f\!\left(\frac r{(\delta,r)}\right)
 \right\}.
 \tag{9.578}
\]

For supports in intervals of lengths \(H,L\), the divisor identity
\((n,r)=\sum_{d\mid(n,r)}\varphi(d)\) bounds the right side by

\[
 \mathcal E_r^{\rm prim}(f,g)
 \ll_\varepsilon
 \|f\|_2^2\|g\|_2^2
 \left(H+L+\frac{HL}{r}\right)r^\varepsilon.
 \tag{9.579}
\]

At the original balanced scale \(H=L=T^{5/2}\), \(r=T^3\), and
\(|f_h|,|g_\delta|\le1\), this only gives
\(\mathcal E_r^{\rm prim}\ll T^{15/2+\varepsilon}\).  The \(H+L\)
term is one half-power larger than the \(T^7\) product-density scale.
Therefore (9.574)--(9.576) remove the spurious pointwise alias obstruction
and identify a weaker surviving gate, but elementary Cauchy--Parseval still
does not close it: one must save a half-power in the primitive product
spectrum using the actual Möbius/AFE packet before the outer character
square is separated.

The finite helper cofactor_outer_product_fourier_operator_audit verifies
(9.573)--(9.576), including composite alias-rich moduli.  The helper
primitive_product_residue_energy_audit verifies (9.577), the exact finite
version of (9.578), and its interval ceiling.  The companion
primitive_product_spectrum_exponent_audit records the exact \(15/2\) versus
\(7\) balanced ledger.  At this stage all three helpers leave the analytic primitive-spectrum estimate
and the coupled-kernel gate explicitly false;
Sections 9.86--9.88 subsequently close the standalone smooth archimedean
spectrum, but not its joint arithmetic embedding.

### 9.86 A published fourth moment closes the unit-label interval subpacket

The half-power loss in (9.579) is not intrinsic on the stratum where both
outer variables are units modulo \(r\).  Let \(I,J\) be arbitrary translated
integer intervals, put

\[
 S_I(\chi)=\sum_{h\in I}\chi(h),\qquad
 S_J(\chi)=\sum_{\delta\in J}\chi(\delta),
\]

and extend Dirichlet characters by zero on nonunits.  Multiplicative
Plancherel in the primitive additive-frequency variable \(k\), applied to
(9.577), gives the exact identity

\[
 \boxed{
 \mathcal E_{r,U}^{\rm prim}(I,J)
 =\frac1{r\varphi(r)}
 \sum_{\chi\bmod r}
 |\tau_r(\overline\chi)|^2
 |S_I(\chi)|^2|S_J(\chi)|^2.}
 \tag{9.580}
\]

Here the subscript \(U\) means that \(h,\delta\) are restricted to
\(U(r)\), exactly as enforced by the character sums.  Cochrane--Shi,
Theorem 1, proves uniformly for every translated interval of length \(B\)
and every positive integer modulus \(r\) that

\[
 \frac1{\varphi(r)}
 \sum_{\chi\ne\chi_0}
 \left|\sum_{a<n\le a+B}\chi(n)\right|^4
 \ll
 8^{\omega(r)}\tau(r)(\log r)^3(\log\log r)^7B^2.
 \tag{9.581}
\]

For squarefree \(r\), the arithmetic factor on the right is
\(r^\varepsilon\), and the induced-character Gauss formula gives
\(|\tau_r(\chi)|^2\le r\).  Cauchy between the \(I\)- and \(J\)-moments
therefore bounds the nonprincipal characters in (9.580) by
\(r^\varepsilon |I||J|\).  The principal character has
\(\tau_r(\chi_0)=\mu(r)\).  Consequently

\[
 \boxed{
 \mathcal E_{r,U}^{\rm prim}(I,J)
 \ll_\varepsilon
 r^\varepsilon |I||J|
 +\frac{|I|^2|J|^2}{r\varphi(r)}.}
 \tag{9.582}
\]

On \(H=L=T^{5/2}\), \(r=T^3\), the two exponents in (9.582) are \(5\)
and \(4\), respectively.  Thus the sharp unit-label interval subpacket is
not merely at the \(T^7\) product-density scale: it lies two powers below
that scale.  This rigorously removes the apparent half-power obstruction
of (9.579) on this subpacket.

Three interfaces still prevent a global conclusion.  First, (9.580) does
not represent labels for which \((h\delta,r)>1\); those require an exact
\((h,r),(\delta,r)\) decomposition and include the fully resonant condition
\(r\mid h\delta\).  Second, the actual AFE weight must be decomposed into
translated interval or bounded-variation rank-one packets at
\(T^\varepsilon\) total projective cost.  Third, the resulting estimate
must remain inside the same \(q\)-phase, two-Möbius character square, and
global AFE/reflection packet map.  None of these three statements follows
from the scalar fourth moment.

The exact-rational helper cochrane_shi_unit_product_spectrum_audit records
the \(5,4\) exponents against the elementary \(15/2\) and product-density
\(7\) ledgers.  It marks only the unit, sharp-interval subpacket as covered;
the nonunit gcd strata, smooth adapter, joint two-Möbius packet, and full
coupled-kernel gate remain false.

### 9.87 Exact nonunit gcd descent closes every sharp interval stratum

The first missing interface after (9.582) can also be discharged without a
new analytic theorem.  For every pair \(h,\delta\), put

\[
 d=(h,r),\qquad e=(\delta,r),\qquad
 w=[d,e],\qquad R=\frac r w,\qquad
 h=dh',\quad\delta=e\delta'.
\]

Squarefreeness makes \(w\) and \(R\) coprime, and
\((d,e)=de/w\) is a unit modulo \(R\).  Hence

\[
 \boxed{
 e_r(kh\delta)
 =e_R\!\left(k(d,e)h'\delta'\right),\qquad
 h',\delta'\in U(R),}
 \tag{9.583}
\]

while reduction \(U(r)\to U(R)\) is exactly
\(\varphi(w)\)-to-one.  Splitting (9.577) by the exact pair
\((d,e)\), then applying Cauchy only across these divisor strata, gives

\[
 \mathcal E_r^{\rm prim}(I,J)
 \le \tau(r)^2
 \sum_{d,e\mid r}
 \frac{\varphi([d,e])}{[d,e]}\,
 \mathcal E_{r/[d,e],U}^{\rm prim}(I_d,J_e).
 \tag{9.584}
\]

Here \(I_d\) is the interval for \(h'=h/d\) with the exact restriction
\((h',r/d)=1\), and similarly for \(J_e\).  The primes in
\([d,e]/d\) and \([d,e]/e\) do not divide the reduced modulus; Möbius
inversion of those remaining coprimalities writes each \(I_d,J_e\) as
\(r^\varepsilon\) translated interval character sums.  Therefore every
term with \(R>1\) is covered by (9.582).  Summing the interval lengths over
\(d,e\) costs only \(r^\varepsilon\).

When \(R=1\), (9.583) has no oscillatory residue left.  This is not hidden:

\[
 R=1
 \Longleftrightarrow [d,e]=r
 \Longleftrightarrow r\mid h\delta.
\]

The complete mass of these fully resonant divisor strata has the elementary
Euler-product bound

\[
 \boxed{
 \sum_{\substack{d,e\mid r\\[d,e]=r}}
 \left(\frac Hd+1\right)\left(\frac Le+1\right)
 \ll_\varepsilon
 r^\varepsilon\left(1+H+L+\frac{HL}{r}\right).}
 \tag{9.585}
\]

Indeed, prime by prime there are only the three assignments
\((p\mid d,p\nmid e)\), \((p\nmid d,p\mid e)\), and
\((p\mid d,p\mid e)\); the \(HL\)-coefficient is
\(r^{-1}\prod_{p\mid r}(2+1/p)\), and all boundary coefficients are
\(r^\varepsilon\).

Combining (9.582)--(9.585), including the principal terms on all reduced
moduli, proves the separated sharp-interval estimate

\[
 \boxed{
 \mathcal E_r^{\rm prim}(I,J)
 \ll_\varepsilon
 r^\varepsilon\left\{
 HL+\left(1+H+L+\frac{HL}{r}\right)^2
 \right\}.}
 \tag{9.586}
\]

At \(H=L=T^{5/2}\), \(r=T^3\), both terms in braces have exponent \(5\).
Thus all unit and nonunit sharp-interval gcd strata lie two powers below
the \(T^7\) product-density scale.  At this stage the remaining interfaces
are the \(T^\varepsilon\)-projective decomposition of the actual smooth, nonseparable AFE packet
and its compatibility with the joint \(q\)-phase,
both Möbius weights, reflection, and the global packet map.  Formula
(9.586) alone does not provide either interface; Section 9.88 proves the
archimedean projective decomposition, but not the arithmetic compatibility.

The finite helper nonunit_product_gcd_strata_audit checks (9.583), the
uniform frequency-lift multiplicity, and the equivalence
\(R=1\Longleftrightarrow r\mid h\delta\) on supplied finite labels.  The
exact-rational helper cochrane_shi_all_gcd_product_spectrum_audit records
the exponent \(5\) in (9.586).  It leaves the smooth AFE adapter, joint
two-Möbius packet, and coupled-kernel gate explicitly false.

### 9.88 The archimedean smooth packet has bounded projective cost

The second interface listed after (9.582) is a functional-analytic adapter,
not a new arithmetic estimate.  It can be proved directly from the uniform
seminorm bound (5.14).  We record the argument because merely saying
``Fourier separation'' does not control the norm needed after Minkowski.

Let \(\Psi\) be one normalized core weight in (5.13)--(5.15), extended by
zero from its fixed compact support to a fixed four-dimensional torus.  The
dyadic cutoffs are smooth on the real line, so this extension is smooth.
Write its Fourier series as

\[
 \Psi(u,v,\alpha,\beta)
 =\sum_{\mathbf n\in\mathbb Z^4}
 c_{\mathbf n}\prod_{j=1}^4e(n_jx_j/P_j),
 \qquad (x_1,x_2,x_3,x_4)=(u,v,\alpha,\beta),
 \tag{9.587}
\]

where the fixed periods \(P_j\) are chosen larger than the supports.  For
an integer \(s>4\), Cauchy--Schwarz and Parseval give the weighted Wiener
bound

\[
 \boxed{
 \sum_{\mathbf n}|c_{\mathbf n}|
 (1+|n_3|)(1+|n_4|)
 \ll_s \|\Psi\|_{H^s}
 \ll_{s,W}\mathscr L^{C_s}.}
 \tag{9.588}
\]

Indeed, the first factor in Cauchy--Schwarz is the Sobolev square sum of
the Fourier coefficients, while the second is bounded by
\(\sum_{\mathbf n}(1+|\mathbf n|)^{4-2s}<\infty\).  Equation (5.14)
supplies the last inequality.  Thus (9.587) converges absolutely with the
two variation weights needed in the \(h\)- and \(\delta\)-coordinates.
It may be inserted into every finite arithmetic sum without a limiting
interchange.  On the power-enlarged upper-bound core of Section 6.3 the
same proof costs \(T^{O(\eta)}\), which is absorbed by the prescribed
\(\varepsilon_0\)-budget after \(\eta\) is chosen sufficiently small.

For completeness, the sharp-interval character estimate also survives
these variation weights.  If \(w\) is supported on an integer interval
\(I\), Abel summation gives

\[
 \left|\sum_{n\in I}w_n\chi(n)\right|
 \leq (\|w\|_\infty+\operatorname {Var}_I w)
       \max_{J\subset I}\left|\sum_{n\in J}\chi(n)\right|.
 \tag{9.589}
\]

A binary decomposition of every subinterval, followed by
\((\sum_{j\leq\log |I|}x_j)^4\ll(\log |I|)^3\sum_jx_j^4\), reduces the
fourth moment of the maximum in (9.589) to Cochrane--Shi (9.581) on
translated dyadic subintervals.  At each scale the sum of the squared
block lengths is \(O(|I|^2)\); hence all maximal and variation losses are
polylogarithmic.  Consequently (9.586) holds for separated bounded-
variation weights \(f,g\), multiplied by

\[
 (\log(2+H+L))^C
 (\|f\|_\infty+\operatorname {Var}f)^2
 (\|g\|_\infty+\operatorname {Var}g)^2.
 \tag{9.590}
\]

The logarithm is retained here because this weighted statement is uniform
even when the modulus is fixed and the intervals grow.  On the actual AFE
boxes, \(H,L\ll T^{O(1)}\), so it is absorbed into \(T^\varepsilon\), not
silently into a fixed-modulus \(r^\varepsilon\).

Finally apply (9.590) to each tensor in (9.587) and use the triangle
inequality for the Hilbert norm
\(\|P_r^{\rm prim}U\|_2\), before squaring.  The weighted projective norm
in (9.588) shows that the complete smooth archimedean factor preserves
(9.586) at \(T^\varepsilon\) cost.  In particular, at
\(H=L=T^{5/2},r=T^3\), it retains exponent \(5+\varepsilon\), rather than
the elementary \(15/2\).

This closes only the **archimedean smooth adapter**.  The coefficient
\(z_a(x)\) in (9.566) still contains the same-modulus \(q\)-phase
\(K_{q,a}(x)\), both Möbius weights, and the remaining packet labels.
Multiplying by that product phase is not a bounded-variation tensor in
\((h,\delta)\), and replacing it by an independent additive twist would
separate the very coupling that (9.565) was designed to retain.  Therefore
the joint \(q\)-phase/two-Möbius/reflection operator and the exhaustive
global packet map remain unproved; neither CK\(_{\rm ub}(3)\) nor the
twisted-moment upper bound is asserted here.

The helper finite_two_variable_fourier_projective_audit records the exact
finite Fourier reconstruction and its variation-weighted projective norm.
The exponent ledger smooth_projective_product_spectrum_audit records that
the sharp exponent \(5\) survives the smooth adapter while keeping the
joint arithmetic packet and coupled-kernel flags false.

### 9.89 Global ratio-frequency diagonalization before Type I/II

The remaining \(q\)-phase obstruction in Section 9.88 should not be
handled by applying (9.576) separately for every product residue \(x\).
There is a further exact reindexing which retains all cross terms.  It is
cleanest to take the cofactor in (9.564) to be the full squarefree modulus
\(s\), so that the complementary factor is (1).  For arbitrary arrays
\(c_x(a)\), \(x\in U(s)\), put

\[
 \widehat c_x(k)=\sum_{a\bmod s}c_x(a)e_s(-ka).
\]

In (9.567) set \(y=x_1\overline{x_2}\).  Summing first in \(a,b\), then
putting \(k=\overline v\) and \(\lambda=x_2k\), gives

\[
\boxed{
 \begin{aligned}
 &\sum_{x_1,x_2\in U(s)}\sum_{a,b\bmod s}
 c_{x_1}(a)\overline{c_{x_2}(b)}
 C_{x_1\overline{x_2}}(a,b)\\
 &\qquad=\sum_{\lambda\in U(s)}
 \left|\sum_{x\in U(s)}
 e_s(Bx\overline\lambda)
 \widehat c_x(\lambda\overline x)\right|^2\\
 &\qquad=\sum_{\lambda\in U(s)}
 \left|\sum_{t\in U(s)}e_s(Bt)
 \widehat c_{t\lambda}(\overline t)\right|^2.
 \end{aligned}}
 \tag{9.591}
\]

The second equality is the bijection \(x=t\lambda\).  The phase
simplifications are exact:

\[
 (x_1\overline{x_2}-1)\overline{k}
=(x_1-x_2)\overline\lambda,\qquad
 \lambda\overline{x}=\overline t.
\]

Thus the complete unequal-label Gram is one positive ratio-frequency
square.  No triangle inequality in \(x_1,x_2\), no pointwise conductor
bound, and no deletion of distinct congruent product labels occurs.

The identity becomes especially transparent on one rank-one tensor from
(9.587).  Suppose

\[
 c_x(a)=C(x)U(a),\qquad
 \widehat U(k)=\sum_aU(a)e_s(-ka),qquad
 A(t)=e_s(Bt)\widehat U(\overline t).
\]

Then (9.591) is the multiplicative correlation

\[
 \boxed{
 \mathcal G_s(C,U)
 =\sum_{\lambda\in U(s)}
 \left|\sum_{t\in U(s)}A(t)C(t\lambda)\right|^2
 =\frac1{\varphi(s)}\sum_{\chi\bmod s}
 |\widehat A(\overline\chi)|^2|\widehat C(\chi)|^2.}
 \tag{9.592}
\]

Here \(\widehat F(\chi)=\sum_{u\in U(s)}F(u)\overline{\chi(u)}\).
The last equality is multiplicative Parseval, not an inequality.  If the
product residue is formed from the two Type variables,

\[
 C(x)=\sum_{dp\equiv x\,(s)}\alpha_d\beta_p,
\]

then its transform factors exactly:

\[
 \boxed{
 \widehat C(\chi)
 =\left(\sum_d\alpha_d\overline{\chi(d)}\right)
  \left(\sum_p\beta_p\overline{\chi(p)}\right).}
 \tag{9.593}
\]

Equations (9.591)--(9.593) put the product trace, the complete outer-label
sum, and both Type polynomials inside one fixed-modulus character moment.  The smooth
projective norm (9.588) permits summing the rank-one tensors at
\(T^\varepsilon\) cost.  In the application \(\alpha_d\) contains the
Möbius sign \(\mu(d)\), and that sign remains inside (9.592).  However,
the outer sign \(\mu(s)\) is constant on a fixed-modulus block and is
squared away by (9.591).  Therefore one may not sum the positive quantity
(9.592) over \(s\) and claim that both original Möbius signs were retained.
The identity is an exact inner-block diagonalization, not yet the required
cross-modulus two-Möbius dispersion.

There is also a determinant form which is better suited to dispersion.
Opening the first square in (9.592) and using (9.593) gives the exact
incidence

\[
 \boxed{
 d_1p_1t_2\equiv d_2p_2t_1\pmod s.}
 \tag{9.594}
\]

Apply the remainder-free two-cutoff identity (9.241) to the single factor
\(\mu(d)\), and write \(d=bcn\).  Every I/I, I/II, II/I, and II/II term
in the square still satisfies

\[
 \boxed{
 b_1c_1n_1p_1t_2-b_2c_2n_2p_2t_1=js.}
 \tag{9.595}
\]

This is the promised pre-Cauchy Type I/II determinant: \(j=0\) is the
exact rational-product resonance, while \(j\ne0\) is the genuine
dispersion family.  The product label \(a=h\delta\) remains inside
\(A(t)=\sum_aU(a)e_s(Bt-a\overline t)\), and the Type sign remains as
\(\mu(b)\mu(c)\).  The outer sign \(\mu(s)\) can survive only if the
original \(s\)-sum is squared once globally, producing cross-modulus
blocks \((s_1,s_2)\); it is not present in the fixed-\(s\) positive square.

The available published estimates cover only projections of this master
identity:

| input | part genuinely controlled | missing hypothesis for (9.592)--(9.595) |
|---|---|---|
| Cochrane--Shi Theorem 1 | the unweighted primitive \(a=h\delta\) spectrum, including all gcd strata and BV weights, Sections 9.86--9.88 | no simultaneous weight \(|\widehat C(\chi)|^2\) and no outer \(s\)-average |
| multiplicative large sieve / classical character moments | the unweighted mean of the factored Type polynomial (9.593) | no correlation with the rank-one product trace \(|\widehat A(\bar\chi)|^2\); taking its supremum loses the recovered powers |
| FKM/FKMS prime Type I/II estimates | the fixed-prime outer wings recorded in (9.521)--(9.524) | the balanced rank-one inverse-pole resonance (9.546) and the composite-modulus/outer-\(s\) moment remain |
| Pascadi, Blomer--Pascadi, Milićević--Qin--Wu | bilinear forms with independently short classical Kloosterman arguments | (9.592) has one complete multiplicative character family weighted by a product-additive transform, as already exposed by (9.527)--(9.529) |

Thus (9.592) is a strictly more explicit **fixed-modulus inner gate** than
a generic pointwise kernel estimate, but it is not the surviving global
two-Möbius gate.  The next analytic task is to form the cross-modulus
\((s_1,s_2)\) analogue before any fixed-\(s\) square, subtract its exact
zero determinant, and apply one global dispersion step to the nonzero
determinants without taking absolute values over \(s_1,s_2\) or the Type
blocks.

The finite helper global_ratio_frequency_square_audit verifies all three
forms in (9.591), the character Parseval identity (9.592), and the Type
factorization (9.593).  It leaves the determinant estimate, outer-modulus
two-Möbius average, and coupled-kernel gate explicitly false.

### 9.90 The global linear character master retains both Möbius weights

The loss of \(\mu(s)\) in (9.591) is caused by the fixed-modulus Cauchy
step, not by multiplicative Fourier inversion itself.  Return to the exact
linear identity (9.564), take its cofactor to be the full modulus \(s\),
and perform the smooth tensor separation (9.587) without taking absolute
values over \(s\).  For one tensor put

\[
 \begin{aligned}
 \mathcal A_s(\chi;U)
   &=\sum_{t\in U(s)}e_s(Bt)\overline{\chi(t)}
       \sum_aU(a)e_s(-a\overline t),\\
 D_s(\chi)&=\sum_d\mu(d)\alpha_d\chi(d),\qquad
 P_s(\chi)=\sum_p\beta_p\chi(p).
 \end{aligned}
\]

Multiplicative inversion and the product congruence \(x\equiv dp\pmod s\)
give the boundary-exact global formula

\[
 \boxed{
 \mathscr S[\alpha,\beta,U]
 =\sum_s\frac{\mu(s)}{\varphi(s)}
   \sum_{\chi\bmod s}
   \mathcal A_s(\chi;U)D_s(\chi)P_s(\chi).}
 \tag{9.596}
\]

The left side is the original product-trace packet

\[
 \sum_s\mu(s)\sum_{d,p,a}
 \mu(d)\alpha_d\beta_pU(a)
 e_s\!\left(Bdp-a\overline{dp}\right),
 \tag{9.597}
\]

with the unit and dyadic restrictions absorbed in the displayed finite
coefficient families.  Thus (9.596), unlike (9.592), keeps \(\mu(s)\) and
\(\mu(d)\) simultaneously and linearly.  No character supremum and no
fixed-modulus positive square has appeared.

The single inner Möbius polynomial has an exact boundary-safe Type split.
Let \(W_0=\max(U_0,V_0)\).  Retain \(d\leq W_0\) as a finite small term;
for \(d>W_0\), insert (9.241).  Then

\[
 \boxed{
 D_s(\chi)=D_s^{\rm small}(\chi)
           -D_{s,U_0,V_0}^{\rm I}(\chi)
           +D_{s,U_0,V_0}^{\rm II}(\chi),}
 \tag{9.598}
\]

where

\[
 \begin{aligned}
 D_s^{\rm I}(\chi)
 &=\sum_{d>W_0}\alpha_d\chi(d)
   \sum_{bc\mid d\atop b\leq U_0,\ c\leq V_0}\mu(b)\mu(c),\\
 D_s^{\rm II}(\chi)
 &=\sum_{d>W_0}\alpha_d\chi(d)
   \sum_{bc\mid d\atop b>U_0,\ c>V_0}\mu(b)\mu(c).
 \end{aligned}
 \tag{9.599}
\]

Equations (9.596)--(9.599) are the requested pre-Cauchy two-Möbius Type
I/II master: the factor \(a=h\delta\) remains in \(\mathcal A_s\), the
outer sign \(\mu(s)\) remains outside the character sum, and the second
sign is represented exactly by the short--short/long--long divisor
families.  All small-\(d\) boundaries are displayed, and there is no mixed
rectangle or truncation remainder.

Only now may one perform a single global dispersion.  Its formal square
contains

\[
 \frac{\mu(s_1)\mu(s_2)}{\varphi(s_1)\varphi(s_2)}
 \varepsilon_{\star_1}\varepsilon_{\star_2}
 \mathcal A_{s_1}(\chi_1)\overline{\mathcal A_{s_2}(\chi_2)}
 D_{s_1}^{\star_1}(\chi_1)\overline{D_{s_2}^{\star_2}(\chi_2)}
 P_{s_1}(\chi_1)\overline{P_{s_2}(\chi_2)},
 \tag{9.600}
\]

for every ordered Type pair
\((\star_1,\star_2)\in
\{\mathrm{small},\mathrm I,\mathrm{II}\}^2\), with

\[
 \varepsilon_{\mathrm{small}}=\varepsilon_{\mathrm{II}}=1,
 \qquad \varepsilon_{\mathrm I}=-1.
\]

Thus all nine ordered cross-Type blocks, not only the three equal-Type
blocks, remain in the same signed global square.
This is the cross-modulus object which (9.592) cannot see.  Character
large sieves separately control an unweighted \(D\)- or \(P\)-square,
and Sections 9.86--9.88 control an unweighted \(\mathcal A\)-square, but
neither result bounds their product with the signed \((s_1,s_2)\) kernel
in (9.600).  Applying Cauchy to detach any one of the three factors
returns the known balanced deficit.

A targeted literature check does not presently fill this row.  Xi's
[moments of multiplicative analogues of Kloosterman
sums](https://arxiv.org/abs/2105.15051) concern, for one prime modulus,
the different trace
\(p^{-1/2}\sum_a\chi(a+\overline a)\) and certain special \(L\)-value
weights.  They do not provide a varying-squarefree-modulus estimate for
\(\mathcal A_s(\chi)D_s(\chi)P_s(\chi)\) with arbitrary dyadic Type
polynomials.  The KMS/FKMS trace-function bilinear theorems likewise fix a
prime modulus and require their stated NIO/gallant hypotheses; the
rank-one resonance audit in (9.530)--(9.549) remains applicable.  Thus
neither source is entered as coverage of (9.600).

Accordingly the remaining analytic gate is now stated on an exact finite
object: prove the target norm for the sum of (9.600), after recombining all
Type pairs and packet labels, by subtracting its zero determinant before
estimating the nonzero determinant family.  This is weaker and more
structured than an arbitrary coupled-kernel hypothesis, but it remains
unproved and has not yet been shown packet-exhaustive for every term of
(4.5).

The helper global_two_mobius_character_master_audit verifies (9.596)--
(9.599) for supplied finite squarefree moduli, including unequal cutoffs
and the small-\(d\) boundary.  It keeps the global dispersion, packet map,
and coupled-kernel flags false.

### 9.91 The cross-modulus zero product frequency is exactly diagonal

The first subtraction in the global square (9.600) can be identified
without an estimate.  For \(t\in U(s)\), define the reduced frequency

\[
 \xi(s,t)=\frac{\overline t_s}{s}\in(0,1).
 \tag{9.601}
\]

Both numerator and denominator are coprime.  Hence uniqueness of reduced
fractions gives

\[
 \boxed{
 \xi(s_1,t_1)=\xi(s_2,t_2)
 \Longleftrightarrow s_1=s_2\ \text{and}\ t_1=t_2.}
 \tag{9.602}
\]

More generally, for two distinct pairs with \(s_i\leq2S\),

\[
 \boxed{
 \|\xi(s_1,t_1)-\xi(s_2,t_2)\|_{\mathbb R/\mathbb Z}
 \geq\frac1{s_1s_2}\geq\frac1{4S^2}.}
 \tag{9.603}
\]

Thus the zero outer-product Fourier mode in
\(\mathcal A_{s_1}\overline{\mathcal A_{s_2}}\) has no hidden
cross-modulus component: it is exactly the same-\((s,t)\) diagonal.  On
that diagonal \(\mu(s_1)\mu(s_2)=1\), and its product-label energy is the
same primitive spectrum bounded in Sections 9.86--9.88.  It must still be
combined with the Type-polynomial diagonal and the explicit AFE/reflection
ledger, but no speculative cancellation is needed to classify it.

The complementary frequencies are separated enough for the classical
additive large sieve.  If \(U(a)\) is supported on an interval of length
\(A\), then

\[
 \sum_{S\leq s\leq2S}\ \sum_{t\in U(s)}
 \left|\sum_aU(a)e_s(-a\overline t)\right|^2
 \ll (A+S^2)\sum_a|U(a)|^2.
 \tag{9.604}
\]

At the balanced face \(A=HL=T^5\), \(S=T^3\), and
\(\sum_a|U(a)|^2\ll T^{5+\varepsilon}\), (9.604) has exponent \(11\).
The energy in (9.577) is normalized by \(1/s\).  For this comparison one
must first recover the unnormalized row energy \(s\mathcal E_s\), and then
sum it over \(s\asymp T^3\); the exponent ledger is therefore
\(3+3+5=11\), the same exponent as (9.604).  Thus the ordinary Farey large sieve correctly
separates the zero mode but supplies no additional power for the weighted
three-factor character master (9.596).  The needed gain must come from
the simultaneous Type and outer-modulus signs in the nonzero-frequency
part of (9.600), not from frequency spacing alone.

The helper primitive_product_farey_collision_audit checks (9.601)--
(9.603) on finite modulus families and records the balanced \(11\) ceiling.
It leaves the same-diagonal reassembly, signed nonzero-frequency estimate,
and coupled-kernel gate false.

### 9.92 Exact Euler centering of every cross-modulus frequency

The nonzero-frequency family has a further exact local decomposition before
any spectral estimate.  Let \(s_1,s_2\) be squarefree and write

\[
 g=(s_1,s_2),\qquad s_1=gr_1,\qquad s_2=gr_2,
 \qquad L=[s_1,s_2]=gr_1r_2.
\]

Then \(g,r_1,r_2\) are pairwise coprime.  For inverse labels
\(u_i=\overline{t_i}_{s_i}\), define the circular numerator

\[
 \kappa\equiv r_2u_1-r_1u_2\pmod L.
 \tag{9.605}
\]

Thus \(u_1/s_1-u_2/s_2\equiv\kappa/L\pmod1\).  The exact multiplicity
of this frequency is

\[
 \mathfrak m_{s_1,s_2}(\kappa)
 :=\#\{(t_1,t_2)\in U(s_1)\times U(s_2):(9.605)\}
\]

and CRT gives

\[
 \boxed{
 \mathfrak m_{s_1,s_2}(\kappa)
 =\mathbf 1_{(\kappa,r_1r_2)=1}
  \prod_{p\mid g,\ p\mid\kappa}(p-1)
  \prod_{p\mid g,\ p\nmid\kappa}(p-2).}
 \tag{9.606}
\]

Indeed, a prime dividing \(r_1r_2\) fixes the corresponding unit label
and forces \(p\nmid\kappa\).  At a prime \(p\mid g\), the nonzero pair
\((u_1,u_2)\in\mathbb F_p^\times\times\mathbb F_p^\times\) on the
linear fibre has \(p-1\) choices when \(p\mid\kappa\), and \(p-2\)
choices otherwise.  In particular, if \(2\mid g\), every odd
\(\kappa\) fibre is empty.  The zero fibre is nonempty exactly when
\(r_1=r_2=1\), recovering the same-\((s,t)\) diagonal in (9.602).

The outer signs simplify without an estimate:

\[
 \boxed{\mu(s_1)\mu(s_2)=\mu(r_1)\mu(r_2).}
 \tag{9.607}
\]

The common-factor sign has squared to one, but the two coprime-cofactor
Möbius signs remain.  This is the exact signed pair which a cross-modulus
dispersion estimate must retain.

More importantly, (9.606) has a canonical principal-density subtraction.
Put

\[
 z_p(\kappa)=\mathbf 1_{p\mid\kappa}-\frac1p.
\]

Then each \(z_p\) has mean zero modulo \(p\), and the entire frequency
multiplicity factors as

\[
 \boxed{
 \mathfrak m_{s_1,s_2}(\kappa)
 =\prod_{p\mid r_1r_2}
   \left(\frac{p-1}{p}-z_p(\kappa)\right)
  \prod_{p\mid g}
   \left(\frac{(p-1)^2}{p}+z_p(\kappa)\right).}
 \tag{9.608}
\]

The constant term is therefore

\[
 \boxed{
 \rho(s_1,s_2)
 =\frac{\varphi(r_1r_2)}{r_1r_2}\frac{\varphi(g)^2}{g}
 =\frac{\varphi(s_1)\varphi(s_2)}{[s_1,s_2]}.}
 \tag{9.609}
\]

Expanding (9.608) over squarefree \(q\mid L\) gives

\[
 \mathfrak m_{s_1,s_2}(\kappa)
 =\rho(s_1,s_2)
  +\sum_{1<q\mid L}c_q(s_1,s_2)
    \prod_{p\mid q}z_p(\kappa),
 \qquad
 \sum_{\kappa\bmod L}
 \bigl(\mathfrak m_{s_1,s_2}(\kappa)-\rho(s_1,s_2)\bigr)=0.
 \tag{9.610}
\]

This is an exact finite principal-mode/centered-complement decomposition,
not a probabilistic heuristic.  It identifies the local density which
must be returned to the AFE/reflection ledger and supplies an Euler basis
whose every nonconstant term has a genuinely mean-zero prime factor.

There is still a decisive boundary.  Formula (9.606) counts unweighted
inverse-label fibres.  The factors
\(e_{s_i}(Bt_i)\), the two Type polynomials, the smooth \(h\delta\)
packet, and all nine signs in (9.600) vary inside such a fibre.  Therefore
the weighted Type/AFE packet has not yet been centered merely by (9.608),
and no nonzero-frequency bound follows by taking the absolute value of
the coefficients \(c_q\).  The next valid step is to lift (9.608) through
the full weighted master and then apply dispersion only to the
\(q>1\) mean-zero Euler blocks.

The helper cross_modulus_product_frequency_density_audit verifies
(9.605)--(9.610) exactly for finite squarefree pairs.  It keeps the
weighted-packet centering, signed nonzero-frequency estimate, and
coupled-kernel flags false.

### 9.93 Arbitrary packet weights admit an orthogonal CRT centering

The restriction to unweighted fibres in Section 9.92 can be removed
algebraically, without taking an absolute value.  Continue to write
\(s_i=gr_i\) and \(L=[s_1,s_2]\), and identify

\[
 \Omega=U(s_1)\times U(s_2)=\prod_{p\mid L}\Omega_p,
 \qquad
 \Omega_p=
 \begin{cases}
  \mathbb F_p^\times\times\mathbb F_p^\times,&p\mid g,\\
  \mathbb F_p^\times,&p\mid r_1r_2.
 \end{cases}
 \tag{9.611}
\]

Let \(W:\Omega\to\mathbb C\) be arbitrary.  In the application it is
the entire fixed-\((s_1,s_2)\), fixed ordered-Type-pair packet, including
the two direct phases, both smooth \(h\delta\) sums, and all coefficient
labels.  Let \(E_p\) be uniform conditional expectation in the
\(\Omega_p\) coordinate, with every other CRT coordinate fixed, and put
\(\Delta_p=I-E_p\).  For \(q\mid L\), define

\[
 \boxed{
 W_q=\prod_{p\mid q}\Delta_p
     \prod_{p\mid L/q}E_pW.}
 \tag{9.612}
\]

The projections commute.  Finite product expansion and orthogonality give

\[
 \boxed{
 W=\sum_{q\mid L}W_q,\qquad
 \langle W_q,W_{q'}\rangle=0\ (q\ne q'),\qquad
 \sum_{q\mid L}\|W_q\|_2^2=\|W\|_2^2.}
 \tag{9.613}
\]

Moreover,

\[
 E_pW_q=0\quad(p\mid q),
 \qquad W_1=\overline W
 :=\frac1{|\Omega|}\sum_{\omega\in\Omega}W(\omega).
 \tag{9.614}
\]

Thus every nonconstant component has a literal zero conditional marginal,
not merely a zero heuristic density.  Cauchy over the divisor index costs
only

\[
 \sum_{q\mid L}\|W_q\|_2
 \leq\tau(L)^{1/2}\|W\|_2
 \ll_\varepsilon L^\varepsilon\|W\|_2.
 \tag{9.615}
\]

This decomposition now lifts (9.610) to an arbitrary weighted fibre.
With

\[
 F(u_1,u_2)=r_2u_1-r_1u_2\pmod L,
 \qquad
 \mathscr F_W(\kappa)=\sum_{F(u_1,u_2)=\kappa}W(u_1,u_2),
\]

one has the exact identity

\[
 \boxed{
 \mathscr F_W(\kappa)
 =\overline W\,\rho(s_1,s_2)
 +\overline W\bigl(\mathfrak m_{s_1,s_2}(\kappa)
                   -\rho(s_1,s_2)\bigr)
 +\sum_{1<q\mid L}\mathscr F_{W_q}(\kappa).}
 \tag{9.616}
\]

The first term in (9.616) is the constant Fourier mode as a function of
\(\kappa\); it is not the single \(\kappa=0\) fibre classified in (9.602).
Those two objects must remain separate in the AFE ledger.

Both terms after the displayed principal density are centered:

\[
 \sum_{\kappa\bmod L}
  \bigl(\mathfrak m_{s_1,s_2}(\kappa)-\rho(s_1,s_2)\bigr)=0,
 \qquad
 \sum_{\kappa\bmod L}\mathscr F_{W_q}(\kappa)=0
 \quad(q>1).
 \tag{9.617}
\]

Most importantly for (9.600), (9.612) is linear.  If the original packet
is written before Cauchy as

\[
 W=\sum_\lambda c_\lambda W^{(\lambda)},
\]

where \(\lambda\) contains \(h,\delta\), both Type labels, and the
ordered pair \((\star_1,\star_2)\), then

\[
 W_q=\sum_\lambda c_\lambda W_q^{(\lambda)}.
 \tag{9.618}
\]

Hence the \(a=h\delta\) product structure, the inner Type Möbius signs,
the outer factor \(\mu(s_1)\mu(s_2)=\mu(r_1)\mu(r_2)\), and all nine
ordered Type blocks remain linear throughout the centering.  No
fixed-modulus square or coefficient supremum is inserted.

Equations (9.611)--(9.618) complete the **algebraic weighted centering**,
but not the analytic dispersion.  Two tasks remain distinct:

1. reassemble the explicit principal density
   \(\overline W\rho(s_1,s_2)\) with both AFE directions, the reflected
   boundary terms, and the already isolated diagonal;
2. prove the target global norm for the two centered terms in (9.616),
   summed with \(\mu(r_1)\mu(r_2)\) and all ordered Type signs.

Zero marginal conditions alone do not imply a power saving, so neither
task is declared proved.  What has changed is the surviving gate: it may
now be stated only for the explicitly centered components in (9.616),
rather than for an arbitrary uncentered coupled kernel.

The helper weighted_cross_modulus_hoeffding_audit performs (9.611)--
(9.617) exactly for finite rational packets.  It verifies pointwise
reconstruction, pairwise orthogonality, energy conservation, every active
prime marginal, and fixed-frequency reassembly.  Its AFE/reflection
principal-density, signed centered-dispersion, and coupled-kernel flags
remain false.

### 9.94 The bare global square has no reciprocal-LCM normalization

There is a tempting but incorrect shortcut after (9.616).  Let
\(Z_s(u)\) denote one complete inverse-label packet before the outer
modulus sum, and put

\[
 Z_s^{\rm tot}=\sum_{u\in U(s)}Z_s(u),
 \qquad
 \mathscr S=\sum_s\mu(s)Z_s^{\rm tot}.
 \tag{9.619}
\]

For the ordered pair \((s_1,s_2)\), the rank-one weight is
\(W(u_1,u_2)=Z_{s_1}(u_1)\overline{Z_{s_2}(u_2)}\).  Therefore its
single-\(\kappa\) principal density in (9.616) is indeed

\[
 \overline W\rho(s_1,s_2)
 =\frac{Z_{s_1}^{\rm tot}\overline{Z_{s_2}^{\rm tot}}}
        {[s_1,s_2]}.
 \tag{9.620}
\]

However, the square of (9.619) contains the **unnormalized** sum over all
\(\kappa\bmod [s_1,s_2]\).  Consequently

\[
 \boxed{
 \sum_{\kappa\bmod [s_1,s_2]}
 \overline W\rho(s_1,s_2)
 =Z_{s_1}^{\rm tot}\overline{Z_{s_2}^{\rm tot}}.}
 \tag{9.621}
\]

The apparent reciprocal LCM in (9.620) is cancelled exactly by the number
of frequency residues.  After restoring the outer signs and summing the
moduli, (9.621) gives

\[
 \sum_{s_1,s_2}\mu(s_1)\mu(s_2)
 Z_{s_1}^{\rm tot}\overline{Z_{s_2}^{\rm tot}}
 =|\mathscr S|^2,
 \tag{9.622}
\]

not a smaller LCM quadratic form.  The latter would arise only from the
normalized frequency average

\[
 \sum_{s_1,s_2}
 \frac{\mu(s_1)\mu(s_2)
 Z_{s_1}^{\rm tot}\overline{Z_{s_2}^{\rm tot}}}{[s_1,s_2]},
 \tag{9.623}
\]

which could then be diagonalized into totient squares.  No factor
\([s_1,s_2]^{-1}\) is present in the bare global master (9.596)--(9.597):
the \(1/\varphi(s)\) from character inversion is cancelled when the
complete character sum is returned to the direct packet.

This does not rule out an LCM multiplier supplied by the original
AFE/\(TT^\ast\) kernel after every physical normalization is restored.
It does prove that such a multiplier must be exhibited explicitly; it
cannot be inferred from frequency centering alone.  Until the exhaustive
packet map produces it, the principal density may be as hard as the
original square, and no principal-density bound is claimed.

The helper weighted_principal_density_normalization_audit verifies
(9.619)--(9.623) exactly for finite rational modulus packets.  It keeps
the extra AFE/\(TT^\ast\) LCM normalization, principal-density bound, and
coupled-kernel flags false.

## 10. What has and has not been proved

**Current classification: Young closes each fixed scalar stratum and the
globally aggregated transition range \(\tau\geq1/4\); the equivalent
Type-I/II packet (9.242), divisor-incidence packet (9.250), and affine
Möbius--inverse packet (9.258) for \(0\leq\tau<1/4\), hence the full
Region-D recombination, remain unproved.  After transition completion,
all Type-I nonzero modes and all centered low-product modes are now
proved within target; their exact remaining projection is the joint
density-plus-complementary gate (9.310), equivalently the squarefree
parity-breaking bilinear gate (9.315).  The finite Ramanujan
diagonalization further closes every nonzero reduced denominator
\(2\leq r\leq D\); the strictly weaker zero/high edge gate (9.334),
with its quotient-aware two-Möbius form (9.337)--(9.344), remains
unproved.  The precompletion dual-product audit (9.345)--(9.351)
removes some high-gcd circle strata but leaves every dominant
\((k,q_\alpha)=1\), or \(\tau_k=0\), box at exponent \(5\), still one half-power above
target.  The exact $3\times2$ shifted-convolution identity
(9.352)--(9.358) shows that published standard-divisor shift errors are
numerically strong enough only after replacing the actual coefficients;
for the dyadic Möbius convolutions, both the nonvanishing zero/singular
term and the centered coefficient-transfer estimate remain unproved.
For the actual smooth separated kernel, (9.365)--(9.371) remove the
sharp full-residue and far-frequency spectra: the remaining balanced
gate is the single \(a,b\ll T^{1/2+O(\eta)}\),
\(|r-s|\ll T^{2+O(\eta)}\) block with both Möbius signs retained.  It
still needs a \(T^2\) saving and is not covered by the cited
Blomer--Pascadi theorem.  Reciprocity and completion modulo
\(d=r-s\) then remove even this short Kloosterman spectrum,
(9.372)--(9.377), reducing the decisive face to the weighted
two-dimensional Chowla gate \({\rm SC}_{2/3}\).  Published all-interval
and averaged-Chowla estimates give only logarithmic savings there, so
this final \(T^2\) pair saving remains unproved.  The boundary-exact
Fejér identity (9.378) identifies the same saving with the optimal
diagonal-sized short-Mertens mean square
\({\rm MS}_{2/3}\), also unavailable unconditionally.  Finally,
(9.380)--(9.386) identify the short-modulus zero frequency, before any
estimate and after summing every dyadic zero coefficient, with the
continuous \(m_1=m_2\) locus and its outer arithmetic factor with the
literal long-mollifier square.  This aggregate is not the original
Poisson \(h=0\) mode.  A fixed balanced box is only one broad Fourier
constituent, so global cancellation is not excluded; the identified
escape is the precompletion \(B_{N,i\tau}\) regrouping in (9.361), whose
uniform compact-\(\tau\) shifted energy is unproved.  Density centering
does not close that route: (9.387)--(9.390) cancel the infinite-series
pole but leave the complete finite product boundary, while the
transition contour ledger (9.391) shows that zeta convexity exactly
cancels the geometric line-shift gain.  The resulting diagonal-sized
compact-Mellin gate \({\rm CME}_3\), (9.392), is also unproved.
The exact Gaussian bilinear identity (9.393)--(9.395) further shows
that applying a standard Mellin \(L^2\) estimate returns the same
length-\(T^{7/2}\) product polynomial; Montgomery--Vaughan loses the
entire \(X/T=T^{5/2}\) window factor.  The integer-gap refinement
(9.396)--(9.402) now proves that every original lattice point on the
balanced short-\(d\) support has \(m_1=m_2\) and \(\delta=-m(r-s)\).
Its inverse phase is \(e_s(hm)\), so neither a second zeta-index average
nor shift oscillation can provide the missing power.  This applies only
after complete \(h\)-recombination, or to the exact divisibility
subpacket (9.402); it does not delete the complementary terms in one
fixed post-Poisson frequency box.  Finally, (9.403)--(9.407) show that
retaining the common compact-Mellin integral before absolute values is
weaker than \({\rm CME}_3\) but supplies only the original
\(m_1m_2\asymp T\) AFE constraint.  It is an exact loop back to the
balanced shifted-divisor packet, not a proved source of a power
saving.  The long-polynomial Fourier model (9.408)--(9.413) gives the
same \(X/T=T^2\) deficit.  Guth--Maynard explicitly reduce to the
classical first term when polynomial length exceeds the time interval;
here those exponents are \(X=T^3>T\), so their new large-value range
does not touch the residual face.  Finally, (9.414)--(9.421) show that
the balanced squarefree product has no von-Mangoldt component at
zero Mellin frequency and that its reflected diagonal is an exact LCM
form, while the nonzero shifted part remains a two-Möbius affine
correlation.  The diagonal high-gcd restriction cannot be used off the
diagonal, and nonzero compact Mellin frequencies retain many-prime
support.  The intact-mollifier Perron formula (9.422)--(9.426) does not
bypass this: its absolute-convergence line gives exponent \(4\) instead of
\(1\), while shifting far enough left enters a region of possible
reciprocal-zeta poles whose simple-zero residues contain uncontrolled
\(1/\zeta'(\rho)\).  Under RH, however, there are no poles between the two
positive \(w\)-lines, and Bui--Florea's fixed-shift fourth negative moment
closes the full \(\theta=3\) mollified second moment by (9.427)--(9.432).
This last closure is conditional on RH and does not change the unconditional
status.  Bettin--Gonek's converse calibration (9.433)--(9.436) does not make
the dyadic target RH-hard: at \(\theta=3\) its zero-free boundary is the
vacuous \(7/6\).  It instead shows that a viable unconditional residue
argument must retain the height displacement lost by a global negative
moment.  The new finite master schema (9.437)--(9.448) keeps every supplied
labelled secondary-zero packet, both reflected cross terms, and the explicit
diagonal before centering, while excluding the original \(h=0\) mode
already settled in (4.6).  Its decomposition is exact but depends on the
as-yet-underived principal density: changing that density moves mass
between \(\mathcal M_{\rm res}\) and \(\mathcal R_{\rm cent}\); the
exhaustive analytic adapter from (4.5) is also not yet constructed.  Finally,
(9.449)--(9.455) identify the exact \(T^2\) operator saving, equivalently
\(T^4\) after \(TT^*\), and split the global Gram form into determinant-zero
and determinant-nonzero orbits.  Neither the resonant evaluation nor the
nonzero-determinant spectral estimate has been proved.  Finally,
(9.456)--(9.464) identify the actual aggregate zero-mode projector as the
time-Fourier Gram.  Its Gaussian \(1,2,4\) minor, even after diagonal
removal, has rank \(3\), whereas every row/column/grand projection has
rank at most \(2\).  Thus product-density centering cannot isolate the
whole resonance; the surviving high-rank banded Möbius energy remains
unproved.  The primitive-slope lemma (9.465)--(9.468) also proves that
the determinant-zero Gram orbit contains only equal \((k_0,\ell_0)\);
it is a sum of same-slope squared norms, with no cross-slope resonances.
Its remaining outer-parameter cancellation is unproved.  The subsequent
Type ledger (9.469)--(9.482) distinguishes the auxiliary sector character
\(\xi\) from \(a_{\rm AFE}=h\delta\), proves the exact common-sector
Euclidean remainder identity, and recombines every internal \(dm=r\)
cross factorization before Cauchy.  The Type-entry determinant-zero part
is exactly the original self diagonal and has no positive-power deficit;
the sector model's extra power is confined to
\(\Delta_{\rm Type}\ne0\).  This does not close either that offdiagonal
estimate or the separate global same-slope gate.  The fixed-function
collision (9.483)--(9.484) additionally rules out applying the published
scalar metric-Beatty \(L^2\) theorem across the moving sector family.
The structured Sobolev transfer (9.498)--(9.503) now proves that separated
reciprocal-grid sampling itself costs only \(T^\varepsilon\) for a fixed
Hilbert coefficient family; hence sampling is no longer listed as a
separate half-power obstruction.  Deriving that fixed family from the
moving two-Möbius packet remains open.
The exact labelled split (9.485)--(9.487) now retains all four Type-pair
blocks and every \(h\delta\) packet before separating \(\Delta=0\) from
\(\Delta\ne0\); only the former is recombined, while the joint signed
nonzero-determinant estimate remains open.  Equations (9.504)--(9.508)
replace an absolute estimate of that signed sum by its exact centered
positive moving-Beatty projector.  This projector still requires one
power of energy cancellation and no published fixed-slope logarithmic
Beatty theorem proves its moving-grid Hilbert-valued bound.  The exact
sector Fourier formula (9.510)--(9.515) now closes every primitive
half-jump boundary by a one-entry-per-sector bijection.  The remaining
continuous harmonics have the direct Type phase \(e(adp/s)\), but the
standard additive-large-sieve ledger (9.516) is still one full power of
energy above target.  Recombining that harmonic with the retained
\(h\delta\)-inverse phase gives the genuine nonhomogeneous Kloosterman
phase (9.517).  The focused coverage table (9.520)--(9.524) shows that
published pointwise Type-I estimates cover only the outer factor wings
and save at most \(1/24\) on prime moduli or \(1/35\) uniformly on
composite moduli.  FKM's bilinear trace theorem covers fixed
prime-modulus off-balance slices with saving at most \(1/8\), but
degenerates at exact balance.  The composite central Type-II band and
the required joint \(s,\xi,h\delta\) moment remain unproved.**

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
* the power-enlarged upper-bound tail estimate (6.12) and the weakest
  sufficient implication
  \(\mathrm{CK}_{\rm ub}(3)\Rightarrow
  \mathcal R_{T^3,T}\ll_{\varepsilon,W}T^{1+\varepsilon}\), (6.13);
* the exact Region A--C coverage classification, (8.1)--(8.9).
* the finite Möbius identity (9.3)--(9.5), its exact substitution (9.7),
  and the five-term proof that termwise fixed-factor summation does not
  cover the residual boxes, (9.8)--(9.12).
* the exact applicability audit of Pascadi Theorem 7.8 and its remaining
  balanced exponent gap, (9.14)--(9.21).
* the exact Milićević--Qin--Wu applicability obstruction and the
  reverse-Poisson identity, (9.22)--(9.26).
* the direct Möbius--inverse-phase audit, including its balanced
  \(T^{5-o(1)}\) residual gap, (9.27)--(9.30).
* the boundary-safe elementary Farey large-sieve estimate and its exact
  \(A^{1/2}\) loss, (9.31)--(9.36).
* the two-sided finite Möbius decomposition, its CRT phase, and the exact
  dispersion interface, (9.37)--(9.42).
* the direct specialization of Pascadi's spectral-dispersion corollary
  and its \(T^{11/2}\) balanced gap, (9.43)--(9.46).
* the direct fourfold scale comparison, exact gcd--character phase
  stratification, and the standard character-large-sieve obstruction,
  including the dual lowest-mode zero-free barrier, (9.47)--(9.55).
* the exact primitive-conductor Gauss factor, cancellation of the cofactor
  Möbius sign, and the principal-character \(1/3\) obstruction diagnostic,
  (9.56)--(9.60).
* the coprime reverse-Poisson identity and the unconditional global bound
  for the unit principal spectrum, (9.61)--(9.64).
* the full Ramanujan projection, its exact zero-mode recombination, and
  the residual top-face long--short principal Type-II form,
  (9.65)--(9.74).
* the exact reverse completion of the unit spectrum, its highest-divisor
  affine parametrization, and the normalized binary Möbius correlation
  diagnostic, (9.75)--(9.82).
* the exact applicability map for averaged Chowla and its remaining
  polynomial-slope obstruction, (9.83)--(9.86).
* the centered Ramanujan mean-zero identity, exact divisor--dual
  cancellation of all common integral dual frequencies, and its confined
  cofactor support, (9.87)--(9.92).
* the delta-completion window and exact self-dual affine
  parametrization, (9.93)--(9.99).
* the one-dimensional post-centering scale ledger and the resulting
  no-coverage certificates for completion, averaged Chowla, and direct
  spectral dispersion, (9.100)--(9.102).
* the exact remapping of Wright's unbalanced-convolution corollary and
  its negative modulus margins on the full balanced \(J\)-interval,
  (9.103)--(9.105).
* the exact convolution/Fourier-energy form, its general-coefficient
  \(V\)-loss, the unconditional \(J/M=T^{O(\eta)}\) boundary coverage,
  and the separated central-arc Mertens thresholds, (9.106)--(9.110).
* the global reverse completion of every nonprincipal gcd stratum into
  one dilated centered Ramanujan family, including all \(k\mid e\)
  boundary terms, (9.111)--(9.115).
* the exact recombination of the centered and principal spectra and the
  weakest remaining joint gate after all proved complements are removed,
  (9.116)--(9.119).
* the generalized divisor-dual identity, cancellation of every common
  dilated frequency, and the exact self-dual scale ledger on all gcd
  strata, (9.120)--(9.129).
* the finite sign-migration bijection which moves
  \(\mu(e)\mu(k)\) to \(\mu(E)\) and exposes the three-Möbius nonunit
  family, (9.130)--(9.135).
* the exact Blomer--Pascadi length margins, Pascadi modulus-average
  margins, integral fourth-trace formula, projective-character identity,
  and the raw-cycle counterexample, (9.136)--(9.146); these identify but
  do not prove the coherent cross-modulus bridge (9.147).
* the fixed-numerator inverse-linear spacing lemma (9.148)--(9.150) and
  the exact proof that collapsing \(h\delta\) to arbitrary product
  coefficients leaves the same \(A^{1/2}\) operator loss,
  (9.151)--(9.154).
* the cross-numerator divisor switch, natural-scale unsigned Farey collision
  exponent, exact rational-denominator strata, product-kernel resonance,
  and two-dimensional additive completion, (9.155)--(9.164); these
  narrow but do not prove the signed cross-modulus gate.
* the exact additive-dual shifted-Chowla coordinates and moving endpoints,
  the complete axis/origin recombination, and the lowest-block
  \(X^{2/3}\)-shift power ledger, (9.165)--(9.179); these remove the
  separately bounded zero mode, close the near-block exponent polytope,
  and prove that one-modulus Parseval still misses the target.
* the exact smooth modulated double completion, rapid dual-tail estimate,
  and actual support exponents (9.365)--(9.371); these prove that the
  sharp full-residue spectrum is unnecessary and reduce the balanced
  obstruction to the short \(s^{1/6}\times s^{1/6}\) dual block.  The
  exact Blomer--Pascadi margins are all negative there, so the required
  double-Möbius \(T^2\) saving remains unproved.
* additive reciprocity followed by smooth completion modulo the shift,
  (9.372)--(9.376), and the resulting explicit weighted-Chowla form
  (9.377).  All nonzero short-modulus dual modes are arbitrary-power
  small because \(H,L>d\).  The remaining \({\rm SC}_{2/3}\) gate is
  strictly simpler but still asks for an unavailable fixed \(T^2\)
  saving in the two-Möbius pair sum.
* the finite Fejér/sliding-window identity (9.378) and its exact
  exponent ledger.  It identifies the \(T^2\) deficit with the gap
  between trivial \(XD^2=T^7\) and optimal diagonal-sized
  short-Mertens energy \(XD=T^5\); it does not assert the latter bound.
* the exact equal-zeta-variable identity (9.380)--(9.383), the gcd
  factorization of its aggregate zero coefficient into the
  long-mollifier square (9.384), and the finite formal
  von-Mangoldt identity (9.385).  These prove that the complete
  shift-zero aggregate is a continuous equal-index long-mollifier
  square, not a second copy of the original \(h=0\) LCM mode.  A fixed
  balanced box retains a broad Fourier cutoff; these identities do not
  prove \({\rm MS}_{2/3}\), its necessity for every weight, or the
  uniform \(B_{N,i\tau}\) replacement.
* the exact truncated generating series and density centering
  (9.387)--(9.389), including the complete moving product boundary
  (9.390).  At the pole density the separated bulk vanishes but the
  boundary survives.  On \(X=T^{7/2},H=X/T\), contour geometry saves
  \(T^{-c/2}\) while zeta convexity costs \(T^{c/2}\), (9.391).
  The sufficient compact-Mellin correlation gate (9.392) therefore
  remains a new, unproved diagonal-sized estimate rather than an
  elementary consequence of pole cancellation.
* the exact finite Gaussian product-polynomial identity
  (9.393)--(9.395).  It identifies the compact shifted correlation
  with a bilinear mean of the same \(B_{N,z}\) polynomial.  Cauchy
  returns its long \(L^2\) norm, while Montgomery--Vaughan loses
  \(X/T=T^{5/2}\), exactly the factor required by \({\rm CME}_3\).
  Thus standard Mellin \(L^2\) is circular here, not a proved weaker
  gate.
* the endpoint-exact integer-gap lemma (9.396)--(9.399) on the original
  short-shift lattice and the inverse-phase linearization (9.400).
  At the balanced scale it forces \(m_1=m_2\), \(\delta=-m(r-s)\), and
  retains \(h\delta=-hm(r-s)\), while \(HM/S=T^{o(1)}\).  The exact
  post-Poisson divisibility subpacket is (9.402).  The lemma does not
  apply termwise to the continuous \(x\)-integral in a fixed \(h\)-box,
  so it narrows the obstruction to the equal-index two-Möbius band but
  does not prove its required \(T^2\) cancellation.
* the exact common-Mellin recombination (9.403)--(9.407).  Before taking
  an absolute value, both divisor twists cancel against the single
  product factor \((xy)^{-i\tau}\), leaving only the Fourier constraint
  on the original zeta-index product \(nm\).  The actual AFE kernel
  reconstructs \(V_t(nm)\), so this strictly weaker formulation loops
  back to the original shifted-divisor geometry and does not provide
  an independent orthogonality or power saving.
* the exact long-polynomial Fourier identity (9.408)--(9.410) and its
  mean-value ledger (9.411)--(9.413).  A time interval of length \(T\)
  resolves only blocks of \(X/T=T^2\) adjacent coefficients in a
  length-\(X=T^3\) Möbius polynomial.  The classical normalized bound
  has exponent \(3\) against diagonal exponent \(1\).  Guth--Maynard
  revert to that classical first term for \(N_{\rm GM}\geq T_{\rm GM}\),
  so their coefficient-agnostic large-value theorem supplies none of
  the missing \(T^2\).
* the balanced zero-Mellin reflection (9.414), the four-term pair-kernel
  energy identity (9.415), the exact short-cofactor unfolding
  (9.416), and the diagonal LCM form (9.418)--(9.419).  These remove the
  von-Mangoldt component at \(\tau=0\) on the balanced squarefree
  product and close its boundary diagonal.  For nonzero shifts the same
  unfolding leaves the affine two-Möbius family (9.420)--(9.421); the
  diagonal high-gcd constraint and the zero-frequency vanishing do not
  extend to that family.
* the exact Perron representation of the intact tapered mollifier
  (9.422)--(9.424), its critical-line exponent ledger (9.425), and the
  simple-zero residue formula (9.426).  At \(N=T^3\) the direct contour
  exponent is \(4\) against target \(1\); moving to the required
  \(c=o(1)\) enters a region where possible poles have simple-zero weights
  \(1/\zeta'(\rho)\).  Existing negative moment results do not provide the
  unconditional all-zero residue bound, so this is a certified obstruction
  rather than a closure of the gate.
* conditional on RH, the pole-free shift to every fixed \(c>0\), the
  Bui--Florea \(k=2\) negative fourth moment, and the classical positive
  fourth moment give the ratio estimate (9.430)--(9.431).  Hence (9.432)
  proves the full mollified second-moment bound
  \(\ll_{\varepsilon,\theta}T^{1+\varepsilon}\) for every fixed \(\theta\),
  including \(\theta=3\).  This is a conditional theorem and supplies no
  unconditional control of off-critical zeros.
* the exact Bettin--Gonek zero-free consequence ledger (9.433)--(9.435).
  Uniform long-mollifier control on \([0,T]\) at \(\theta=3\) would exclude
  \(\Re\rho>2/3\), but the actual dyadic \([T,2T]\) implication excludes
  only \(\Re\rho>7/6\) and is vacuous.  Their model (9.436) exhibits the
  dyadic \(T^{-3}\) displacement factor; it is not an unconditional
  all-zero expansion or an upper bound.
* the boundary-exact secondary-zero master schema (9.437)--(9.448), for
  supplied labelled AFE directions, \(h,\delta\), and dyadic packets,
  both nonsymmetric reflected cross terms, the explicit diagonal, and
  the weighted zero-row/zero-column centered kernel.  The finite identity
  has no endpoint error and rejects the already counted original \(h=0\)
  mode.  It also proves that arbitrary choices of the centering density
  change the separate resonant and centered terms, so no canonical
  principal mode or estimate is claimed.  Constructing the exhaustive
  analytic packet adapter from (4.5) is not part of this proved schema.
* the centered \(2\to2\) exponent ledger and the global finite \(TT^*\)
  determinant split (9.449)--(9.455).  Raw exponent \(5\) to target
  exponent \(3\) requires \(T^2\) before squaring and \(T^4\) in the Gram
  form.  The determinant-zero and determinant-nonzero pieces recombine
  exactly, but their required resonant and spectral estimates remain
  unproved.
* the exact aggregate Fourier-projector formula (9.456)--(9.459) and the
  rank obstruction (9.460)--(9.463).  On the Gaussian indices \(1,2,4\),
  both the full Gram and its diagonal-removed kernel have nonzero
  \(3\times3\) determinant, while the resonant projection of any
  product-density double centering has rank at most \(2\).  This proves
  that the explicit diagonal plus row/column modes cannot remove the
  whole zero packet; estimating the remaining banded Möbius energy is
  still open.
* the primitive-slope determinant-zero reduction (9.465)--(9.468).
  For positive coprime slope pairs, determinant zero is equivalent to
  equality of the two slopes, so the whole zero orbit is a sum of
  same-slope squared norms.  Cross terms in \(g,h,\delta,\nu,\sigma\)
  remain inside each square and are not estimated here.
* the label-safe one-factor Type ledger (9.469)--(9.482).  It keeps
  \(a_{\rm AFE}=h\delta\) distinct from the auxiliary sector character,
  proves \(Q\Delta_{\rm Type}=\rho_1s_2-\rho_2s_1\) on a common
  Euclidean quotient, and recombines all prime-power Type
  cross-factorizations to the original Möbius-log coefficient.  The
  nonprincipal Type-entry diagonal is exactly
  \((1-M^{-1})D_{\rm cont}\); only its
  \(\Delta_{\rm Type}\ne0\) complement can carry the extra power.
  Neither that complement nor the global same-slope estimate is proved.
* the exact sector-step Fourier completion (9.510)--(9.516).  The
  primitive jump set is in bijection with the \(Q\) Beatty sectors, so
  after recombining all labels its centered boundary contribution is
  bounded by the already-controlled continuous diagonal.  Every
  nonboundary harmonic becomes the retained-label Type phase
  \(e(adp/s)\).  Standard additive large sieve applied after Cauchy still
  has energy exponent \(3\) at the balanced face instead of the target
  \(2\), so the continuous Type-I/II estimate remains unproved.
* the exact recombination of the sector harmonic with the AFE inverse
  phase, (9.517)--(9.519), and the resulting one-factor coverage
  polytope (9.520)--(9.524).  The prime-bearing phase is
  \(e_s(\alpha dp-h\delta\bar d\bar p)\), with both Möbius factors and
  the factorization \(h\delta\) retained.  Korolev's composite-modulus
  theorem saves at most \(1/35\), while the FKM one-variable
  prime-modulus trace theorem has limiting saving \(1/24\).  FKM
  Theorem 1.17 improves fixed prime-modulus bilinear slices to at most
  \(1/8\), but gives zero at exact balance.  None supplies the required
  joint half-power or the composite central Type-II estimate.
* the exact unit-lift formulas, complete squarefree double-unit divisor
  spectrum, Möbius sign migration, and closed scalar-stratum identity,
  (9.180)--(9.186); these isolate the still-unproved top spectrum from
  its proper Ramanujan-divisor layers.
* the coprimality-migrated triple spectrum (9.187), its exact bridge to a
  theorem-compatible Kloosterman fraction (9.188)--(9.189), and the
  Bettin--Chandee exponent audit (9.190)--(9.193); the theorem saves
  \(T^{5/16}\) but still misses the completed primitive stratum target by
  \(T^{67/16}\), and its gap is at least \(T^2\) on every balanced
  scalar-factor box.
* the centered common-divisor covariance (9.194)--(9.196), centered
  scalar-divisor packet (9.197), and exact dual Kloosterman interface
  (9.198)--(9.201); coprime oscillatory moduli are exactly orthogonal and
  the zero dual mode collapses to their common divisor, while the
  nonzero dual mixed moment remains unproved.
* the factorwise centered CRT identity (9.205)--(9.208), which splits the
  coprime double-Möbius tensor into nine terms with no all-principal
  factor on either side, and the exact balanced unit-mean screening
  ledger (9.209)--(9.211).
* the exact numerator-Fourier unit support (9.212), smooth completion
  (9.213), dual reciprocity (9.214), and Young varying-level large-sieve
  map (9.215)--(9.217); for each fixed scalar stratum the primitive fully
  centered raw term saves \(T^2\), and the complete three-gcd exponent audit
  (9.218)--(9.219) never exceeds the target exponent \(9\).  The
  squarefree mean factors have the elementary dyadic bound (9.220).
* the pre-residue numerator transform (9.221), exact four-term
  common-modulus collision formula (9.222), and compatibility divisor
  (9.223); cancelling \(t=(m,n)\) from the Young rational gives the
  fixed-scalar common-stratum ledger (9.226), whose nonzero-dual
  collision term has exponent \(9-2\tau\) before the scalar sum; the
  four-parameter fixed-stratum gcd audit is (9.227).
* the exact Ramanujan marginal factorization (9.228), its exponent
  margins (9.229), the recombined zero-mode congruence (9.230), and the
  finite interval boundary bound (9.231); after restoring the scalar
  cost these still control all marginal and zero-mode terms, but not the
  small-common-factor collision.
* the general nonunit numerator transform (9.232) and ambient CRT
  factorization (9.233); nonunit multipliers reduce to the same centered
  collision on shorter moduli, while the gcd selection and numerator
  restriction exactly balance and the free normalized Ramanujan factor
  costs no power, (9.234).
* the scalar-factor correction (9.235)--(9.238): after restoring the
  missing transition scalar sum, Young has exponent \(19/2-2\tau\), so
  it covers exactly \(\tau\geq1/4\).  The residual packet (9.239) keeps
  \(h\delta_0\) and all three Möbius signs.  The exact two-cutoff identity
  (9.240)--(9.242) splits its last sign into short--short Type I and
  long--long Type II packets without mixed or truncation errors; the
  direct prime-modulus Möbius--trace ledger is quantitatively insufficient.
  Absolute Type I retains at least the full scalar cost, (9.243)--(9.244),
  while (9.245)--(9.246) identify the balanced long--long packet as a
  near-determinant family with long variables \(k,q\asymp T^{5/2}\).
  Fourier separation followed by Bettin--Chandee still misses the target
  by at least \(T^{1/4}\), even with a free scalar sum, (9.252)--(9.254).
  The determinant solutions and reciprocal phase reduce further to the
  affine packet (9.258), while its unweighted complete core is exactly
  the Ramanujan sum (9.257).
* the exact scalar recombination (9.247)--(9.250): the two scalar signs
  combine back to \(\mu(s)\), the phase lifts from \(q=s/g\) to \(s\),
  and the scalar family becomes the divisor-incidence multiplicity
  \(\nu_{\mathcal G,\mathcal Q}(s,m)\leq\tau(s)\).  The resulting
  full-modulus incidence large-sieve estimate remains unproved.  Its
  exact LCM-pair energy is (9.251), saving the scalar half-power in the
  coefficient moment.
* the complete affine reciprocal Parseval identity (9.259), the
  boundary-exact product-residue energy majorant (9.260), and the unit-mode
  complete-period collapse (9.261)--(9.262).  These reduce the complete
  \(\delta\)-period core to an affine Mertens sum; the smooth incomplete-period
  modes remain unproved.
* the direct application audit of Wright's partially fixed denominator
  theorem after reciprocity, (9.263)--(9.266).  Its best parenthetical
  saving is \(T^{1/4}\); after direct \(B,g\) summation it has exponent
  \(83/8\), still \(11/8\) above the dispersion target.
* the exact smooth \(\delta\)-Poisson formula (9.267), its joint affine
  endpoint lattice (9.268), and the character screening
  (9.269)--(9.271).  Bombieri--Vinogradov gives no power beyond
  progression density, while the ordinary primitive-character large
  sieve saves only \(T^{1/4}\) of the required \(T^{1/2}\).
* the exact principal-density coefficient (9.272).  Its value is
  \(-1\) on every prime above the two cutoffs, ruling out a separate
  pointwise Selberg-sieve/Euler-product power saving.
* the direct Kloosterman-over-primes audit (9.273).  Irving's published
  full-interval estimate saves \(T^{3/10}\), below the required
  \(T^{1/2}\), and it has no joint product-numerator moment.
* the prime-slice Selberg-integral audit (9.274)--(9.276).  The
  unconditional variance exponent \(7\) returns the trivial exponent
  \(5\) after Cauchy; the RH-scale variance would cover the centered
  fluctuation, but the separately created density mode already asks for
  the unproved Mertens exponent \(5/6\).  Ramanujan centering does not
  cancel this distinct prime-density mode.
* the direct averaged shifted-prime map (9.277).  Lichtman's theorem
  handles the stripped signed \(\mu(s)\Lambda(s+d)\) projection, with
  endpoint cost \(T^{4+o(1)}\), but gives only logarithmic cancellation
  at power exponent \(5\); it also does not admit the shift-dependent
  inverse/product kernel.
* the transition numerator completion (9.278)--(9.282).  Poisson in
  \(h\) forces the exact dilation \(\delta_0=\ell d\), with only
  \(T^\varepsilon\) dual modes, and removes the inverse/product phase.
  The resulting three-variable weighted averaged-Chowla core still
  requires the exact relative saving \(S^{-1/6}=T^{-1/2}\).  Nonzero
  numerator-dual frequency does not remove the separate shift-major
  arcs.
* the exact transport of Ramanujan centering through that completion,
  (9.283).  It becomes a point mass minus the uniform unit-group mean.
  On a short aligned box the finite mass is
  \(U_q(D)-U_q(D)^2/\varphi(q)\), (9.284), and for prime \(q>D\) this is
  \(D-D^2/(q-1)\), (9.285).  Hence the background is exactly
  \(T^{1/2}\) smaller at the transition, (9.286), and the original
  centering supplies no universal \(d\)-major-arc vanishing identity.
* the actual-weight transition scale (9.287)--(9.288): all six
  dimensionless archimedean and Poisson frequencies have exponent zero.
  Hence integration by parts has no power reserve, the AFE Mellin zeros
  do not imply a shift-Fourier zero, and a weight-specific escape would
  require the new exact global moment identity (9.289), which remains
  unproved and would not by itself remove all rational major arcs.
* the post-completion scalar-sign recombination (9.290)--(9.291): all
  scalar-dependent weights become one divisor-incidence coefficient on
  \(s=gq\), while \(\mu(g)\mu(q)=\mu(s)\).  Its \(L^2\) norm is
  divisor-bounded, (9.292), so Lichtman's arbitrary-coefficient Fourier
  lemma matches each separated and coprimality-divisor component exactly;
  its power ledger remains \(SD=T^5\), leaving \(T^{1/2}\),
  (9.293)--(9.294).
* the product-modulus regrouping (9.295)--(9.298): the exact Type-I/II
  coefficient reconstructs \(\mu(n)\), its long--long part starts only at
  \((U+1)(V+1)\), and its finite complete-period mean is the explicit
  coprimality-twisted density prefix.  The Abelian factorization (9.299)
  cancels only after the full product family is aggregated.  Smooth
  Type-I nonzero modes and even sharp endpoint errors are below target,
  (9.300), leaving precisely (9.301); a factorwise central-arc route
  needs the fixed-power inequality (9.303), which is not supplied by the
  classical zero-free region.  The preliminary \(U=V=T^{3/4}\)
  geometry is (9.304)--(9.306); after the centered large-sieve step the
  exact endpoint \(U=V=\lfloor\sqrt D\rfloor\) separates Type I and
  Type II at \(m=D\), (9.319)--(9.322).
* the exact density/centered/complementary split (9.307).  Additive
  large sieve closes every centered low-product block, with the uniform
  bound (9.308) and exact exponent (9.309); the gcd layers scale by
  \(S_j=S/j,D_j=D/j\) and cost no power.  The transition obstruction is
  therefore reduced to the joint density plus \(m>D_j\) complementary
  divisor gate (9.310), whose quotient always has length at most \(T\).
* the squarefree complementary switch (9.311)--(9.313): nonsquarefree
  shifted arguments return to the already bounded centered term, while
  on the residual support \(\lambda(m)=\mu(m)R_{U,V}(m)\) and
  \(\mu(m)=\mu(mk)\mu(k)\).  The exact FI parameter map is (9.314);
  their parity-breaking estimate (B) is an assumption, not a theorem
  applicable here.  The remaining gate is equivalently the signed
  asymptotic-sieve bilinear form (9.315).  At the final square-root
  cutoff, fixing either long factor misses the published \(5/8\)
  threshold by the exact exponent gap \(2/3\), (9.316)--(9.322).
* the additive rational-denominator coverage ledger (9.323)--(9.327):
  Vaughan's \(X^{2/5}\) split covers a relative saving \(X^{-\eta}\)
  only for \(\eta\leq1/5\) and denominator exponent
  \(2x\eta\leq r\leq x(1-2\eta)\).  For the length-\(S\) shifted
  polynomial and the length-\(Q\) quotient polynomial, that interval
  meets the actual near-zero denominator range at only one outer
  endpoint.  It has no positive-width overlap.  On the complementary
  polytope every individual factor has length below the \(T^{5/2}\)
  minimum needed to save \(T^{1/2}\).  The remaining circle interface
  is therefore the coupled small-denominator major-arc packet, not a
  classical one-factor minor-arc estimate.
* the finite Ramanujan diagonalization (9.328)--(9.331): the
  \(r=1\) coefficient combines the density prefix with every
  complementary zero mode exactly, while
  \(C_r\ll T^\varepsilon/r\) for \(r>1\).  Discrete summation by parts
  in the smooth shift weight and two additive large sieves give
  (9.332)--(9.333), proving every nonzero reduced denominator
  \(2\leq r\leq D\) within target.  The exact residual is only the
  coupled zero/high edge form (9.334).  For \(r>D\), writing
  \(m=rv\) and \(a_{\rm R}=uv\) gives the quotient-aware identity
  \((\rho-2)+(3-\kappa-\rho)=1-\kappa\), (9.335)--(9.336), and retains
  the two long Möbius weights in (9.337).  The exact gcd-stratum
  regrouping is (9.338)--(9.339); the elementary high-edge gap is
  \(\nu=\rho-2\), (9.340)--(9.341).  Two hypothetical square roots
  cover only \(\nu\leq\lambda\), while the audited published
  convolution and monomial estimates do not cover a positive-width
  remainder, (9.342)--(9.344).  The original
  \(a_{\rm AFE}=h_0\delta_0\) remains instead in the precompletion packet
  (9.239)--(9.246).
* the precompletion dual-product circle audit (9.345)--(9.351):
  applying the exact numerator completion only after the four-Möbius
  Type-II split gives the factored determinant polynomial (9.345).
  DRZZ Lemma 4.2 applies separately to \(bc\) at frequency \(\alpha k\)
  and \(gq\) at frequency \(-\alpha\).  The quotient-gcd,
  Diophantine-loss, circle-width, and coefficient-norm ledger is
  (9.347)--(9.349).  It proves some large-gcd strata, but on every
  coprime stratum its best bound is exactly \(T^{5+\varepsilon}\),
  leaving the original \(T^{1/2}\) gap, (9.350).
* the boundary-exact $3\times2$ shifted-convolution identity
  (9.352)--(9.353), its standard-divisor proxy exponents
  (9.354)--(9.356), the exact cyclic zero-frequency factorization
  (9.357), and its sampling-invariant natural central-cell form (9.358).
  These separate a numerically covered standard $d_3$-shift error from
  two still-unproved actual-coefficient obligations: recombination of the
  Möbius singular term and the centered dyadic convolution estimate.

| Claim | Status | Complete derivation or exact status location |
|---|---|---|
| Completed AFE and diagonal extraction | verified | (2.0)--(2.10), including pole cancellation, absolute convergence, uniform weight bounds, and the diagonal parametrization |
| Shifted-divisor expansion | verified | (3.1)--(3.8), including the absolute dyadic reindexing and full smooth kernel |
| Poisson zero/nonzero-mode decomposition | verified after correction | (4.1)--(4.8); the omitted sine quotient is restored in (4.5i)--(4.6c), and the complete correction bound is (4.7c.0)--(4.7c) |
| Effective ranges and coupled-kernel normalization | verified | (5.1)--(5.15), including both nonstationary cutoffs and the exact kernel scale |
| Comparison of the three candidate gates | verified logical reduction | (6.0)--(6.8); only \({\rm(US)}\Rightarrow{\rm(IS)}\Rightarrow{\rm(CK)}\) is proved |
| Upper-bound tail outside the power-enlarged core | verified | (6.10)--(6.12), by fixed-order integration by parts depending on \(\varepsilon\) |
| Published/elementary Region A--C coverage | verified | exact inequalities and hypothesis ledger in Section 8 |
| Finite Möbius Type-I/II decomposition | verified | exact convolution identity and retained coupled sum in (9.1)--(9.7) |
| Termwise Wright route after \(s=un\) | verified insufficient | five exact savings (9.10); balanced gap (9.12) |
| Fixed-modulus Pascadi route | verified insufficient | best full-residue saving \(s^{33/191-o(1)}\); balanced gap (9.21) |
| Milićević--Qin--Wu route | verified inapplicable to the full Fourier box | top box violates \(MN\leq s^{5/4}\); (9.22)--(9.25) |
| Reverse Poisson | verified exact but tautological | returns the shifted-divisor congruence and zero-mode subtraction, (9.26) |
| One-variable Möbius inverse-phase route | verified insufficient | arbitrary composite moduli give only logarithmic saving; balanced power gap \(T^{5-o(1)}\), (9.27)--(9.30) |
| Elementary Farey large sieve | verified insufficient | uniform bound \(RS A^{1/2}T^\varepsilon\); balanced gap \(T^{5/2+\varepsilon}\), (9.31)--(9.36) |
| Two-sided Möbius decomposition | verified finite identity | both short Möbius averages and \(h\delta\) retained, (9.37)--(9.39) |
| Möbius dispersion estimate | **unproved** | sufficient mean-square gate (9.40); present pointwise gap (9.41) |
| Pascadi 2024 spectral dispersion | verified insufficient | direct scale \((RS)^{3/2}A^{1/2}\); balanced gap \(T^{11/2}\), (9.43)--(9.46) |
| Gcd--character stratification | verified finite identity; termwise routes insufficient | direct margin and exact separation (9.47)--(9.52); large-sieve gap \(T^{5/2}\), (9.53); dual \(2/3\) barrier, (9.54)--(9.55) |
| Primitive-conductor decomposition | verified finite algebra; standard character moments insufficient | cofactor Möbius sign cancels, (9.56)--(9.58); separate principal term demands the impossible uniform \(1/3\) Mertens scale, (9.59)--(9.60) |
| Unit principal spectrum | proved globally, not boxwise in \(H\) | coprime reverse Poisson gives \(RLM T^\varepsilon\leq RS T^\varepsilon\), (9.61)--(9.64) |
| Nonunit principal spectrum | exact reduction; residual Type II unproved | zero frequency returns to the LCM mode; residual lies on \(HM\asymp S\), has \(wc\asymp M\), signs \(\mu(r)\mu(u)\mu(w)\), and balanced loss \(T^2\), (9.65)--(9.74) |
| Unit nonprincipal spectrum | exact reverse completion; centered gate unproved | (9.75) gives the full Ramanujan-weighted lattice sum; its highest-divisor component is the affine binary Möbius correlation (9.79), with balanced normalized gap \(T^{5/2}\), (9.80)--(9.82) |
| Averaged Chowla on the affine family | verified applicable but insufficient | residue-class map (9.84); the published \(A_0^2\) loss is \(T\) at generic balanced slopes and the remaining cancellation is only logarithmic, (9.85)--(9.86) |
| Centered unit divisor--dual form | exact identity; two-Möbius estimate unproved | mean-zero kernel (9.88); all common modes \(v=qj\) cancel in (9.90a), leaving \(j\gtrsim M\), and delta completion further forces \(j\gtrsim L\) |
| Delta completion of the centered form | exact reduction; self-dual correlation unproved | only \(|b|\lesssim J/L\) survives, but \(br-v=zj\) parametrizes another \(\mu(r)\mu(j)\) affine family of length \(L\); balanced scales are (9.99) |
| Post-centering published coverage | verified absent on the balanced \(J\)-range | exact scale ledger (9.100); termwise completion loses \(T^{2}\) to \(T^{5/2}\), averaged Chowla has slope loss \(T\), and direct spectral dispersion loses at least \(T^5\) |
| Wright unbalanced-convolution corollary after centering | verified inapplicable | exact product/modulus map (9.103); both published modulus margins are negative throughout \(5/2\leq\jmath\leq3\), (9.104)--(9.105) |
| Centered Fourier-energy route | low-divisor face proved; remaining flatness unproved | Parseval loses exactly \(V=J/M\), so \(J/M=T^{O(\eta)}\) is covered by (9.109a); on the remaining polynomial face a separated central-arc estimate needs common Mertens exponent from \(7/11\) down to \(7/12\), (9.110) |
| All nonprincipal gcd strata | exact unified reduction; centered estimate unproved | scaled reverse Poisson (9.111) and mean-zero kernel (9.113)--(9.114); the complete residual family is (9.115), with no characterwise triangle inequality |
| Recombined residual spectrum | exact identity; joint estimate unproved | principal plus centered kernels recombine termwise in (9.117); the weakest post-reduction gate is the joint sum (9.119), not separate bounds for (9.69) and (9.115) |
| Generalized centered divisor duality | exact reduction; polynomial window unproved | all common \(v=qj(e/k)\) modes cancel in (9.121)--(9.122); the remaining equation is \(br-kv=zj\), with scales (9.126), Parseval loss \(Je/M\), and unconditional corner (9.128) |
| Nonunit Möbius sign migration | exact finite bijection; estimate unproved | \(E=e/k,\delta'=k\delta_1,f=kc\) gives \(k=(\delta',f)\) and \(\mu(e)\mu(k)=\mu(E)\), (9.130)--(9.134); after divisor duality the nonunit family retains \(\mu(r)\mu(E)\mu(j)\) |
| Blomer--Pascadi quadratic-character route | exact trace/coverage audit; direct routes insufficient | critical fixed-modulus saving \(c^{-1/32}\), but full-residue margins are negative in (9.140); Pascadi Corollary 7.9 has full-residue loss \(C^{(1+\tau)/6}\), (9.143); exact trace and character identities are (9.144)--(9.146) |
| Coherent cross-modulus fourth trace | **unproved** | candidate joint interface (9.147) must retain the common \(\mu(r)\) transform, outer \(\mu(s)\), factorized \(h\delta\), scalar-divisor strata, and discriminant energy before taking moduluswise norms |
| Fixed-numerator inverse fractions | spacing proved; generic operator route insufficient | for \(r,s,t\) in one balanced dyadic interval the exact congruence (9.148) gives spacing at least \(1/(16Y)\), (9.150); after collapsing \(h\delta\), the arbitrary-coefficient operator still loses exactly \(A^{1/2}\), (9.153)--(9.154) |
| Cross-numerator product-kernel route | unsigned central count proved; signed estimate unproved | exact factorization (9.156), Farey count \(T^{7+\varepsilon}\) in (9.160), noncentral resonance (9.162), and additive completion (9.163); termwise separation of its origin would require the \(2/3\) Mertens exponent (9.164), but Section 9.30 recombines that origin with the axes |
| Additive-dual shifted-Chowla route | exact finite reduction; joint estimate unproved | \(r=s+d\) gives the moving-endpoint identity (9.166); complete axes recombine the origin in (9.167)--(9.168), so the isolated \(2/3\) Mertens barrier is removed; all near blocks lose at most \(T^2\), one-modulus Parseval loses \(T^{5/2}\), (9.177) records the surviving resonance, (9.178) absorbs every axis boundary, and (9.179) factorizes each squarefree scalar-gcd stratum |
| Scalar-stratum unit spectrum | exact divisor decomposition; top layer unproved | unit and unrestricted lifts are (9.180)--(9.181); the double-unit sum has divisor spectrum (9.183), outer \(\mu(q)\) migrates to \(\mu(k)\) in (9.184), and (9.185) isolates the inverse-product top layer (9.186) |
| Coprimality-migrated scalar spectrum | exact Type-II bridge; balanced face unproved | expanding \((k,\delta')=1\) gives the triple spectrum (9.187), whose product coefficient is independent of the oscillatory modulus; Bettin--Chandee applies with (9.189), but (9.193) proves a uniform gap of at least \(T^2\), with gap \(T^{67/16}\) at the primitive corner |
| Centered common-divisor dispersion | exact zero-frequency reduction; nonzero dual estimate unproved | centering the full divisor packet makes the \(k=1\) layer vanish, (9.197); the cross-modulus covariance is zero for coprime moduli and otherwise factors only through \(t=(m,n)\), (9.194)--(9.196); (9.198)--(9.201) isolate the remaining dual Kloosterman frequencies and the \(t_0=Q^2/R=T^2\) transition |
| Factorwise centered Type-II tensor | exact nine-term reduction; joint estimate unproved | (9.206) has three terms and no all-principal product; applying it on both coprime Möbius moduli gives the nine-term tensor (9.207) while retaining all four signs (9.208).  On the balanced unit face, one mean saves \(T^{15/8-o(1)}\) and two save \(T^{15/4-o(1)}\), but (9.211) is only a screening ledger |
| Young varying-level primitive route | fixed scalar strata close; scalar aggregation residual unproved | numerator completion kills zero and nonunit dual modes, (9.212)--(9.213); reciprocity maps each fixed-stratum raw term to Young's additive rational large sieve, (9.214)--(9.219), saving \(T^2\).  Restoring the transition scalar sum gives exponent \(19/2\), leaving \(T^{1/2}\), (9.235)--(9.238) |
| Common-modulus unit-numerator family | closes for \(\tau\geq1/4\); small-common-factor packet unproved | the CRT collision cancels \(t\) from the Young rational, (9.221)--(9.227), but after the scalar sum its exponent is \(19/2-2\tau\).  Ramanujan marginals and the recombined zero mode remain below target, (9.228)--(9.231).  The exact residual is (9.239) for \(0\leq\tau<1/4\) |
| Scalar Möbius transition packet | exact Type-I/II and affine reduction; smooth endpoint modes unproved | (9.239) retains \(\mu(g)\mu(q)\mu(gq+d)\), the exact moving \(d\)-interval, and \(h\delta_0\); (9.241) splits \(\mu(gq+d)\) exactly into short--short and long--long divisor packets.  Absolute Type I has exponent \(\max(1/2,u+v)\), so no cutoff closes it, (9.243)--(9.244); the balanced Type II is the near determinant (9.245)--(9.246).  Affine parametrization gives (9.255)--(9.258), Parseval is (9.259), and complete \(\delta\)-periods collapse exactly to an affine Mertens sum in (9.261)--(9.262).  Direct Bettin--Chandee and Wright applications remain above target, (9.252)--(9.254) and (9.263)--(9.266); the jointly averaged smooth incomplete-period modes remain unproved |
| Affine endpoint character route | exact dual lattice; ordinary mean squares insufficient | smooth \(\delta\)-Poisson gives \(|n|\ll T^\varepsilon\) and \(h+nq=jd\), (9.267)--(9.268).  Character orthogonality is (9.269); Bombieri--Vinogradov gives no power beyond progression density, and the primitive large sieve leaves a \(T^{1/4}\) gap, (9.270).  The intermediate long-character moment (9.271) would fill the screening ledger but is unproved and does not by itself discharge the coupled smooth weights |
| Principal Type-I/II density | exact finite obstruction to separate elementary closure | the rational coefficient is (9.272), and equals \(-1\) for every prime \(p>\max(U,V)\).  Thus a pointwise Selberg-sieve/Euler-product estimate of the separated principal spectrum cannot give a power saving; phase and Möbius recombination remain necessary |
| Prime Kloosterman slice | published theorem applicable only after enlarging the moving interval; quantitatively insufficient | on \(Q=T^{5/2},x=T^3\), Irving's three exponents give \(26/5\) versus trivial \(11/2\), a saving \(3/10<1/2\), (9.273).  The actual prime interval has length \(T^2\) at height \(T^3\), and the theorem has no joint \(h\delta_0\)-moment |
| Prime-slice Selberg variance | unconditional scalar projection insufficient; RH diagnostic only | at \(X=T^3,Y=T^2\), the unconditional \(J(X,Y/X)\ll XY^2T^\varepsilon\) gives exponent \(5\) after Cauchy, still \(1/2\) above target, (9.274).  RH-scale variance would give exponent \(4\), (9.275), but the density term separately requires the unproved \(X^{5/6+\varepsilon}\) Mertens bound (9.276); the Ramanujan zero mode (9.230) is not this density mode |
| Averaged Möbius on shifted primes | stripped signed projection covered only logarithmically | \(h=Y-d,n=s+d-Y\) maps the scalar correlation to Lichtman's shift average with fixed \(G(n)=\Lambda(n+Y)\); endpoints cost \(Y^2=T^4\), but the theorem's main bound remains \(XY/(\log X)^{1/3-\delta}=T^{5-o(1)}\), leaving the full \(T^{1/2}\) power gap and excluding the actual shift-dependent inverse/product kernel, (9.277) |
| Transition numerator completion | exact three-variable reduction; weighted averaged-Chowla power gate unproved | Poisson in \(h\) gives (9.278); \(q>\delta_0+|\ell d|\) forces \(\delta_0=\ell d\), (9.279), so the inverse/product kernel disappears and only bounded dual modes of (9.280) remain.  The ledger is \(23/2-2=19/2\), still \(1/2\) above target, (9.281), equivalently the core (9.282) needs \(S^{-1/6}\).  The nonzero \(h\)-dual mode does not delete the distinct \(d\)-major arcs |
| Centering after transition completion | exact short-box obstruction; no major-arc deletion | the centered numerator transform is the point-minus-uniform identity (9.283).  Its aligned short-box mass is (9.284), equal to \(D-D^2/(q-1)\) for prime \(q>D\), so the uniform background is a factor \(D/q=T^{-1/2}\) below the dilation point mass, (9.285)--(9.286).  This disproves an automatic vanishing-moment route but is not a lower bound for the actual signed smooth packet; published averaged/short-interval Möbius bounds remain logarithmic at the required power scale |
| Actual archimedean zero-moment route | scale audit exact; special identity unproved | in the balanced transition every parameter \(TL/(MR),HM/S,M^2R/(ST),KS/(MR),gD/L,H/q\) has exponent zero, (9.287)--(9.288).  Thus the completed weight is sampled at bounded frequency and integration by parts gives no power.  The AFE zeros at Mellin \(z=\pm1/2\) do not force the proposed \(d\)-moment (9.289), and even that moment would remove only the additive origin |
| Post-completion scalar recombination | exact two-Möbius form; published average only logarithmic | (9.290)--(9.291) merge \(\mu(g)\mu(q)\) into \(\mu(s)\) and put every separated scalar weight into \(\omega_{G,Q}(s)\).  Its divisor-bounded \(L^2\) norm (9.292), together with the exact gcd-divisor split, fits Lichtman's arbitrary-coefficient Fourier lemma componentwise.  The resulting bound has power exponent \(SD=T^5\), not the target \(S^{3/2}=T^{9/2}\), (9.293)--(9.294); no third independent Möbius sign remains |
| Central Type-I/II density prefix | exact square-root split; parity-breaking bilinear gate unproved | (9.295)--(9.298) identify the product coefficient and finite density prefix; (9.299) gives only Abelian cancellation.  The exact split and additive large sieve (9.307)--(9.309) remove every centered low-product block.  Nonsquarefree complementary terms reduce to that bound; on squarefree support (9.311)--(9.313) maps the residual to the FI boundary (9.314), whose bilinear axiom is assumed rather than proved.  The endpoint \(U=V=\lfloor\sqrt D\rfloor\) makes \(m\leq D\) pure Type I and \(m>D\) pure Type II, (9.319)--(9.320), leaving \(\beta,\gamma\geq1,\kappa\leq1\), (9.321).  Fixing either long factor misses the \(5/8\) theorem by \(2/3\), (9.322), so the joint gate (9.315) remains essential |
| Additive Vinogradov circle route | exact denominator coverage; no positive-width overlap | The explicit rational-approximation bound is (9.323), and a relative saving \(X^{-\eta}\) is available only on (9.324).  The direct length-\(S\) polynomial and the fixed-\(g\), length-\(Q\) polynomial each meet their actual near-zero denominator interval at one endpoint only, (9.325)--(9.326).  A single complementary factor would need length at least \(T^{5/2}\), (9.327), while (9.321) gives at most \(T^2,T^2,T\).  Recent almost-all Möbius Fourier uniformity remains logarithmic, so the coupled major-arc gate is still unproved |
| Density/complement Ramanujan spectrum | exact middle-spectrum closure; quotient-aware zero/high edge pair unproved | The finite coefficients and reconstruction are (9.328)--(9.331), with \(C_r\ll T^\varepsilon/r\).  Summation by parts plus the additive large sieve proves all \(2\leq r\leq D\), with exact exponent (9.333).  The weaker residual gate is (9.334): the combined \(r=1\) mode plus \(r>D\) small numerators.  On \(m=T^{3-\kappa}=rv\), lifting to \(a_{\rm R}=uv\) gives \(\nu+\lambda=1-\kappa\), not a constant \(1\), (9.335)--(9.337).  The finite bijection (9.338)--(9.339) shows \(u,v\) are gcd strata of one numerator.  The elementary gap is \(\nu\); two hypothetical square roots cover only \(\nu\leq\lambda\).  DRZZ is resonant on \(r\mid bc\), while the Robert--Sargos/Fouvry--Iwaniec monomial shapes cap at one half-power, so neither closes a positive-width residual, (9.340)--(9.344) |
| Precompletion dual-product Type II | exact published coverage polytope; dominant coprime stratum unproved | Starting from the four-Möbius packet retaining \(h\delta_0\), exact numerator completion produces (9.345), whose circle transform factors into the \(bc\) and \(gq\) product polynomials.  DRZZ Lemma 4.2 is applicable here.  Equations (9.347)--(9.349) include the reduced denominator after \((k,q_\alpha)=T^{\tau_k}\), the approximation loss \((\kappa-2\tau_k)_+\), circle-band mass, and the competing Cauchy bound.  Some high-gcd strata satisfy the target, but for every \(\tau_k=0\) box the optimum is exactly exponent \(5\), leaving \(1/2\), (9.350).  Hence the postcompletion resonance is not the only obstruction |
| Coprime $3\times2$ shifted convolution | exact finite reduction and published proxy exponents; actual main/error pair unproved | (9.353) is the finite correlation of a dyadic three-factor Möbius convolution with a dyadic two-factor one.  Topacogullari's fixed-shift standard $d_3$--$d$ error sums to exponent $9/2+7/64$, while the Baier--Browning--Marasingha--Zhao signed $d_3$--$d_3$ first moment has exponent $17/4$.  Neither theorem accepts the coefficients (9.352).  The natural central cell (9.358), not one resampling-dependent zero point, has raw exponent $5$ and needs the invariant half-power; hence the weaker actual interface still requires both singular-cell recombination and a centered coefficient-transfer estimate |
| Precompletion $\zeta$--mollifier pairing | exact two-product-variable reduction; compact twisted coefficient family unproved | Pairing $x=nd,y=me$ on the initial AFE line gives (9.361) with the truncated coefficients $B_{N,z}$.  At $z=0$, (9.362)--(9.363) are exactly von Mangoldt plus a reflected cofactor shorter than $T^{1/2+\varepsilon}$ on the balanced transition.  But the actual compact Mellin family contains every $B_{N,i\tau}$; (9.364) shows that nonzero bounded $\tau$ restores arbitrary many-prime support.  Moving the reindexed long energy to a left line is not absolutely convergent, so the prime slice alone is not the full gate |
| Short-modulus zero-frequency recombination | complete aggregate identified; fixed balanced weight still unproved | Only after summing the full \(h,\delta\) dyadic partitions does Fourier inversion give the continuous \(m_1=m_2\) condition (9.380)--(9.383).  Summing gcd strata gives the literal square (9.384), minus the explicit \(r=s\) diagonal.  A fixed balanced box has Fourier width \(S/H\asymp M\), so it is not a point mass and no converse from its actual weight to \({\rm MS}_{2/3}\) is claimed.  The identified alternative is a uniform shifted-energy theorem for the full compact family \(B_{N,i\tau}\), not merely its prime-supported \(\tau=0\) slice |
| Compact-Mellin density centering | exact pole cancellation and finite boundary; diagonal-sized correlation unproved | The generating series is (9.388), and subtracting \(\beta_N(z)\) cancels its \(w=1\) pole in (9.389).  For every finite product cutoff, (9.390) shows that the entire moving edge remains; at \(w=1\) it is the whole centered prefix.  On the transition \(X=T^{7/2},H=X/T\), convexity cancels the contour gain exactly, (9.391).  Goldston--Gonek requires the same coefficient correlations as input, and the Conrey--Keating divisor Type II framework does not apply to the inverse Möbius coefficient.  The precise sufficient replacement \({\rm CME}_3\), (9.392), needs the full \(H=T^{5/2}\) diagonal saving and is unproved |
| Compact-Mellin \(L^2\) route | exact finite Fourier identity; standard mean values circular | The Gaussian identity (9.394) localizes the product polynomial to \(|m-n|\ll X/T\), (9.395), with the same-\(z\) bilinear coefficients from (9.361).  Cauchy asks for the \(L^2\) norm of that same length-\(X\) polynomial.  Opening \(B_{N,z}\) returns the original zeta--mollifier product chunk, while Montgomery--Vaughan has the long term \(X\sum|c_n|^2\), losing exactly \(X/T=T^{5/2}\).  Goldston--Gonek replaces the loss only after assuming the coefficient correlations on the right side, so no standard mean-square theorem proves \({\rm CME}_3\) |
| Balanced short-shift integer lattice | exact equal-index forcing; banded two-Möbius estimate unproved | Under the literal endpoint condition \(S/2>2L+4MD\), (9.396)--(9.399) force every original solution to have \(m_1=m_2=m\) and \(\delta=-m(r-s)\).  On this divisibility slice the retained product is \(h\delta=-hm(r-s)\) and the inverse phase is exactly \(e_s(hm)\), (9.400), with critical scale \(HM/S=T^{o(1)}\).  Formula (9.402) is the exact post-Poisson subpacket.  A fixed \(h\)-box also contains a complementary continuous-\(x\) packet which cancels only after full Poisson inversion; hence the result removes the prospective shift oscillation and extra zeta-index average, but does not prove the remaining \(T^2\) two-Möbius saving |
| Coupled compact-Mellin integral | exact finite recombination; no independent power saving | Keeping \(\tau\) before absolute values is formally weaker than \({\rm CME}_3\), but (9.403)--(9.404) show that the single common mode cancels both mollifier twists and leaves only \((nm)^{-i\tau}\).  The actual contour reconstructs \(V_t(nm)\), (9.405), hence the original conditions \(y-x=\Delta\) and \(nm\asymp T\), (9.406).  It supplies neither two divisor orthogonalities nor an equal-divisor condition; the finite Laurent identity is (9.407).  Any gain must therefore use this product constraint jointly with the shift and both Möbius signs |
| Guth--Maynard large-value route | exact Fourier-cell audit; long range reduces to classical | The separated equal-index model is the exact energy (9.409), whose time window resolves \(|r-s|\ll X/T\), (9.410).  At \(X=T^3\), each cell contains \(X/T=T^2\) coefficients.  Montgomery--Vaughan gives normalized exponent \(3\) against diagonal exponent \(1\), (9.412).  Guth--Maynard's proof explicitly returns to the classical first term for polynomial length \(N_{\rm GM}\geq T_{\rm GM}\); here \(N_{\rm GM}=T^3>T=T_{\rm GM}\).  Their theorem is coefficient-agnostic and provides no Möbius-specific saving, so (9.413) remains exactly the unavailable banded two-Möbius estimate |
| Intact-mollifier Perron route | unconditional possible-zero estimate unproved; RH route closes | Perron inversion has no endpoint or truncation error, (9.422)--(9.424).  On the limiting absolute-convergence contour \(c=1/2\), squaring \(N^c\) gives exponent \(4\) at \(N=T^3\), three powers above target, (9.425).  Reaching \(T^{1+\varepsilon}\) unconditionally enters a region where off-critical zeros are not excluded, and any simple-zero residue encountered contains \(1/\zeta'(\rho)\), (9.426).  Under RH the shift to fixed \(c>0\) is pole-free; Bui--Florea's \(k=2\) fourth negative moment plus the classical fourth moment yields (9.432), which closes every fixed \(\theta\), including \(3\), conditionally on RH |
| Bettin--Gonek long-mollifier converse | exact theorem map; no dyadic \(\theta=3\) zero-free obstruction | Uniform \(T^{1+\varepsilon}\) control for every \(N\leq T^\theta\) on \([0,T]\) excludes zeros right of \(1/2+1/(2\theta)\), while on \([T,2T]\) it excludes only those right of \(1/2+2/\theta\), (9.434).  At \(\theta=3\) the dyadic boundary is \(7/6\), hence vacuous; a nontrivial dyadic consequence starts only at \(\theta>4\).  Their model (9.436) shows a \(T^{-3}\) displacement factor for one fixed off-line zero, but is not an unconditional all-zero upper bound |
| Secondary-zero boundary master | exact finite schema; analytic packet adapter and estimate unproved | For every supplied labelled AFE/\(h,\delta\)/dyadic packet family, (9.437)--(9.448) retain both reflected cross terms, the diagonal, and all finite endpoints before absolute values.  Double centering gives weighted zero row and column sums, but changing the density changes the separate \(\mathcal M_{\rm res}\) and \(\mathcal R_{\rm cent}\).  The helper does not yet derive an exhaustive packet family from (4.5); the actual principal object is identified by the later Fourier-projector row, whose banded energy remains open |
| Global centered \(TT^*\) route | exact determinant split; both analytic estimates unproved | The balanced operator needs a relative \(T^2\) saving, or \(T^4\) after squaring, (9.449)--(9.450).  One global Gram expansion splits exactly by \(k_u\ell_v-k_v\ell_u=0\) or not, (9.451)--(9.454).  The zero determinant must be bounded using the same reflection data as the pre-Cauchy resonant master, but the two are not literally added; only the nonzero determinant is eligible for a spectral large sieve.  None of the three tasks in (9.455) is asserted |
| Actual zero-mode Fourier projector | exact high-rank identification; banded Möbius energy unproved | The fully recombined equal-index packet is the Fourier Gram (9.457), minus its explicit diagonal (9.458).  On the Gaussian \(1,2,4\) minor, both determinants in (9.462) are nonzero, so the full and diagonal-removed projectors have rank \(3\); every product-density row/column/grand projection has rank at most \(2\), (9.463).  Hence scalar-density centering cannot isolate the whole resonance, and the remaining projector is the long-polynomial gate rather than an LCM diagonal |
| Determinant-zero primitive slopes | exact same-slope decomposition; within-slope norm unproved | Since every affine slope \((k_0,\ell_0)\) is positive and primitive, determinant zero forces equality of the two slopes, (9.465)--(9.466).  The zero orbit is therefore the sum of same-slope squared norms (9.467), with no cross-slope collisions.  All \(g,h,\delta,\nu,\sigma\) signs remain inside each square, and the bound (9.468) is still open |
| Label-safe Type-entry determinant | internal zero orbit recombined; nonzero entry determinant unproved | The auxiliary sector character is \(\xi\), not \(a_{\rm AFE}=h\delta\), and all original packet labels remain in the row, (9.469)--(9.471).  A common Beatty sector is one common Euclidean quotient and obeys \(Q\Delta_{\rm Type}=\rho_1s_2-\rho_2s_1\), (9.472)--(9.477).  All \(dm=r\) cross factorizations must be recombined by the Möbius-log identity (9.478)--(9.481).  This makes the nonprincipal \(\Delta_{\rm Type}=0\) part exactly \((1-M^{-1})D_{\rm cont}\), already at diagonal power, (9.482); the extra power is confined to \(\Delta_{\rm Type}\ne0\), which is not estimated |
| Moving-Beatty fixed-function and labelled Type split | structured slope sampling proved; exact centered positive projector isolated; moving-grid Hilbert square unproved | The collision (9.483)--(9.484) shows that one value \(r=7\) receives opposite two-Möbius coefficients at two moving slopes, so the published fixed-\(f\) metric theorem cannot directly encode the packet.  Equations (9.485)--(9.487) instead split the true nonprincipal labelled Gram into all I/I, I/II, II/I, II/II and \(\Delta=0/\ne0\) blocks while retaining \(h\delta\).  The zero blocks recombine, and (9.489) makes the complete packet an exact projector square.  Therefore only the one-sided joint upper gate \({\rm JNT}_{2}^{+}\), (9.491), is needed after the diagonal estimate.  Reindexing by \(n=rs\) further gives one fixed \(\mu(n)\) and an \(O(1)\) product-sector fiber, (9.494)--(9.497), but the vector weight remains factorization-dependent.  The Sobolev/divisor argument (9.498)--(9.503) proves \(T^\varepsilon\)-loss sampling on the reciprocal grid for every fixed Hilbert family.  Finally, (9.504)--(9.508) identify the exact centered positive moving-Beatty projector sufficient for the signed one-sided gate; it still needs one power of energy saving, and the exhaustive packet map remains unproved |
| Primitive Beatty Fourier boundary | exact half-jump closure; continuous Type spectrum unproved | The exact sector-step expansion (9.510)--(9.512) has harmonics \(a=\xi+jQ\) and a half-jump term.  On primitive entries the boundary condition is equivalent to \(s\mid Q\), and (9.513)--(9.515) give a bijection with the \(Q\) sectors.  After label recombination the centered boundary is bounded by the known continuous diagonal.  The continuous harmonics retain both Möbius factors and the full \(h\delta\) labels through the phase \(e(adp/s)\), but standard additive large sieve still loses one energy power by (9.516) |
| Sector--AFE Kloosterman Type polytope | exact combined phase and published prime-slice coverage; composite central band unproved | Recombining before absolute values gives \(e_s(\alpha dp-h\delta\bar d\bar p)\), (9.517), and the unit condition is exactly \((\alpha h\delta,s)=1\), (9.519).  For \(d=T^u,s=T^\sigma\), Korolev covers the composite-modulus left wing with saving at most \(\sigma/35\); the FKM one-variable prime rows give \(\sigma/24\).  FKM Theorem 1.17 applies bilinearly at fixed prime modulus, saving at most \(\sigma/8\) but zero at \(u=\sigma/2\).  The exact completion (9.526)--(9.529) has one fixed Kloosterman argument and Cauchy--Parseval returns the trivial scale, so the recent complete-Kloosterman bilinear theorems do not directly fit.  The apparent FKMS rank-one \(1/224\) substitution is also invalid: the equal-shift constant-phase family has dimension \(4m-1>3m\), (9.530)--(9.533), so the required Type-II moment count fails.  All inputs remain below the critical half-power and provide no joint \(s,\xi,h\delta\) moment.  The prime balanced slice, composite central band, and full coupled Type-II gate remain unproved, (9.520)--(9.535) |
| Squarefree CRT prime-factor transfer | exact factorization and sharp pointwise cofactor cost; coupled character average unproved | For \(s=qr\), (9.536)--(9.539) factor the product trace and separate the cofactor by multiplicative characters while retaining \(\mu(s)\mu(d)\) and \(h\delta\).  A prime bound saving \(q^{-\kappa}\) pays the unavoidable coefficient-independent cost \(r^{1/2}\), so a power remains only for \(\lambda>\sigma/(1+2\kappa)\), (9.541).  Even the optimistic registered \(\kappa=1/8\) requires a prime factor larger than \(s^{4/5}\), gives only \(1/16\) at \(q=s^{9/10}\), and never reaches the required half-power.  Eliminating the \(r^{1/2}\) loss requires a new global character square-function before Cauchy, not a fixed-prime theorem, (9.540)--(9.542) |
| Rank-one Type-II resonance subtraction | exact classification and centered square-root bound; signed resonant projector unproved | The partial fractions (9.543)--(9.546) classify every constant phase by one global linear equation and one reciprocal-residue equation per equal-shift block.  Its nonpole value is explicit, (9.547), and subtracting it leaves a standard Weil square-root sum, (9.548).  Every admissible partition has resonant dimension at least \(4m-1\), so the positive FKMS moment exceeds its \(3m\) allowance by \(m-1\), (9.549).  The remaining \(\operatorname{RSCCG}_3\) must retain \(\mu(qr)\mu(d)\), \(h\delta\), all characters, and all packet labels before Hölder; neither that signed resonant estimate nor the exhaustive implication to \(\operatorname{CK}_{\rm ub}(3)\) is proved |
| Resonant-projector dual split | exact principal/centered decomposition; both global estimates unproved | Additive orthogonality on \(L\) and every block residue \(R(\rho)\) gives the product formula (9.552)--(9.554) without taking absolute values.  The zero dual frequency is the explicit product of total-mass products minus local \(a=b\) diagonals, (9.555); it must be recombined across AFE directions, reflection, the explicit diagonal, \(h,\delta\), and dyadic scales.  Every remaining mode has a genuine nonzero \((\lambda,\eta_\rho)\), (9.556), but its squarefree CRT character operator still needs a global pre-Cauchy estimate |
| Pre-Poisson product-incidence orthogonality | exact equal-outer-label Fourier bound with half-power numerical capacity; full Gram estimate unproved | After the cofactor character square imposes \(x_1\equiv x_2\pmod r\), the equal-\((h,\delta)\) inverse cross phase has reduced conductor \(Q=q/(x_1-x_2,q)\), while the same pair collides modulo \(s/Q\), (9.557)--(9.560).  Grouping \(h,\delta\) modulo \(Q\) gives the exact Fourier-operator bound (9.561)--(9.562).  On the original \(s=T^3,H=L=T^{5/2}\) box, every \(T\leq Q\leq T^3\) has at least half-power numerical capacity, (9.563).  This acts before \(h\)-Poisson and is an alternative ordering of (9.493), not an extra post-Poisson gain.  Closing the route still requires the unequal-label Gram estimate (9.566), a joint count for \(Q<T\), a \(T^\varepsilon\)-cost smooth adapter, compatibility with the preceding reductions, and an exhaustive global packet map |
| Full unequal-label CRT character Gram | exact Kloosterman collapse and coefficient-principal classification; global operator bound unproved | Keeping every \(a=h\delta\) label inside one character Cauchy step gives (9.564)--(9.566), with no pointwise \(\varphi(r)^{1/2}\) multiplier cost.  Character orthogonality collapses the full square to the cofactor trace \(\mathcal C_r(a_1,a_2;y)\), (9.567).  Its exact coefficient-principal set is \(y=1,\ a_1\equiv a_2\pmod r\), where the kernel equals \(\varphi(r)\), (9.568); this includes distinct outer product labels.  For composite \(r\), the complement still contains local-principal finite aliases, so no uniform pointwise square-root claim is made.  The principal mode needs global AFE/reflection/diagonal reassembly, while the coefficient-nonprincipal trace must be estimated jointly with the \(q\)-phase, both Möbius weights, and all packets |
| Cofactor Kloosterman conductor stratification | exact prime-factor split and local square-root bound; conductor average superseded by the outer-label operator | With \(g=(B(y-1),a_2-a_1\bar y,r)\) and \(R_0=r/g\), CRT gives the exact prime product (9.570).  Principal primes contribute \(p-1\), one-zero primes contribute \(-1\), and the remaining primes satisfy the classical \(2\sqrt p\) bound.  Hence (9.571) gives \(|\mathcal C_r|\ll_\varepsilon\varphi(g)R_0^{1/2+\varepsilon}\), including all \(2,3\)-adic aliases.  Low conductor forces \(y=1\) and \(a_1=a_2\) modulo the large divisor \(g\), (9.572).  Sections 9.85--9.88 replace pointwise conductor summation by an exact outer-label Fourier operator and close its standalone smooth archimedean product spectrum; the joint arithmetic embedding remains open |
| Exact cofactor outer-label Fourier operator | exact partial isometry and alias cancellation; joint arithmetic product-spectrum embedding unproved | The complete matrix \(C_y(a,b)\) maps a unit additive frequency to a phase times the permuted frequency \(\bar yk\), with singular value exactly \(r\), and annihilates every nonunit frequency, (9.573)--(9.575).  Thus all row and column sums vanish and principal/full-amplitude composite aliases cancel before absolute values.  The sharp bound (9.576) depends only on the primitive projection of the \(a=h\delta\) residue arrays.  Its exact energy is (9.577); elementary Cauchy--Parseval gives (9.578)--(9.579), which is one half-power too large at \(H=L=T^{5/2},r=T^3\).  Sections 9.86--9.88 close all gcd strata and the smooth archimedean adapter at exponent \(5+\varepsilon\).  The same \(q\)-phase, two Möbius weights, reflection, and global packet map remain outside that standalone estimate |
| Unit-label primitive product spectrum | published composite-modulus fourth moment closes the unit sharp-interval subpacket | Multiplicative Plancherel gives the exact Gauss-weighted character formula (9.580).  Cochrane--Shi Theorem 1 supplies the arbitrary-translated-interval fourth moment (9.581), and squarefree Gauss bounds yield (9.582).  On \(H=L=T^{5/2},r=T^3\), the nonprincipal and principal exponents are \(5\) and \(4\), both below the \(T^7\) product-density scale.  Section 9.87 extends this through every nonunit gcd stratum |
| Nonunit primitive product gcd descent | exact reduced conductor and published sharp-interval closure; archimedean adapter handled next | With \(d=(h,r),e=(\delta,r),w=[d,e]\), the phase descends exactly to modulus \(R=r/w\), and \(U(r)\to U(R)\) has \(\varphi(w)\) lifts, (9.583)--(9.584).  Every \(R>1\) term returns to Cochrane--Shi after finite Möbius inversion.  The \(R=1\) locus is exactly \(r\mid h\delta\) and has mass (9.585).  Thus (9.586) bounds every separated sharp-interval stratum by exponent \(5\) at the balanced face.  Section 9.88 supplies the smooth archimedean adapter; compatibility with the joint \(q\)-phase, two Möbius weights, reflection, and exhaustive packet map remains unproved |
| Smooth archimedean product-spectrum adapter | bounded projective cost proved; joint arithmetic packet unproved | The four-variable Fourier expansion (9.587) has variation-weighted projective norm \(\ll\mathscr L^{C_s}\) by Sobolev--Parseval, (9.588).  Abel summation plus a dyadic maximal fourth-moment argument extends Cochrane--Shi to separated bounded-variation factors, (9.589)--(9.590).  Hence the actual smooth archimedean core weight preserves the all-gcd exponent \(5+\varepsilon\).  The same \(q\)-phase, two Möbius weights, reflection, and exhaustive global packet map are not consequences of this separation and remain unproved |
| Fixed-modulus ratio-frequency/character square | exact inner-block diagonalization and Type determinant; cross-modulus two-Möbius estimate unproved | Taking the full squarefree modulus as cofactor rewrites the fixed-\(s\) unequal-label Gram as the positive ratio-frequency square (9.591).  On each smooth rank-one tensor, multiplicative Parseval gives (9.592), while the Type product transform factors as two Dirichlet polynomials, (9.593).  Opening the square and applying the remainder-free split (9.241) gives (9.595), retaining \(a=h\delta\) and the Type Möbius sign.  The fixed-modulus square necessarily removes the outer \(\mu(s)\); the required next object is its cross-modulus \((s_1,s_2)\) analogue formed before Cauchy, with both outer signs retained |
| Global linear two-Möbius character master | exact pre-Cauchy Type I/II form; cross-modulus dispersion unproved | Applying multiplicative inversion linearly before the \(s\)-sum gives (9.596)--(9.597): \(\mu(s)\), \(\mu(d)\), the complete character family, and \(a=h\delta\) all remain in one finite sum.  The boundary-safe identity (9.598)--(9.599) splits only \(\mu(d)\), retains \(d\leq\max(U_0,V_0)\), and has no mixed rectangles or remainder.  A single subsequent global square has the signed cross-modulus kernel (9.600).  Published separate character moments do not bound the product of its trace, Type, and companion polynomials at the balanced face |
| Cross-modulus zero product frequency | exact same-\((s,t)\) diagonal; signed complement unproved | The primitive frequency \(\bar t_s/s\) is a reduced fraction.  Hence equality across two blocks forces \(s_1=s_2,t_1=t_2\), and every distinct pair has Farey spacing at least \((s_1s_2)^{-1}\), (9.601)--(9.603).  The ordinary additive large sieve (9.604) and the sum of fixed-modulus Cochrane--Shi energies both have balanced exponent \(11\), so spacing alone gives no new power.  The zero projector is classified, but its AFE/Type reassembly and the signed nonzero-frequency cross-modulus estimate remain unproved |
| Cross-modulus frequency Euler centering | exact local density and mean-zero divisor expansion; weighted lift handled next | For \(s_i=gr_i\), CRT gives the exact multiplicity (9.606) of every circular numerator \(\kappa\).  The common Möbius sign cancels as \(\mu(s_1)\mu(s_2)=\mu(r_1)\mu(r_2)\), while (9.608)--(9.610) split the multiplicity into the explicit density \(\varphi(s_1)\varphi(s_2)/[s_1,s_2]\) and Euler blocks containing a mean-zero factor \(1_{p\mid\kappa}-1/p\).  Section 9.93 lifts this to arbitrary fixed-pair packet weights; the signed estimate for the resulting centered blocks remains unproved |
| Weighted CRT packet centering | exact orthogonal projection; principal reassembly and centered dispersion unproved | Conditional expectations in the prime CRT coordinates give the Hoeffding decomposition (9.612)--(9.615) for an arbitrary fixed-\((s_1,s_2)\) packet.  The weighted fibre identity (9.616) separates \(\bar W\varphi(s_1)\varphi(s_2)/[s_1,s_2]\) from two terms whose total \(\kappa\)-mass is exactly zero.  Linearity (9.618) retains \(h\delta\), both Type Möbius weights, the outer cofactor signs, and all nine ordered Type blocks at divisor cost \(T^\varepsilon\).  Zero marginals do not themselves give power cancellation; the AFE/reflection principal ledger and the global signed norm of the centered blocks remain open |
| Principal-density normalization | exact no-gain audit for the bare global square | A single \(\kappa\)-fibre contributes the reciprocal-LCM density (9.620), but the unnormalized sum over all \([s_1,s_2]\) residues cancels that denominator exactly, (9.621).  Hence the bare master returns \(|\sum_s\mu(s)Z_s^{\rm tot}|^2\), not the totient-square form (9.623).  Any useful reciprocal-LCM normalization must be exhibited by the complete physical AFE/\(TT^*\) multiplier; it is not a consequence of centering, and no such packet-exhaustive multiplier has yet been proved |
| Divisor-incidence scalar recombination | exact finite identity and energy; incidence large sieve unproved | \(s=gq,m=g\delta_0\) gives (9.247)--(9.249), replacing the apparent third scalar sign by \(\mu(s)\) and \(\nu_{\mathcal G,\mathcal Q}(s,m)\leq\tau(s)\).  The exact energy (9.251) is \(\ll(L/G+1)\tau(s)^2\), but the equivalent full-modulus gate (9.250) must exploit it while the conductor lifts from \(q\) to \(s\) |
| Nonunit numerator completion | exact reduced-modulus identity; shorter-interval recombination unproved | (9.232) forces \((\ell,q)=(\delta,q)\) and replaces the nonunit multiplier by a centered point mass modulo \(q/(\delta,q)\).  The original ambient unit coordinates factor as \(c_w(k)/w\), (9.233), and gcd selection is paid by the restricted numerator count, (9.234).  Primitive nonunit strata cost no power; polynomial quotient-dual rows from shorter numerator intervals remain to be integrated with the smooth box decomposition |
| Coupled-kernel estimate CK\(_{\rm ub}(3)\) | **unproved** | weakest sufficient upper-bound gate, stated in Section 6.3 |
| Averaged Möbius Type-II estimate | **unproved** | explicit residual statement (9.13) |
| Global remainder upper bound | **conditional** | CK\(_{\rm ub}(3)\) implies it by (6.13) |

* CK\(_{\rm ub}(3)\), the accepted weakest upper-bound gate;
* the averaged Möbius Type-II estimate (9.13);
* the unconditional \(T^3\) long-mollifier upper bound;
* separately, CK\(_{1/1000}\) and TAIL\(_{B,D}\) for an asymptotic.

Thus the tail obstruction in the polylogarithmic asymptotic setup is not an
obstruction to the stated \(O(T^{1+\varepsilon})\) goal. That goal remains
blocked only at the residual coupled Region-D estimate. Treating this
estimate as a consequence of Bettin--Chandee or Wright would be incorrect.

## 11. Primary references

* M. Technau, A. Zafeiropoulos, *Metric results on summatory arithmetic
  functions on Beatty sets*, arXiv:1907.06050, Theorem 2.1 and Corollary
  4.4; Section 9.74 records the exact fixed-function collision preventing
  its scalar continuous-slope estimate from representing the moving
  two-Möbius packet.
* D. Crnčević, F. Hernández, K. Rizk, K. Sereesuchart, R. Tao,
  *On the multiplicative independence between \(n\) and
  \(\lfloor\alpha n\rfloor\)*, arXiv:2211.15830v4, Theorem B; its
  fixed-irrational qualitative logarithmic Liouville correlation is
  compared with (9.508) in Section 9.75.
* J. Teräväinen, A. Walker, *On a Bohr set analogue of Chowla's
  conjecture*, arXiv:2303.12574v1, Theorem 1.2; it subsumes the preceding
  fixed-slope result and classifies fixed rational-ratio resonances, but
  supplies neither a moving-grid power rate nor the Hilbert packet square
  in (9.508).
* F. P. Boca, M. Siskaki, *A note on the pair correlation of Farey
  fractions*, arXiv:2109.12744; used in Section 9.29 only as published
  context for the unsigned determinant count.
* P. Humphries, *Distributing Points on the Torus via Modular Inverses*,
  arXiv:2003.09955, Q. J. Math. 73 (2022), 1--16; its fixed-modulus
  inverse graph is compared with the varying-modulus family in
  Section 9.29.
* J. Bourgain, M. Z. Garaev, *Kloosterman sums in residue rings*,
  arXiv:1309.1124, and *Sumsets of reciprocals in prime fields and
  multilinear Kloosterman sums*, arXiv:1211.4184; both are fixed-ring
  reciprocal-set results and do not supply the signed varying-modulus
  estimate in Section 9.29.
* I. D. Shkredov, *Modular hyperbolas and bilinear forms of Kloosterman
  sums*, arXiv:1905.00291; its fixed-prime-field incidence setting is
  recorded in the Section 9.29 applicability audit.
* T. Cochrane, S. Shi, *The congruence \(x_1x_2\equiv x_3x_4\pmod m\)
  and mean values of character sums*, J. Number Theory 130 (2010),
  767--785, Theorem 1 and Lemma 1; Section 9.86 combines its
  arbitrary-translated-interval fourth moment with the squarefree
  induced-character Gauss formula to prove (9.582) on the unit-label
  subpacket.
* A. J. Irving, *Average Bounds for Kloosterman Sums Over Primes*,
  arXiv:1301.6372, Theorem 1; the \(B=1\) prime-slice exponents and its
  moving-short-interval mismatch are audited in Section 9.40.
* A. Languasco, A. Perelli, A. Zaccagnini, *An extension of the pair
  correlation conjecture and applications*, arXiv:1603.02952, Section 2;
  its unconditional and RH Selberg-integral scales are audited in
  Section 9.41.
* J. D. Lichtman, *Averages of the Möbius function on shifted primes*,
  Q. J. Math. 73 (2022), 729--757, arXiv:2009.08969v2, especially
  Theorems 1.3 and 6.2; mapped to the stripped signed prime projection
  in Section 9.42.
* B. Cha, D. H. Kim, *On the Vinogradov bound by the Diophantine type*,
  arXiv:2504.06726, especially the Vaughan decomposition and the
  displayed Type-I/Type-II bounds in Proposition 4; specialized to the
  exact denominator coverage interval (9.323)--(9.327).
* K. Matomäki, M. Radziwiłł, X. Shao, T. Tao, J. Teräväinen,
  *Higher uniformity of arithmetic functions in short intervals II.
  Almost all intervals*, Invent. Math. 244 (2026), 967--1091,
  Corollary 1.2(i) and the Type-II discussion; Section 9.50 records that
  the Möbius saving is logarithmic whereas the fixed-power statements
  concern divisor-function coefficients.
* W. D. Banks, I. E. Shparlinski, *Multiple sums with the Möbius
  function*, arXiv:2506.08787, Theorems 2.1 and 2.4; Section 9.51
  records the mismatch between its additive three-variable,
  logarithmic-cancellation framework and the product-modulus
  zero/high edge pair (9.334)--(9.337).
* A. Dong, N. Robles, A. Zaharescu, D. Zeindler, *Exponential sums
  twisted by general arithmetic functions*, arXiv:2412.20101,
  Theorem 1.6 and Lemma 4.2; Section 9.52 records both the quantitative
  \(\min(\rho/4,(3-\kappa)/7,\lambda/4)\) proxy and the decisive
  resonance \(e(u\,bc/r)=1\) on the selected support \(r\mid bc\);
  Section 9.53 applies Lemma 4.2 before that selection to both product
  polynomials and records the exact remaining coprime half-power gap.
* P. Srivastav, *Log-free bounds on exponential sums over primes*,
  arXiv:2505.07803v2, Theorem 1; its Möbius estimate with the \(0/1\)
  central-major-arc approximation is audited in Section 9.53.  The two
  available \(\delta_\alpha^{1/2}\) savings remain a factor
  \(T^{1/2}\) short of the coupled circle-band target.
* O. Robert, P. Sargos, *Three-dimensional exponential sums with
  monomials*, J. Reine Angew. Math. 2006, 1--20,
  DOI 10.1515/crelle.2006.012; É. Fouvry, H. Iwaniec, *Exponential sums
  with monomials*, J. Number Theory 33 (1989), 311--333,
  DOI 10.1016/0022-314X(89)90067-X.  Their arbitrary-coefficient
  monomial-sum shapes and \(X^{-1/2}\) terms are audited at the
  quotient-aware phase scale \(X=S/D=T\) in Section 9.52.  J. Pliego,
  arXiv:2211.02096, Theorem 3, is used only as an accessible restatement
  of the Robert--Sargos estimate, not as a stronger input.
* J. Friedlander, H. Iwaniec, *Asymptotic sieve for primes*, Ann. of
  Math. 148 (1998), 1041--1065, arXiv:math/9811186, especially
  hypotheses (B), (B1)--(B3); Section 9.48 maps the complementary
  divisor scales exactly and records that (B) is an input axiom, not a
  theorem available for the signed sequence here.
* M. Z. Garaev, I. E. Shparlinski, *On the distribution of modular
  inverses from short intervals*, arXiv:2304.07953; the lower-bound
  examples rule out assuming a uniform one-variable inverse-sum power
  saving.
* S. Bettin, V. Chandee, M. Radziwiłł, *The mean square of the product of
  the Riemann zeta function with Dirichlet polynomials*, arXiv:1411.7764,
  especially Proposition 1 and Sections 3.1--3.4.
* S. Bettin, V. Chandee, *Trilinear forms with Kloosterman fractions*,
  arXiv:1502.00769, Theorem 1 and equation (7.2), used in Section 8.1.
* M. P. Young, *The large sieve for self-dual Eisenstein series of varying
  levels*, arXiv:2208.03358, Theorem 1.2; its additive rational large
  sieve is mapped to the primitive centered dual family in Section 9.35.
* T. Wright, *Trilinear Kloosterman fractions I: partially fixed moduli and
  unbalanced convolutions*, arXiv:2604.25177v2, Theorem 2.1, audited but not
  used for a new box in Section 8.3.
* A. Pascadi, *Non-Abelian Amplification and Bilinear Forms with
  Kloosterman Sums*, Geom. Funct. Anal. (online 21 August 2026),
  DOI 10.1007/s00039-026-00746-0, especially Theorem 7.8 and Corollary
  7.9; audited in Sections 9.5 and 9.27.
* V. Blomer, A. Pascadi, *Bilinear forms with Kloosterman sums via
  quadratic characters*, arXiv:2607.24311v1, especially Theorem 1.1,
  Lemma 3.3, and Propositions 3.4 and 3.6; audited in Section 9.27.
* A. Menon, *Improved bounds for multiplicative functions in almost all
  short intervals*, arXiv:2607.15574v1, especially Theorems 1.4 and 1.5;
  its logarithmic averaged-Chowla ceiling is audited in Section 9.27.
* A. Pascadi, *Large sieve inequalities for exceptional Maass forms and
  the greatest prime factor of \(n^2+1\)*, arXiv:2404.04239,
  Corollary 18; specialized in Section 9.11.
* D. Milićević, X. Qin, X. Wu, *Bilinear forms with Kloosterman sums and
  moments of twisted L-functions*, arXiv:2511.07550, Theorem 1.1; audited
  in Section 9.6.
* M. A. Korolev, *On Kloosterman sums with multiplicative coefficients*,
  Izv. Math. 82:4 (2018), 647--661, DOI 10.1070/IM8633, Theorems 1 and 5;
  audited in Section 9.8.
* M. A. Korolev, *Kloosterman sums with primes to composite moduli*,
  Research in Number Theory 6 (2020), article 24,
  arXiv:1911.09981, Theorem 1; its exact nonhomogeneous Type-I coverage
  and saving exponent are audited in Section 9.77.
* É. Fouvry, E. Kowalski, P. Michel, *Algebraic trace functions over the
  primes*, Duke Math. J. 163 (2014), 1683--1736, arXiv:1211.6043,
  Theorems 1.5, 1.7, and 1.17; their one-variable and bilinear
  prime-modulus Type coverage is audited in Section 9.77, while the
  earlier transition projection is audited in Section 9.39.
* É. Fouvry, E. Kowalski, P. Michel, W. Sawin, *Bilinear forms with trace
  functions*, arXiv:2511.09459v3, Theorem 1.3 and Section 9.11.  The
  quantitative theorem is stated for rank-at-least-two gallant sheaves;
  the rank-one inverse-pole discussion does not verify the second
  Type-II exceptional family for the present kernel.  Section 9.78 gives
  an exact dimension obstruction and retains \(1/224\) only as a formal,
  invalidated gallant-formula calibration.
* P. Xi, *Moments and equidistributions of multiplicative analogues of
  Kloosterman sums*, arXiv:2105.15051; its fixed-prime moments concern
  \(p^{-1/2}\sum_a\chi(a+\bar a)\), not the varying-modulus three-factor
  character master (9.596), so Section 9.90 records it as a no-coverage
  comparison rather than an input.
* M. A. Korolev, I. E. Shparlinski, *Sums of algebraic trace functions
  twisted by arithmetic functions*, Proc. Steklov Inst. Math. 314
  (2021), 128--144, arXiv:1804.01337, Theorem 2.1; its saving in the
  \(p^{1/2+\varepsilon}\) range is logarithmic and prime-modulus only.
* arXiv:2601.00292 is **withdrawn from this project's admissible analytic
  inputs**: the author record reports a missing \(L^2\) factor (changing the
  relevant loss from \(L^5\) to \(L^7\)), so the advertised improvement is
  not used.
* M. Radziwiłł, *Limitations to mollifying \(\zeta(s)\)*,
  arXiv:1207.6583, for Farmer's all-\(\theta\) long-mollifier conjecture and
  the nontrivial role of the off-diagonal.
* S. Bettin, S. M. Gonek, *The \(\theta=\infty\) conjecture implies the
  Riemann hypothesis*, arXiv:1604.02740, Theorems 1 and 2; used in
  Section 9.12 only to classify the strength of polynomial-length
  mollified upper bounds, not as an estimate for the present remainder.
* K. Pratt, N. Robles, *Perturbed moments and a longer mollifier for
  critical zeros of \(\zeta\)*, arXiv:1706.04593, for later exploitation of
  Möbius/convolution structure up to lengths below \(T^{4/7}\) or
  \(T^{6/11}\), still far from \(T^3\).
* K. Matomäki, M. Radziwiłł, T. Tao, *An averaged form of Chowla's
  conjecture*, Algebra Number Theory 9 (2015), 2167--2196,
  arXiv:1503.05121v3, Theorem 1.6 and Remark 5.2; mapped exactly to the
  affine family in Section 9.17.
* K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen, T. Ziegler,
  *Higher uniformity of bounded multiplicative functions in short
  intervals on average*, Ann. of Math. 197 (2023), 739--857,
  arXiv:2007.15644; its qualitative \(o(1)\) Fourier-uniformity boundary
  is recorded in Section 9.44.
* K. Matomäki, X. Shao, T. Tao, J. Teräväinen, *Higher uniformity of
  arithmetic functions in short intervals I. All intervals*,
  arXiv:2204.03754, especially the \(\theta=5/8\) Möbius range; its
  arbitrary log-power, rather than fixed \(S^{-1/6}\), saving is audited
  in Section 9.44.
* T. Tao, J. Teräväinen, *The structure of correlations of multiplicative
  functions at almost all scales, with applications to the Chowla and
  Elliott conjectures*, arXiv:1809.02518v2; its almost-all-scales boundary
  is recorded in Section 9.30.
* J. Guo, *Logarithmic Chowla Correlations Uniformly over Fixed
  Polylogarithmic Shift Ranges*, arXiv:2608.23500v2; this very recent
  logarithmically weighted result is used only for the no-coverage audit
  in Section 9.30.
