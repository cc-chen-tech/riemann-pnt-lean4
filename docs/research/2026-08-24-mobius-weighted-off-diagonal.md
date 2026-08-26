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

## 10. What has and has not been proved

**Current classification: Young closes each fixed scalar stratum and the
globally aggregated transition range \(\tau\geq1/4\); the equivalent
Type-I/II packet (9.242) and divisor-incidence packet (9.250) for
\(0\leq\tau<1/4\), hence the full Region-D recombination, remain
unproved.**

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
* the exact scalar recombination (9.247)--(9.250): the two scalar signs
  combine back to \(\mu(s)\), the phase lifts from \(q=s/g\) to \(s\),
  and the scalar family becomes the divisor-incidence multiplicity
  \(\nu_{\mathcal G,\mathcal Q}(s,m)\leq\tau(s)\).  The resulting
  full-modulus incidence large-sieve estimate remains unproved.  Its
  exact LCM-pair energy is (9.251), saving the scalar half-power in the
  coefficient moment.

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
| Scalar Möbius transition packet | exact Type-I/II reduction; joint estimate unproved | (9.239) retains \(\mu(g)\mu(q)\mu(gq+d)\), the exact moving \(d\)-interval, and \(h\delta_0\); (9.241) splits \(\mu(gq+d)\) exactly into short--short and long--long divisor packets.  Absolute Type I has exponent \(\max(1/2,u+v)\), so no cutoff closes it, (9.243)--(9.244); the balanced Type II is the near determinant (9.245)--(9.246).  Direct Bettin--Chandee remains \(T^{1/4}\) high even with free scalar cancellation, (9.252)--(9.254); fixed-prime Möbius--trace estimates save at best the optimistic \(q^{-1/120}\), versus required \(q^{-1/5}\) |
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
* É. Fouvry, E. Kowalski, P. Michel, *Algebraic trace functions over the
  primes*, Duke Math. J. 163 (2014), 1683--1736, arXiv:1211.6043,
  Theorem 1.7; its optimistic prime-modulus exponent at the transition
  length is audited in Section 9.39.
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
* T. Tao, J. Teräväinen, *The structure of correlations of multiplicative
  functions at almost all scales, with applications to the Chowla and
  Elliott conjectures*, arXiv:1809.02518v2; its almost-all-scales boundary
  is recorded in Section 9.30.
* J. Guo, *Logarithmic Chowla Correlations Uniformly over Fixed
  Polylogarithmic Shift Ranges*, arXiv:2608.23500v2; this very recent
  logarithmically weighted result is used only for the no-coverage audit
  in Section 9.30.
