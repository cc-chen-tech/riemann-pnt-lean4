# Möbius-weighted long mollifier: exact off-diagonal reduction

> **Current proof status.**
>
> | Component | Status |
> |---|---|
> | LCM main quadratic form | proved separately |
> | Exact AFE and shifted-divisor identity | under audit in Sections 2--3 |
> | Poisson zero/nonzero-mode identity | proved after correction in Section 4 |
> | MWKF local estimate | unproved |
>
> Thus this note is not a proof of the \(T^3\) long-mollifier asymptotic.
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
\(\Lambda(1-s_t+z)\) occur at \(z=s_t-1,s_t\).  In that order, they are
cancelled by the following zeros:

\[
 \begin{array}{c|c}
 \text{pole} & \text{zero of }G_t\\ \hline
 -s_t & 1-z^2/s_t^2\\
 1-s_t & 1-z^2/(1-s_t)^2\\
 s_t-1=-(1-s_t) & 1-z^2/(1-s_t)^2\\
 s_t & 1-z^2/s_t^2
 \end{array}
\]

For \(V>2t+2\), use the positively oriented rectangle with vertices
\(-2-iV,2-iV,2+iV,-2+iV\).  Its right side is traversed upward and its
left side downward.  Stirling's formula
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

On \(\Re z=2\), the two zeta arguments satisfy
\(\Re(s_t+z)=\Re(1-s_t+z)=5/2\), and their Dirichlet series have the
absolute majorant

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

Here are the derivatives entering (2.5).  Put the signed falling-factorial
polynomial

\[
 P_j(z)=\prod_{r=0}^{j-1}(-z-r),\qquad P_0(z)=1.
\]

Differentiation under the absolutely convergent Mellin integral gives

\[
 x^j\partial_x^j\partial_t^kV_t(x)=\frac1{2\pi i}\int_{(2)}
 P_j(z)\partial_t^k\!\left(G_t(z)g_t(z)\right)
 x^{-z}\frac{dz}{z}.
\tag{2.5b}
\]

Thus the \(j\) derivatives in \(x\) contribute exactly the degree-\(j\)
polynomial \(P_j(z)\).  For the \(t\)-dependence of \(G_t\), write
\(A_t(z)=1-z^2/s_t^2\) and
\(B_t(z)=1-z^2/(1-s_t)^2\).  Direct differentiation gives, for \(a\geq1\),

\[
 \partial_t^aA_t(z)
 =(-1)^{a+1}i^a(a+1)!\,z^2s_t^{-a-2},\qquad
 \partial_t^aB_t(z)
 =-i^a(a+1)!\,z^2(1-s_t)^{-a-2},
\tag{2.5c}
\]

and hence

\[
 \partial_t^kG_t(z)=e^{z^2}
 \sum_{a+b=k}{k\choose a}
 (\partial_t^aA_t(z))(\partial_t^bB_t(z)).
\tag{2.5d}
\]

Every positive derivative in (2.5c) therefore contributes the displayed
power \(z^2\) and an inverse power \(s_t^{-a-2}\) or
\((1-s_t)^{-a-2}\).  On \(T\leq t\leq2T\), multiplying a total of \(k\)
derivatives by \(T^k\) leaves only a fixed polynomial in \(|z|\).

For \(g_t\), define the logarithmic gamma derivatives

\[
 \ell_r(w)=\frac{d^r}{dw^r}\log\gamma(w)
 =\begin{cases}
 -\frac12\log\pi+\frac12\psi(w/2),&r=1,\\
 2^{-r}\psi^{(r-1)}(w/2),&r\geq2,
 \end{cases}
\tag{2.5e}
\]

where \(\psi^{(r-1)}\) is a polygamma function.  Exact logarithmic
differentiation gives

\[
 L_r(t,z):=\partial_t^r\log g_t(z)
 =i^r\bigl(\ell_r(s_t+z)-\ell_r(s_t)\bigr)
  +(-i)^r\bigl(\ell_r(1-s_t+z)-\ell_r(1-s_t)\bigr),
\tag{2.5f}
\]

and Fa\`a di Bruno's formula gives

\[
 \partial_t^kg_t(z)=g_t(z)
 B_k\bigl(L_1(t,z),\ldots,L_k(t,z)\bigr),
\tag{2.5g}
\]

where \(B_k\) is the complete Bell polynomial.  Thus the only additional
factors are the polygamma differences in (2.5f), whose arguments inside
each difference are separated by \(z/2\).

Fix \(c>-1/2\).  On \(\Re z=c\) and \(|\Im z|\leq T/2\), the standard
polygamma estimates applied to (2.5f) give

\[
 L_r(t,z)\ll_{c,r}T^{-r}(1+|z|)^{C_r}.
\tag{2.5h}
\]

For \(|\Im z|>T/2\), the factor \(e^{z^2}\) supplies Gaussian decay;
the polynomial and logarithmic factors from Stirling and the polygamma
functions are absorbed by \(e^{-(\Im z)^2/2}\).  Equations
(2.5c)--(2.5h), after splitting the vertical integral into these central
and tail ranges, yield

\[
 T^k\left|\partial_t^k\{G_t(c+iv)g_t(c+iv)\}\right|
 \ll_{c,k}T^c(1+|v|)^{C_{c,k}}e^{-v^2/2}.
\tag{2.5i}
\]

For \(0<x\leq T\), shift (2.5b) to \(\Re z=-c\), where
\(0<c<1/4\).  The only crossed pole is \(z=0\).  Its residue is
\(G_t(0)g_t(0)=1\) when \(j=k=0\), and it is zero when \(j+k>0\), since
\(P_j(0)=0\) for \(j>0\) and the residue \(1\) is independent of \(t\).
The new-line integral is \(O_{j,k}((x/T)^c)\).  For \(x\geq T\), shift
instead to \(\Re z=A+1\), crossing no pole; (2.5i) gives
\(O_{A,j,k}((T/x)^{A+1})\).  The horizontal pieces vanish by the same
Gaussian estimate.  The use of \(A+1\), rather than \(A\), explicitly
handles \(A=0\) without placing the shifted contour on the pole at \(z=0\).
These two estimates prove (2.5), for \(T\geq2\), with no factor
\(T^{\epsilon_{j,k}}\).

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

Opening the two mollifier sums causes no convergence issue because the
\(d,e\) sums are finite.  On the support of \(W(t/T)\), (2.5) and (2.5a)
majorize the remaining \(m,n\) sum absolutely, uniformly over those finitely
many \(d,e\).  It is therefore legitimate first to open the mollifier and
then to separate the equations \(me=nd\) and \(me\ne nd\).

For every fixed positive integer \(u\), only finitely many dyadic factors
\(F_X(u)\) are nonzero (in fact at most three for the support in (3.1)).
Thus all four dyadic partitions may be inserted term by term.  Each
individual sum in (3.3) is finite because all four variables have compact
dyadic support, while (2.5a) permits the countable sum over boxes to be
rearranged absolutely.  Equation (3.1) is an identity on \((0,\infty)\),
so this reindexing produces neither an endpoint term nor a limiting boundary
term.  Therefore

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
 m_1s-m_2r=\delta.
\tag{4.3}
\]

### 4.1 Residue class and Poisson normalization

Since \((r,s)=1\), equation (4.3) is equivalent to

\[
 m_2\equiv-\bar r\delta\pmod s,
 \qquad
 m_1=\frac{m_2r+\delta}{s},
 \qquad m_2>0,\quad m_2r+\delta>0.
\tag{4.3a}
\]

Our Fourier convention and the corresponding residue-class Poisson formula
are

\[
 \widehat f(\xi)=\int_{\mathbb R}f(x)e(-\xi x)\,dx,
 \qquad
 \sum_{n\equiv b\ (s)}f(n)
 =\frac1s\sum_{h\in\mathbb Z}e(hb/s)\widehat f(h/s).
\tag{4.3b}
\]

For each dyadic box the factors below make the extension by zero to
\(\mathbb R\) smooth and compactly supported.  Taking
\(b=-\bar r\delta\) in (4.3b) therefore contributes

\[
 \frac1s e\left(-\frac{h\delta\bar r}{s}\right)
 \int_{\mathbb R}f(x)e(-hx/s)\,dx.
\tag{4.3c}
\]

The factor preceding the \(m_2\)-sum in (2.6) is
\(2/(q\sqrt{rs})\).  Thus (4.3c) gives exactly
\(2/(q\sqrt{rs}\,s)\), with the displayed minus sign in the phase; no
factor of \(q\), \(r\), or \(s\) is absorbed into the kernel.

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
contains all nonzero Poisson modes.  The conditions \((r,s)=1\),
\(qr,qs\leq N\), and the positivity condition in (4.3a) remain in force.

### 4.2 Zero mode from a common Mellin integral

First sum the \(K,M\) partitions, before Mellin inversion.  On the domain
\(x>0\), \(xr+\delta>0\), equation (3.1) gives

\[
 \sum_{K,M}F_M(x)F_K((xr+\delta)/s)=1.
\tag{4.5a}
\]

All dyadic scales occur in (4.5a), including scales whose original integer
sum is empty; the complete Poisson identity for each such scale is zero.
Consequently (4.5a) introduces no endpoint or boundary term.  The sum of all
zero modes is therefore

\[
\begin{aligned}
 \mathcal Z_0={}&2
 \sum_{\substack{q,r,s\geq1\\(r,s)=1\\qr,qs\leq N}}
 \frac{a_N(qr)a_N(qs)}{q\sqrt{rs}\,s}
 \sum_{\delta\ne0}
 \int_{\mathbb R}W(t/T)\int_{\substack{x>0\\xr+\delta>0}}
 \frac{V_t(x(xr+\delta)/s)}{\sqrt{x(xr+\delta)/s}}\\
 &\hspace{44mm}\times
 \left(1+\frac{\delta}{xr}\right)^{it}dx\,dt.
\end{aligned}
\tag{4.5b}
\]

There is no unregularized Mellin line on which the endpoint integrals and
the signed \(\delta\)-series are both absolutely convergent: the endpoints
ask for \(\Re z<1/2\), whereas \(\sum_{k\geq1}k^{-2z}\) asks for
\(\Re z>1/2\).  To avoid a false Fubini step, introduce the temporary
endpoint regulator

\[
 \rho_\alpha(x,\delta)=
 \begin{cases}
  (rx/(rx+\delta))^\alpha,&\delta>0,\\
  ((rx+\delta)/(rx))^\alpha,&\delta<0.
 \end{cases}
\tag{4.5c}
\]

Both bases in (4.5c) lie in \((0,1)\).  For real \(0<\alpha<2\), shift
(2.3), without crossing \(z=0\), to the moving line

\[
 \Re z=\sigma_\alpha:=\frac12+\frac\alpha2;
 \qquad
 \frac12<\sigma_\alpha<\frac32,\qquad
 \alpha>\sigma_\alpha-\frac12.
\tag{4.5d}
\]

After inserting \(\rho_\alpha\), the \(x\)-integrals and the
\(\delta\)-sum are absolutely convergent on this initial line.  Indeed, put
\(a=s_t+z\), \(b=1-s_t+z\), and write \(k=|\delta|\).  Direct beta
integrals give

\[
\begin{aligned}
 \int_0^\infty x^{-a}(rx+k)^{-b}
  \left(\frac{rx}{rx+k}\right)^\alpha dx
 &=r^{a-1}k^{-2z}
   \frac{\Gamma(1-a+\alpha)\Gamma(2z)}
        {\Gamma(b+\alpha)},\\
 \int_{k/r}^\infty x^{-a}(rx-k)^{-b}
  \left(\frac{rx-k}{rx}\right)^\alpha dx
 &=r^{a-1}k^{-2z}
   \frac{\Gamma(1-b+\alpha)\Gamma(2z)}
        {\Gamma(a+\alpha)}.
\end{aligned}
\tag{4.5e}
\]

The endpoint beta parameters have positive real parts by (4.5d), and
\(\sum k^{-2z}=\zeta(2z)\) converges absolutely because
\(\sigma_\alpha>1/2\).  Repeated integration by parts in \(t\), together
with (2.5), makes the \(t\)-integrated version of (4.5b) locally uniformly
convergent as \(\alpha\downarrow0\).  The moving line in (4.5d) is
essential: the beta poles \(z=s_t+\alpha\) and
\(z=1-s_t+\alpha\) remain to its right, so none crosses the contour.  At
\(\alpha=0\), their limits \(s_t,1-s_t\) are cancelled by the zeros of
\(G_t\); the limiting pole of \(\zeta(2z)\) at \(z=1/2\) is cancelled by
the cosine zero displayed in (4.5i).  The resulting regular product may
then be moved to any fixed \(1/2<\sigma<3/2\), again without a residue.
Thus the limit recovers the unmodified zero mode, rather than a regularized
replacement or a boundary contribution.  It gives the signed series

\[
 \zeta(2z)\Gamma(2z)B_t(z),\qquad
 B_t(z)=
 \frac{\Gamma(1-s_t-z)}{\Gamma(1-s_t+z)}
 +\frac{\Gamma(s_t-z)}{\Gamma(s_t+z)}.
\tag{4.5f}
\]

There is no coprimality condition on \(\delta\): once \((r,s)=1\), every
\(\delta\ne0\) gives the unique residue class (4.3a).  Thus the local
factors in (4.5f) are exactly
\((1-p^{-2z})^{-1}\), with no deleted prime factor.  Moreover the powers
outside (4.5e) simplify exactly as

\[
 \frac{2}{q\sqrt{rs}\,s}\,\sqrt{s}\,r^{-it}s^z
 r^{s_t+z-1}
 =\frac2{qrs}(rs)^z
 =\frac2{[d,e]}(d^*e^*)^z,
 \qquad d^*=r,\quad e^*=s.
\tag{4.5g}
\]

The completed functional equation used at this point is

\[
 \pi^{-z}\Gamma(z)\zeta(2z)
 =\pi^{z-1/2}\Gamma(1/2-z)\zeta(1-2z).
\tag{4.5h}
\]

Reflection and duplication give, term by term,

\[
 B_t(z)=2^{1-2z}\pi^{-2z}\cos(\pi z)
 \frac{\sin(\pi s_t)}{\sin(\pi s_t)+\sin(\pi z)}
 \frac{g_t(-z)}{g_t(z)}.
\tag{4.5i}
\]

Combining (4.5h)--(4.5i) yields the exact transformation

\[
 \zeta(2z)\Gamma(2z)B_t(z)g_t(z)
 =\frac{\sin(\pi s_t)}{\sin(\pi s_t)+\sin(\pi z)}
  \zeta(1-2z)g_t(-z).
\tag{4.5j}
\]

The quotient of sines in (4.5j) is not identically one.  This is the
archimedean factor omitted in the baseline formula.  Put

\[
 \mathfrak A_t(z)=\frac{\sin(\pi s_t)}{\sin(\pi s_t)-\sin(\pi z)}
 =\frac{\cosh(\pi t)}{\cosh(\pi t)-\sin(\pi z)}.
\tag{4.5k}
\]

After \(z\mapsto-z\), the orientation change supplies a minus sign and
(4.5j) supplies \(\mathfrak A_t(z)\).  The poles of \(\mathfrak A_t\) are
\(s_t+2k\) and \(1-s_t+2k\).  Choosing \(\sigma<3/2\), the shift from
\(\Re z=-\sigma\) to \(\Re z=-c\), \(0<c<1/4\), crosses none of them;
the possible \(g_t\)-poles on \(\Re z=-1/2\) are cancelled by \(G_t\) as
in Section 2.1.  Therefore the corrected zero-mode formula is

\[
 \boxed{
 \mathcal Z_0
 =-
 \frac2{2\pi i}
 \sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{[d,e]}
 \int_{\mathbb R}W(t/T)
 \int_{(-c)}
 (d^*e^*)^{-z}\zeta(1+2z)g_t(z)G_t(z)\mathfrak A_t(z)
 \frac{dz}{z}\,dt. }
\tag{4.6b}
\]

The diagonal calculation has no sine quotient.  Directly from (2.10),

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
 \boxed{
 \mathcal C_{N,W}(T)=
 \frac2{2\pi i}
 \sum_{d,e\leq N}\frac{a_N(d)a_N(e)}{[d,e]}
 \int_{\mathbb R}W(t/T)
 \int_{(-c)}
 (d^*e^*)^{-z}\zeta(1+2z)g_t(z)G_t(z)
 \bigl(1-\mathfrak A_t(z)\bigr)\frac{dz}{z}\,dt. }
\tag{4.6c}
\]

Consequently the corrected diagonal-plus-zero-mode identity is

\[
 \boxed{\mathcal D+\mathcal Z_0
 =T\mathcal Q_{N,T}+\mathcal C_{N,W}(T).}
\tag{4.6}
\]

For completeness, the expansions at \(z=0\) are

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
identity.  Nevertheless it is beyond all polynomial orders at the present
height: splitting the \((-c)\)-line into \(|\Im z|\leq t/2\) and its
complement, using
\(1-\mathfrak A_t(z)=-\sin(\pi z)/(\cosh(\pi t)-\sin(\pi z))\)
on the first part and the Gaussian in \(G_t\) on the second, gives

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
 \mathcal C_{N,W}(T)+
 \sum_{q\geq1}\sum_{R,S,K,M}
 \mathcal O^{\ne0}_{q;R,S,K,M}. }
\tag{4.8}
\]

The nonzero-mode sum in (4.8) is taken in the complete dyadic Poisson
ordering used above.  The convergence supplied by (2.5) and repeated
integration by parts in \(t\) justifies that limit; no rearrangement of
individual Fourier modes and no truncated-AFE error is hidden in (4.8).

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

Fix \(0<\eta<10^{-3}\). Repeated integration by parts in (2.7) and (4.4),
together with (2.5), shows the following precise statement. For every
\(B>0\), the part of the nonzero-mode sum in (4.8) outside the boxes
satisfying (5.3)--(5.8) is \(O_{B,W,\eta}(T^{-B})\):

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
 KM\leq T^{1+\eta};
\tag{5.6}
\]

\[
 \frac1{16}\leq\frac{KS}{MR}\leq16;
\tag{5.7}
\]

In particular,

\[
 M\leq4T^{(1+\eta)/2}\sqrt{\frac SR},\qquad
 K\leq4T^{(1+\eta)/2}\sqrt{\frac RS}.
\tag{5.7a}
\]

\[
 1\leq |\delta|\leq 8MR\,T^{-1+\eta},\qquad
 1\leq |h|\leq 8S M^{-1}T^\eta.
\tag{5.8}
\]

A retained nonempty box must consequently also satisfy

\[
 MR\geq\frac18T^{1-\eta},\qquad
 S\geq\frac18MT^{-\eta}.
\tag{5.8a}
\]

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
 1\leq L\leq8MR T^{-1+\eta},\qquad
 1\leq H\leq8S M^{-1}T^\eta,
\tag{5.10}
\]

and hence

\[
 A:=LH\leq64RS T^{-1+2\eta}.
\tag{5.11}
\]

The oscillating arithmetic phase is exactly

\[
 e\left(-\frac{h\delta\bar r}{s}\right)
 =e\left(-\frac{a\bar r}{s}\right),\qquad a=h\delta.
\tag{5.12}
\]

After the changes \(x=MX\), \(t=T\tau\), the archimedean kernel in a
retained box has the normalization

\[
 \mathscr K_{R,S,K,M}(r,s;\delta,h)
 =T\sqrt{\frac SR}\,\Psi_{R,S,K,M,L,H}
 \left(\frac rR,\frac sS,\frac\delta L,\frac hH\right),
\tag{5.13}
\]

where, for each multi-index \(\mathbf j\),

\[
 \|\partial^{\mathbf j}\Psi\|_\infty
 \leq C_{\mathbf j,W,\eta}T^{|\mathbf j|\eta}.
\tag{5.14}
\]

The factors \(r/R\), \(s/S\), and \(s^{-1}\sqrt{rs}^{-1}\) range in fixed
compact intervals and can be absorbed into \(\Psi\). Consequently one box
has the exact scale

\[
 \mathcal O^{\ne0}_{q;R,S,K,M,L,H}
 =\frac{2T}{qRS}\,\mathfrak S_{q;R,S,K,M,L,H}[\Psi].
\tag{5.15}
\]

## 6. The single local inequality that would prove the target

Smooth Mellin/Fourier separation of the admissible kernel in (5.14) reduces
\(\mathfrak S[\Psi]\) to \(T^{O(\eta)}\) superpositions of the following
three-variable sums. For

\[
 x\in\left[\frac{M}{8S},\frac{8M}{S}\right],\qquad
 y\in\left[\frac{T}{8MR},\frac{8T}{MR}\right],
\tag{6.1}
\]

put

\[
 \nu_{x,y}(a)=
 \sum_{\substack{h\delta=a\\H\leq|h|\leq2H\\L\leq|\delta|\leq2L}}
 U(h/H)V(\delta/L)e\left(-hx+\frac{\delta y}{2\pi}\right),
\tag{6.2}
\]

where \(U,V\in C_c^\infty([-2,-1]\cup[1,2])\), with every fixed derivative
bounded by a constant. Define

\[
\boxed{
\begin{aligned}
 \mathfrak T_q(R,S;L,H;x,y)
 ={}&\sum_{a\ne0}\nu_{x,y}(a)
 \sum_{\substack{R/2\leq r\leq2R\\S/2\leq s\leq2S\\
                  qr,qs\leq N\\(r,s)=(q,rs)=1}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\\
 &\qquad\times U_1(r/R)V_1(s/S)
 e\left(-\frac{a\bar r}{s}\right),
\end{aligned}}
\tag{6.3}
\]

with \(U_1,V_1\in C_c^\infty([1/2,2])\). The coefficient in (6.2) is not
arbitrary. It is a divisor-convolution coefficient and satisfies

\[
 \operatorname{supp}\nu\subset
 \{a:LH\leq|a|\leq4LH\},\qquad
 |\nu(a)|\leq\tau(|a|),\qquad
 \|\nu\|_2\ll_\varepsilon(LH)^{1/2+\varepsilon}.
\tag{6.4}
\]

The required new local statement is:

> **MWKF(3).** Uniformly for every squarefree \(q\), all variables satisfying
> (5.3), (5.6), (5.7), (5.10), all \(x,y\) in (6.1), and all admissible
> smooth weights in (6.2)--(6.3),
> \[
> \boxed{
>  |\mathfrak T_q(R,S;L,H;x,y)|
>  \leq C_{\varepsilon,W}RS\,T^\varepsilon. }
> \tag{6.5}
> \]

This is the promised Möbius-weighted trilinear Kloosterman-fraction gate.
Its exponents are explicit: exponent 1 in the product \(RS\), and no
positive power of \(A=LH\).

Indeed, (5.15) and (6.5) give

\[
 |\mathcal O^{\ne0}_{q;R,S,K,M,L,H}|
 \ll_{\varepsilon,W}\frac{T^{1+\varepsilon}}q.
\tag{6.6}
\]

There are \(O_\eta((\log T)^6)\) retained dyadic choices, and

\[
 \sum_{q\leq N}\frac{\mu^2(q)}q\ll\log(2N).
\tag{6.7}
\]

Therefore (6.5) implies

\[
\boxed{\mathcal R_{T^3,T}\ll_{\varepsilon,W}T^{1+\varepsilon}.}
\tag{6.8}
\]

Here the extra exact term \(\mathcal C_{T^3,W}(T)\) in (4.8) is absorbed by
(4.7c).  All analytic tails already contribute
\(O_{B,W,\eta}(T^{-B})\), so no additional arithmetic estimate is needed
after MWKF(3).

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
| \(H\leq8S/M\,T^\eta\) | \(H_d=N_2/(dM)T^\varepsilon\) | Fourier cutoff |
| \(a=h\delta\) | \(a=h\Delta\) | third trilinear variable |
| \(A=LH\leq64RS/T^{1-2\eta}\) | \(A=N_1N_2/(d^2T^{1-\varepsilon})\) | length of the \(a\)-variable |
| \(e(-a\bar r/s)\) | \(e(-a\bar n_1/n_2)\) | Kloosterman-fraction phase |
| \(\nu_{x,y}(a)\) in (6.2) | \(\nu_{x,y}(a)=\sum_{h\Delta=a}e(-hx+\Delta y/2\pi)\) | divisor-convolution coefficient |
| (6.5) | BCR Proposition 1 / Conjecture 1 slot | arithmetic input |

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
   \(A\leq RS/T^{1-2\eta}\). For \(R=S=T^3\), the latter permits
   \(A=T^{5+2\eta}\), while the BCR hypothesis permits only
   \(A\leq T^{3+\varepsilon}\). Thus even BCR's conjectural arbitrary-
   coefficient estimate does not cover the present long-\(a\) boxes.

4. **Arithmetic structure.** BCR discard the nature of \(a_n\) and use only
   \(L^2\) norms. Equation (5.2) keeps both signs \(\mu(r)\mu(s)\), and
   (6.2) keeps the factorization \(a=h\delta\). MWKF(3) is asserted only for
   this structured class, not for arbitrary coefficients.

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

MWKF(3) instead gives \(T^{1+\varepsilon}\) for the corresponding box.
The missing savings relative to (7.3) cannot come from a rearrangement of
the BCR norm inequalities; it has to use the simultaneous Möbius weights
and the divisor-convolution restriction on \(a\).

The \(T^{3/4}\) result in BCR concerns a product of a smooth polynomial of
length \(T^{1/2}\) and a second polynomial of length \(T^{1/4}\), where Watt's
Kloosterman-sum estimate applies. The single polynomial
\(\mu(n)p_N(n)\mathbf1_{n\leq T^3}\) does not have that factorization, so
that theorem supplies no box estimate for (6.3).

## 8. What has and has not been proved

The status table at the top is the controlling audit ledger.  The LCM main
quadratic form is proved separately.  Sections 2--3 now expose the exact AFE
and shifted-divisor derivations for audit, including their convergence,
contour-orientation, and reindexing checks.  They remain marked “under audit”
until independent review accepts those derivations.

Section 4 proves the Poisson zero/nonzero-mode identity after correcting the
baseline zero-mode functional-equation step.  The exact remainder contains
the archimedean term \(\mathcal C_{N,W}(T)\) in (4.6c), although (4.7c)
makes it smaller than every power of \(T\) when \(N=T^3\).  MWKF(3),
equation (6.5), is unproved.  Equations (6.6)--(6.8) are only a conditional
implication from that proposed local estimate, not an available bound.
Treating MWKF(3) as an already available consequence of BCR would be
incorrect for the range reason in item 3 of Section 7.

## 9. Primary references

* S. Bettin, V. Chandee, M. Radziwiłł, *The mean square of the product of
  the Riemann zeta function with Dirichlet polynomials*, arXiv:1411.7764,
  especially Proposition 1 and Sections 3.1--3.4.
* M. Radziwiłł, *Limitations to mollifying \(\zeta(s)\)*,
  arXiv:1207.6583, for Farmer's all-\(\theta\) long-mollifier conjecture and
  the nontrivial role of the off-diagonal.
* K. Pratt, N. Robles, *Perturbed moments and a longer mollifier for
  critical zeros of \(\zeta\)*, arXiv:1706.04593, for later exploitation of
  Möbius/convolution structure up to lengths below \(T^{4/7}\) or
  \(T^{6/11}\), still far from \(T^3\).
