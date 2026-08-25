# Alternative-route spike for the \(T^3\) Möbius mollifier

## 1. Status and question

This is a feasibility spike, not a proof of the long-mollifier
asymptotic.  It starts from the exact symmetric completion in
`2026-08-24-mwkf-global-coupled-coefficient-first.md` and asks whether a
route genuinely different from the generic Bettin--Chandee treatment
produces a weaker local theorem.

The three routes audited here are:

1. Mellin--Euler or character separation of the ordinary fraction phase;
2. a pre-Cauchy, two-Möbius dispersion argument at logarithmic rather than
   fixed-power strength; and
3. interpolation from the single endpoint \(N=T^3\) to shorter
   mollifiers.

Only the second route survives the exponent audit.  It still requires a
new theorem.  In particular, nothing below changes the proof status of the
unconditional asymptotic.

## 2. The exact logarithmic target

Put

\[
 C=\frac SH,\qquad V=\frac SL.
\tag{2.1}
\]

The exact two-dimensional completion is

\[
 \mathfrak S_q[\Psi]=\frac{HL}{S}\mathfrak D_q^{(2)}[\Theta],
\tag{2.2}
\]

where

\[
\begin{aligned}
 \mathfrak D_q^{(2)}[\Theta]
 ={}&\sum_{\substack{R/2\le r\le2R,\ S/2\le s\le2S\\
                      (r,s)=1,\ (q,rs)=1\\qr,qs\le N}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)\frac Ss\\
 &\quad\times\sum_{c,v\bmod s}
 \Theta_{r,s}(c,v)e\left(\frac{rcv}{s}\right),
\end{aligned}
\tag{2.3}
\]

and

\[
 \sum_{c\bmod s}\Theta_{r,s}(c,v)
 =\sum_{v\bmod s}\Theta_{r,s}(c,v)=0.
\tag{2.4}
\]

The fixed power \(T^{-1/1000}\) used in the earlier audit is sufficient
but not necessary.  Under the present crude count of six dyadic
parameters and the harmonic \(q\)-sum, the following logarithmic gate is
also sufficient for the core:

\[
\boxed{
 \mathrm{LMSD}_{B}:\qquad
 |\mathfrak D_q^{(2)}[\Theta]|
 \ll_{B,W}
 \frac{RS^2}{HL}(\log(2T))^{-B}
 =RCV(\log(2T))^{-B},\qquad B>7.}
\tag{2.5}
\]

Indeed, (2.2) turns (2.5) into

\[
 |\mathfrak S_q[\Psi]|\ll_{B,W}RS(\log(2T))^{-B},
\tag{2.6}
\]

and the box and \(q\)-aggregation is then

\[
 \sum_{q\le N}\sum_{\text{retained boxes}}
 \frac{2T}{qRS}|\mathfrak S_q[\Psi]|
 \ll_{B,W}T(\log(2T))^{7-B}=o_W(T).
\tag{2.7}
\]

At the balanced hard box

\[
 R=S=T^3,\qquad H=L=T^{5/2},\qquad C=V=T^{1/2},
\tag{2.8}
\]

(2.5) is the single explicit inequality

\[
 \boxed{|\mathfrak D_q^{(2)}[\Theta]|
 \ll_{B,W}T^4(\log(2T))^{-B}.}
\tag{2.9}
\]

The square-root volume of (2.3) is

\[
 (RSCV)^{1/2}.
\tag{2.10}
\]

Consequently (2.5) permits the precise loss

\[
 \left(\frac{RS}{HL}\right)^{1/2}(\log(2T))^{-B}
\tag{2.11}
\]

beyond square-root cancellation.  In (2.8), (2.11) is
\(T^{1/2}(\log(2T))^{-B}\).  Thus a spectral estimate may lose the
whole \(T^{1/2}\) conductor factor; the genuinely Möbius-specific input
only has to recover a sufficiently large logarithmic saving.

There is also an exact endpoint gain which the power-scale audit erased.
If \(N/4\le qR\le N\) and \(r\in[R/2,2R]\) with \(qr\le N\), then

\[
 0\le p_N(qr)=\frac{\log(N/(qr))}{\log N}
 \le\frac{\log 8}{\log N}.
\tag{2.12}
\]

The two mollifier factors therefore give \((\log N)^{-2}\) in the
top endpoint collar.  This does not by itself beat the current
\((\log T)^7\) aggregation loss, but it must be retained in a sharp
logarithmic proof.

## 3. Route A: Mellin--Euler separation

This route fails by a positive power even under an optimistic separation
which the actual coefficient does not possess.

Let \(U\in C_c^\infty((1/2,2))\) and, for an integer \(a\ge1\), define

\[
 K_a(\tau)=\int_0^\infty U(x)e(ax)x^{-i\tau}\,\frac{dx}{x}.
\tag{3.1}
\]

Stationary phase gives, for every fixed \(A_0\), a constant \(C_{A_0,U}\)
such that

\[
 |K_a(\tau)|\le C_{A_0,U}a^{-1/2}
 \quad (|\tau|\le C_{A_0,U}a),
\tag{3.2}
\]

and the contribution from \(|\tau|>C_{A_0,U}a\) is
\(O_{A_0,U}(a^{-A_0})\) after repeated integration by parts.  Write

\[
 \mathcal M_R(\tau)
 =\sum_{R/2\le r\le2R}\mu(r)w_R(r)r^{i\tau}.
\tag{3.3}
\]

For every interval \(I\) of length at most \(4a\), the classical
Dirichlet-polynomial mean-value inequality gives

\[
 \int_I|\mathcal M_R(\tau)|^2d\tau
 \ll (R+a)\sum_{R/2\le r\le2R}|w_R(r)|^2
 \ll R^2,
\tag{3.4}
\]

because \(a\le T\) and \(R=T^3\) in the hard box.  Even if one replaces
the actual \((r,s)\)-dependent coefficient
\(\Lambda_{r,s}(a)\) by a separated coefficient of modulus at most one,
(3.2)--(3.4) and Cauchy--Schwarz give

\[
 \int K_a(\tau)\mathcal M_R(\tau)
 \overline{\mathcal M_S(\tau)}\,d\tau
 \ll RS\,a^{-1/2}.
\tag{3.5}
\]

Summing (3.5) for \(1\le a\le A\) yields

\[
 RS\sum_{a\le A}a^{-1/2}\ll RS A^{1/2}.
\tag{3.6}
\]

For \((R,S,A)=(T^3,T^3,T)\), (3.6) is \(T^{13/2}\).  The logarithmic
target (2.9) is \(T^4(\log(2T))^{-B}\), so Mellin separation has the
fixed deficit

\[
 \frac{T^{13/2}}{T^4}=T^{5/2}.
\tag{3.7}
\]

Zero-free-region estimates for the vertical Möbius polynomial in (3.3)
can supply logarithmic or subexponential factors, but they cannot recover
the positive power in (3.7).  Moreover, the true
\(\Lambda_{r,s}(a)\) depends on both long variables, so (3.5) is already
more favourable than the available exact expression.

A multiplicative-character expansion reaches the same obstruction.  If
\(g=(a,s)\), \(s'=s/g\), and \(a'=a/g\), then for \((r,s)=1\)

\[
 e\left(\frac{ar}{s}\right)
 =\frac1{\varphi(s')}
 \sum_{\chi\bmod s'}\tau(\overline\chi)\chi(a'r).
\tag{3.8}
\]

Here \(s'\) can equal \(s\), so its conductor can be \(T^3\), the same
size as the Möbius polynomial.  Character orthogonality or the character
large sieve then contains its full diagonal term; the formal identity
\(\sum\mu(n)\chi(n)n^{-z}=1/L(z,\chi)\) does not provide a uniform
power saving for conductors as large as the summation length.

**Decision for Route A:** reject it as the primary route.  It may still
be used after a dispersion step has already supplied the missing
\(T^{5/2}\), but it cannot supply that step itself.

## 4. Route B: logarithmic two-Möbius dispersion

This is the only route in the spike which is not ruled out by a positive
power deficit.

The normalization of \(\Theta\) gives the exact finite Parseval identity

\[
 \sum_{c,v\bmod s}|\Theta_{r,s}(c,v)|^2
 =\frac{s^2}{H^2L^2}
 \sum_{x,y\bmod s}|F_{r,s}(x,y)|^2.
\tag{4.1}
\]

Since \(F_{r,s}\) is supported on at most \(O_W(HL)\) residue pairs and
is uniformly bounded, (4.1) implies

\[
 \sum_{c,v\bmod s}|\Theta_{r,s}(c,v)|^2
 \ll_W\frac{s^2}{HL}=CV.
\tag{4.2}
\]

For a nonzero normalized kernel whose squared mass on the original
\((h,\delta)\)-box is at least \(c_WHL\), (4.1) also gives the matching
lower bound \(c_WCV\).  Thus an early Cauchy--Schwarz inequality sees a
genuine diagonal of the same scale as (4.2).  At the hard box the
resulting barrier is exactly \(T^4\), not
\(T^4(\log(2T))^{-B}\).

It follows that the new estimate cannot have the fixed order

\[
 \text{Cauchy}\ \longrightarrow\ \text{discard the signed off-diagonal}
 \ \longrightarrow\ \text{spectral large sieve}.
\tag{4.3}
\]

It must instead do one of the following before the positive diagonal is
created:

1. retain both Möbius weights through the Poincaré/Kuznetsov transform and
   prove logarithmic cancellation in the resulting spectral coefficients;
2. use a Linnik dispersion identity in which an explicit main diagonal is
   subtracted before Cauchy--Schwarz; or
3. combine the endpoint factors (2.12) with a global square-function
   aggregation that reduces the present seven logarithmic losses below
   two.

The exact Möbius decomposition remains available.  For \(U\ge1\), put

\[
 c_U(a)=\sum_{\substack{d\mid a\\d\le U}}\mu(d).
\tag{4.4}
\]

For every integer \(n>U\),

\[
 \mu(n)=-\sum_{\substack{ab=n\\a>U}}c_U(a)\mu(b).
\tag{4.5}
\]

At \(R=S=T^3\), the exact cutoff choice \(U=V_0=T\) divides each
Möbius weight into a Type-I part with \(b\le V_0\) and a Type-II part
with \(b>V_0\).  The symbol \(V_0\) is distinct from the completion
length \(V=S/L\) in (2.1).
The first genuinely new local proposition can therefore be stated without
an exponent ambiguity:

> For every one of the four Type-I/II combinations obtained by applying
> (4.5) to \(r\) and \(s\), retain the signs in (2.3) and prove that the
> sum of the four pieces is
> \[
> \ll_{B,W}RCV(\log(2T))^{-B},\qquad B>7.
> \tag{4.6}
> \]
> Equivalently, at (2.8), prove
> \(T^4(\log(2T))^{-B}\).

The phrase “sum of the four pieces” in (4.6) is essential.  Requiring
each Cauchy diagonal separately to satisfy (4.6) is stronger than the
original signed problem and is contradicted by the Parseval scale in
(4.1).

The precise spectral budget for (4.6) is

\[
 \boxed{
 (RSCV)^{1/2}
 \left(\frac{RS}{HL}\right)^{1/2}
 (\log(2T))^{-B}
 =RCV(\log(2T))^{-B}.}
\tag{4.7}
\]

Thus any proposed Kuznetsov adapter is falsified immediately if its
conductor loss exceeds \((RS/(HL))^{1/2}\) by a fixed power.  It is also
falsified if it creates the diagonal (4.1) before producing a logarithmic
Möbius factor.

There is an important caveat.  The determinant equation
\(rv-js=\delta\) parametrizes integer matrices, but \(\mu(r)\mu(s)\)
weights two matrix entries and is not automorphic.  A Poincaré expansion
does not automatically turn it into
\(\sum\mu(n)\lambda_f(n)w(n/R)\).  The appearance of such a Hecke
polynomial must be derived; assuming it would be a gap.  The continuous
spectrum and possible exceptional real characters must be audited at the
same point.

**Decision for Route B:** select it for the next research slice, with
the weaker logarithmic gate (4.6)--(4.7).  This is a viable program, not a
completed estimate.  The separate seminorm-sensitive
\(\mathrm{TAIL}_{B,D}\) obligation also remains.

### 4.1 Exact centered-shift form and averaged Chowla audit

There is a further exact reindexing which exposes what an averaged-Chowla
input can and cannot do.  Put

\[
 d=r-s.
\tag{4.8}
\]

Since \(a\) is an integer,

\[
 \boxed{
 e\left(\frac{ar}{s}\right)-1
 =e\left(\frac{a(s+d)}s\right)-1
 =e\left(\frac{ad}s\right)-1.}
\tag{4.9}
\]

Moreover \((r,s)=1\) is exactly \((s,d)=1\).  For all sufficiently
large \(T\) in a box with positive \(r\)- and \(s\)-exponents, \(d=0\)
is impossible: it would give \((r,s)=s>1\).  Thus (2.3), after grouping
\(a=cv\), is exactly

\[
\begin{aligned}
 \mathfrak D_q^{(2)}[\Theta]
 ={}&\sum_{\substack{S/2\le s\le2S\\
                      R/2\le s+d\le2R\\
                      d\ne0,\ (s,d)=1\\
                      (q,s(s+d))=1\\
                      qs,q(s+d)\le N}}
 \mu(s+d)\mu(s)p_N(q(s+d))p_N(qs)\frac Ss\\
 &\quad\times\sum_{a\ne0}\Lambda_{s+d,s}(a)
 \left\{e\left(\frac{ad}{s}\right)-1\right\}.
\end{aligned}
\tag{4.10}
\]

No oscillatory estimate is used in (4.8)--(4.10).  In the balanced hard
box the exact interval constraints imply

\[
 -\frac32T^3\le d\le\frac32T^3,
\tag{4.11}
\]

while the effective product-frequency exponent is one.

Matomäki--Radziwiłł--Tao, Theorem 1.6, applies to averages of fixed
linear-form correlations.  The substitution (4.8) is favourable in one
respect: the two forms \(s\) and \(s+d\) both have unit slope, so the
theorem's \(A^2\) loss for growing linear coefficients is absent.  For
the Möbius function its quantitative factor is bounded by

\[
 \eta(X,D)
 :=\frac{\log\log D}{\log D}
   +\frac1{\log^{1/3000}X},
\tag{4.12}
\]

up to a change of the absolute implied constant when
\(10\le D\le X\).

This still does not estimate (4.10).  There are two exact failures.
First, \(\Lambda_{s+d,s}(a)\) depends jointly on the base variable
\(s\), the shift \(d\), and the product frequency \(a\); it is not a
fixed coefficient attached to either linear form in Theorem 1.6.
Second, even under the optimistic replacement
\(|\Lambda_{s+d,s}(a)|\le T^{o(1)}\), taking the triangle inequality in
\(a\) gives exponent

\[
 \underbrace{3}_{s}
 +\underbrace{3}_{d}
 +\underbrace{1}_{a}=7,
\tag{4.13}
\]

with only the logarithmic factor (4.12).  The logarithmic LMSD target has
exponent four, so the exact remaining power deficit is

\[
 7-4=3.
\tag{4.14}
\]

The function `averaged_chowla_shift_audit` records (4.11)--(4.14) with
exact rational exponents and returns the rejection reasons

```
joint_s_shift_frequency_coefficient
averaged_chowla_saves_only_logarithms
positive_power_deficit
```

Therefore averaged Chowla is not the spectral power-saving step.  It can
only be a candidate for the final logarithmic gain after a pre-Cauchy
spectral argument has already reduced exponent seven to the barrier
exponent four.

### 4.2 An unconditional centered near-resonance collar

The subtraction in (4.10) does give a local estimate before any spectral
input.  Choose the least absolute representatives
\(c,v\in\mathcal C_s\), and recall the exact finite coefficient

\[
 \Lambda_{r,s}(a)
 :=\sum_{\substack{c\mid a\\
                    c,a/c\in\mathcal C_s\setminus\{0\}}}
 \Theta_{r,s}(c,a/c).
\tag{4.15}
\]

The centering in (4.10) is exact because the physical \(h\)- and
\(\delta\)-supports miss both coordinate axes; equivalently the total
Fourier sum is zero.  No additional assertion
\(\sum_a\Lambda_{r,s}(a)=0\) is needed.  From the two-variable decay of
\(\Theta\), with any fixed \(A>3\),

\[
\begin{aligned}
 \sum_{a\ne0}|a\Lambda_{r,s}(a)|
 &\le \sum_{\substack{c,v\in\mathcal C_s\\c v\ne0}}
          |cv|\,|\Theta_{r,s}(c,v)|\\
 &\ll_{A,W}
 \left\{\sum_{c\in\mathbb Z}|c|(1+|c|/C)^{-A}\right\}
 \left\{\sum_{v\in\mathbb Z}|v|(1+|v|/V)^{-A}\right\}\\
 &\ll_{A,W}(CV)^2,
\end{aligned}
\tag{4.16}
\]

provided \(C,V\ge1\), as they are in (2.8).  Extending the finite sums to
\(\mathbb Z\) only enlarges the nonnegative majorant, so (4.16) has no
transform-tail error.

For \((s,d)=1\), define the exact resonance distance

\[
 \Delta_s(d):=\min_{j\in\mathbb Z}|d-js|.
\tag{4.17}
\]

In the hard box \(s>1\), so \(\Delta_s(d)=0\) would contradict
\((s,d)=1\).  Since \(a\in\mathbb Z\), choose a minimizing \(j\) in
(4.17) and use \(e(ad/s)=e(a(d-js)/s)\).  The elementary inequality

\[
 |e(x)-1|\le2\pi|x|
\tag{4.18}
\]

and (4.16) give, for every admissible \((s,d)\),

\[
 \boxed{
 \left|\sum_{a\ne0}\Lambda_{s+d,s}(a)
       \left\{e\left(\frac{ad}{s}\right)-1\right\}\right|
 \ll_W \frac{\Delta_s(d)}s(CV)^2.}
\tag{4.19}
\]

Now restrict (4.10) to \(\Delta_s(d)\le D\), where \(1\le D\le S/2\).
For fixed \(s\asymp S\), (4.11) confines the possible multiples \(js\)
to an absolute bounded set.  For each such \(j\), at most two integers
\(d\) have \(|d-js|=k\).  Consequently

\[
 \sum_{\substack{d:\ R/2\le s+d\le2R\\
                   0<\Delta_s(d)\le D}}
 \Delta_s(d)
 \ll \sum_{1\le k\le D}k\ll D^2.
\tag{4.20}
\]

All arithmetic and mollifier weights outside the inner sum in (4.10)
have modulus at most one, apart from \(S/s\ll1\).  Summing (4.19) with
(4.20) over the \(O(S)\) values of \(s\asymp S\) therefore proves the
unconditional local inequality

\[
 \boxed{
 |\mathfrak D_{q,\mathrm{near}}^{(2)}(D)|
 \ll_W (CV)^2D^2.}
\tag{4.21}
\]

In exponent notation put \(CV=T^p\) and choose

\[
 D=T^{(\rho-p)/2-\eta},\qquad \eta>0.
\tag{4.22}
\]

Then (4.21) is \(T^{\rho+p-2\eta}\), whereas the power scale of the
LMSD gate is \(RCV=T^{\rho+p}\).  At (2.8), \(p=1\), and (4.22)--(4.21)
become

\[
 \boxed{
 \Delta_s(d)\le T^{1-\eta}
 \quad\Longrightarrow\quad
 |\mathfrak D_{q,\mathrm{near}}^{(2)}|
 \ll_W T^{4-2\eta}.}
\tag{4.23}
\]

Thus a genuine fixed-power collar around every resonance \(d=js\) is
already covered.  The exact-rational function
`centered_resonance_scales` records the exponents in
(4.16), (4.22), and (4.23); for \(\eta=1/1000\) it returns the saving
\(1/500\).

This does not prove (2.9): the residual region

\[
 \Delta_s(d)>T^{1-\eta}
\tag{4.24}
\]

still requires the pre-Cauchy two-Möbius dispersion estimate, and the
separate \(\mathrm{TAIL}_{B,D}\) obligation remains.  It does, however,
remove the entire near-resonance range from that new theorem.

The same estimate should be matched to the logarithmic, rather than the
power, gate.  Write \(\mathscr L=\log(2T)\).  In a double-centered box
with \(R\ge CV\mathscr L^B\), and for \(B>7\), set

\[
 D_B:=\left(\frac{R}{CV}\right)^{1/2}\mathscr L^{-B/2}.
\tag{4.25}
\]

Equation (4.21) now gives the exact asymptotic-level estimate

\[
 \boxed{
 |\mathfrak D_{q,\mathrm{near}}^{(2)}(D_B)|
 \ll_W RCV\,\mathscr L^{-B}.}
\tag{4.26}
\]

After (2.2) and the current seven-logarithm aggregation in (2.7), the
contribution of (4.26) to the original remainder is

\[
 \ll_W T\mathscr L^{7-B}=o_W(T).
\tag{4.27}
\]

In the hard box,

\[
 D_B=T\mathscr L^{-B/2}.
\tag{4.28}
\]

Thus (4.28), rather than the smaller fixed-power collar in (4.23), is the
sharp boundary to use in the residual theorem.  The function
centered_resonance_log_budget records (4.25)--(4.27) with exact rational
logarithmic exponents.

### 4.3 Exact far-resonance shell gate

For a dyadic \(D\) with \(D_B<D\ll S\), let
\(\mathfrak D_{q,D}^{(2)}\) denote the restriction of the exact sum
(4.10) to

\[
 D<\Delta_s(d)\le2D.
\tag{4.29}
\]

All coprimality, endpoint, dyadic, Möbius, and coefficient conditions in
(4.10) remain in force.  Besides (4.16), the decay of \(\Theta\) gives

\[
 \sum_{a\ne0}|\Lambda_{r,s}(a)|
 \le \sum_{\substack{c,v\in\mathcal C_s\\cv\ne0}}
       |\Theta_{r,s}(c,v)|
 \ll_W CV.
\tag{4.30}
\]

There are \(O(D)\) admissible shift integers in (4.29) for each
\(s\asymp S\).  Using (4.19) until its phase bound reaches one, and
(4.30) afterwards, proves the piecewise absolute estimate

\[
 \boxed{
 |\mathfrak D_{q,D}^{(2)}|
 \ll_W
 \begin{cases}
   (CV)^2D^2,&D\le S/(CV),\\[2mm]
   SDCV,&S/(CV)\le D\ll S.
 \end{cases}}
\tag{4.31}
\]

The two expressions agree at \(D=S/(CV)\).  Therefore the precise
missing shell theorem is

\[
 \boxed{
 \mathrm{FRSD}_{B}:\qquad
 |\mathfrak D_{q,D}^{(2)}|
 \ll_{B,W}RCV\,\mathscr L^{-B}
 \quad(D_B<D\ll S),\qquad B>7.}
\tag{4.32}
\]

Relative to (4.31), (4.32) asks for the cancellation multiplier

\[
 \mathscr L^{-B}
 \begin{cases}
   R/(CV D^2),&D\le S/(CV),\\[2mm]
   R/(SD),&D\ge S/(CV).
 \end{cases}
\tag{4.33}
\]

At the hard box write \(D=T^\delta\).  The absolute exponent and the
required positive-power saving exponent are exactly

\[
\begin{array}{c|c|c}
 \text{distance range}&\text{absolute exponent}
   &\text{required saving}\\ \hline
 1\le\delta\le2&2+2\delta&2\delta-2\\
 2\le\delta\le3&4+\delta&\delta.
\end{array}
\tag{4.34}
\]

In particular, \(\delta=1\) is a purely logarithmic critical face,
\(\delta=2\) requires a two-power saving, and the largest shell
\(\delta=3\) requires a three-power saving.  The exact-rational function
far_resonance_shell_scales records (4.31)--(4.34).  It is only a gate:
no existing adapter in this audit proves (4.32), because the completed
coefficient still depends jointly on \((s,d,a)\).

The shell formulation also sharpens the averaged-Chowla rejection.  At
the critical power face \(\delta=1\), there is no positive-power deficit,
but Matomäki--Radziwiłł--Tao's quantitative factor gives only

\[
 \mathscr L^{-1/3000}
\tag{4.35}
\]

after absorbing its smaller
\((\log\log D)/\log D\) term.  Taking the first integer gate \(B=8\),
the exact logarithmic shortfall is

\[
 8-\frac1{3000}=\frac{23999}{3000}.
\tag{4.36}
\]

This calculation is still optimistic: the actual
\(\Lambda_{s+d,s}(a)\) is a joint base--shift--frequency coefficient and
is not an input allowed by that theorem.  For every \(\delta>1\), the
positive deficits in (4.34) already rule out a logarithmic theorem even
under this optimistic replacement.  The function
averaged_chowla_shell_audit records both rejection mechanisms separately.

The other published adapters do not improve after merely imposing
(4.29).  The separated Bettin--Chandee comparison still has exponent
\(67/10\) against the power target \(4\), hence deficit \(27/10\), because
the shift restriction does not make \(\Lambda_{s+d,s}(a)\) a separated
coefficient.  The hard-endpoint Wright Type-I and fixed-denominator
adapters retain savings \(-45/8\) and \(-5\), respectively.  Finally,
arXiv:2601.00292 remains excluded from the admissible inputs because its
claimed improvement omits the reported \(L^2\) factor.  Consequently
(4.32), with the piecewise savings (4.34), is the smallest remaining
far-resonance analytic input in this normalization.

## 5. Route C: endpoint-to-all-length interpolation

This route fails algebraically.  Put \(Y=\log X\) and define

\[
 A_Y(s)=\sum_{n\le e^Y}\frac{\mu(n)}{n^s}.
\tag{5.1}
\]

The linear taper satisfies the exact identity

\[
 \boxed{
 Y M_{e^Y}(s)
 =\sum_{n\ge1}\frac{\mu(n)}{n^s}(Y-\log n)_+
 =\int_0^Y A_u(s)\,du.}
\tag{5.2}
\]

Consequently

\[
 \frac{d}{dY}\{Y M_{e^Y}(s)\}=A_Y(s)
\tag{5.3}
\]

away from the discrete break points, with the corresponding distributional
identity everywhere.  Knowledge of the single endpoint
\(M_{T^3}(1/2+it)\) gives one integral in (5.2); it gives no bound for its
integrand and no value of \(M_{T^\theta}(1/2+it)\) for
\(0<\theta<3\).  The kernel of the map
\(A\mapsto\int_0^{3\log T}A(u)du\) is infinite-dimensional, so there is
no norm inequality in the required reverse direction.

Bettin--Gonek's theorem assumes a moment bound for every
\(2\le N\le T^\theta\), not only for \(N=T^\theta\).  Their dyadic
\([T,2T]\) conclusion is the zero-free half-plane
\(\Re s>1/2+2/\theta\); at \(\theta=3\) this boundary is \(7/6\) and
therefore supplies no nontrivial zero-free information.  Varying the
fixed smooth height weight \(W\) does not add the missing length variable
in (5.2).

**Decision for Route C:** reject it.  A uniform family of hypotheses in
the length variable would be additional input, not a consequence of the
single \(T^3\) endpoint.

## 6. Coefficient-first cross-check

The exact identity

\[
 \zeta(s)M_N(s)
 =1+\frac1{\log N}\sum_{2\le n\le N}\frac{\Lambda(n)}{n^s}
 +\mathcal B_N(s)
\tag{6.1}
\]

is useful only when the boundary package \(\mathcal B_N\) is retained.
The prime polynomial in (6.1), taken alone, has length \(N=T^3\); its
mean square over an interval of length \(T\) contains terms of size
\(N/T=T^2\) before cancellation with \(\mathcal B_N\).  Expanding that
piece alone therefore produces an averaged prime-pair problem plus a
positive-power boundary error, not a shortcut to the desired constant.
This is consistent with the connection between long mollification and
zero pair correlation described by Radziwiłł.

## 7. Selected next slice and falsification tests

The next slice should not try to prove the fixed-power CMT gate.  It should
do the following in order:

1. replace the crude boxwise supremum by a coupled square-function
   aggregation and determine the smallest exact logarithmic exponent
   \(B_{\rm agg}\); retain the two endpoint factors (2.12);
2. derive the Poincaré/Kuznetsov transform of (2.3) before applying
   Cauchy--Schwarz, including the continuous spectrum;
3. identify the exact image of each of the four Möbius pieces from (4.5);
4. prove (4.7) with \(B>B_{\rm agg}\), or exhibit one of the following
   rational obstructions:
   - a conductor loss larger than \((RS/(HL))^{1/2}\) by a fixed power;
   - an unavoidable positive diagonal of size \(RCV\) created before any
     Möbius saving; or
   - a spectral coefficient with no multiplicative structure beyond an
     arbitrary sequence.

The relevant published comparison points are
[Bettin--Chandee](https://arxiv.org/abs/1502.00769),
[Bettin--Chandee--Radziwiłł](https://arxiv.org/abs/1411.7764),
[Bettin--Gonek](https://arxiv.org/abs/1604.02740), and
[Radziwiłł](https://arxiv.org/abs/1207.6583).  The Möbius-disjointness
theorem for a fixed horocycle orbit of
[Bourgain--Sarnak--Ziegler](https://arxiv.org/abs/1110.0992) does not
directly apply because both the rational point and its modulus vary in
(2.3).

The outcome of the spike is therefore precise: Mellin separation and
length interpolation are rejected; the surviving task is one
logarithmically strengthened, pre-Cauchy two-Möbius spectral inequality,
(4.7), together with a sharper global logarithmic ledger.
