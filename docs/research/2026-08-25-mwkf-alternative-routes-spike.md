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

### 4.4 Exact reduction to five fixed resonance slopes

There is no need to leave the minimizing integer in (4.17) implicit.
For every positive \(r,s\), write uniquely

\[
 r-s=js+w,\qquad -\frac{s}{2}<w\le\frac{s}{2}.
\tag{4.37}
\]

At an even-modulus tie the representative \(w=s/2\) is selected.  On an
admissible term this tie cannot occur for \(s>2\), since
\((s,w)=1\) but \((s,s/2)=s/2\).  The exact identities are

\[
 r=(j+1)s+w,\qquad
 (r,s)=(s,w),\qquad
 \Delta_s(r-s)=|w|,
\tag{4.38}
\]

and, for every integer \(a\),

\[
 e\left(\frac{a(r-s)}s\right)-1
 =e\left(\frac{aw}s\right)-1.
\tag{4.39}
\]

In the balanced support \(R=S\), the dyadic inequalities imply
\(1/4\le r/s\le4\).  Since \(-1/2<w/s\le1/2\), (4.37) forces exactly

\[
 j\in\{-1,0,1,2,3\}.
\tag{4.40}
\]

For a shell (4.29), define \(\mathfrak F_{q,j}(D)\) by the completely
finite sum

\[
\begin{aligned}
 \mathfrak F_{q,j}(D)
 :={}&
 \sum_{\substack{S/2\le s\le2S,\quad
                  w\in\mathbb Z,\quad D<|w|\le2D\\
                  -s/2<w\le s/2\\
                  R/2\le (j+1)s+w\le2R\\
                  (s,w)=1\\
                  (q,s((j+1)s+w))=1\\
                  qs,\ q((j+1)s+w)\le N}}
 \mu(s)\mu((j+1)s+w)\\
 &\quad\times
 p_N(qs)p_N(q((j+1)s+w))\frac Ss\\
 &\quad\times
 \sum_{a\ne0}\Lambda_{(j+1)s+w,s}(a)
 \left\{e\left(\frac{aw}s\right)-1\right\}.
\end{aligned}
\tag{4.41}
\]

Finite reindexing by (4.37), with no estimate and no discarded endpoint,
gives

\[
 \boxed{
 \mathfrak D_{q,D}^{(2)}
 =\sum_{j=-1}^{3}\mathfrak F_{q,j}(D).}
\tag{4.42}
\]

Thus FRSD\(_B\) is reduced to at most five sums whose two Möbius
arguments are the fixed linear forms

\[
 s,\qquad (j+1)s+w,
 \qquad j+1\in\{0,1,2,3,4\}.
\tag{4.43}
\]

Moreover, if \(D<R/4\), the \(j=-1\) sector is empty: (4.38) would give
\(r=w\), while \(|w|\le2D<R/2\), contradicting the \(r\)-support in
(4.41).  Hence every submaximal hard-box shell with \(D<R/4\) requires
only the four slopes \(1,2,3,4\).  The helper
centered_resonance_coordinates verifies the unique representative, both
endpoint values of \(j\), the coprimality transfer, and the phase
congruence over finite integer fixtures.

This is a structural reduction, not the missing cancellation estimate.
The coefficient in (4.41) still varies jointly with \(s,w,a\), and the
centered absolute-value savings before the primitive-fraction refinement
below are exactly those in (4.34).

### 4.5 Pre-completion Kloosterman-fraction form

The fixed-slope coordinates simplify the original inverse phase as well.
From (4.38) and \((s,w)=1\),

\[
 \overline{(j+1)s+w}\equiv\bar w\pmod s.
\tag{4.44}
\]

Use \(\delta_0\) for the original shifted-divisor variable, to distinguish
it from the distance exponent \(\delta\) in (4.34).  Before either finite
completion, define

\[
\begin{aligned}
 \mathfrak G_{q,j}(D)
 :={}&
 \sum_{\substack{S/2\le s\le2S,\quad
                  w\in\mathbb Z,\quad D<|w|\le2D\\
                  -s/2<w\le s/2\\
                  R/2\le (j+1)s+w\le2R\\
                  (s,w)=1,\quad(q,s((j+1)s+w))=1\\
                  qs,\ q((j+1)s+w)\le N\\
                  H/2\le|h|\le2H,\quad
                  L/2\le|\delta_0|\le2L}}
 \mu(s)\mu((j+1)s+w)\\
 &\quad\times p_N(qs)p_N(q((j+1)s+w))\\
 &\quad\times
 \Psi((j+1)s+w,s,h,\delta_0)
 e\left(-\frac{h\delta_0\bar w}{s}\right).
\end{aligned}
\tag{4.45}
\]

Here \(\Psi\) is exactly the coupled smooth box weight in the
pre-completion core; in particular no factor depending on
\((s,w,h,\delta_0)\) has been separated or replaced.  Linearity of finite
completion and (4.44) give the exact identities

\[
 \mathfrak S_{q,D}[\Psi]
 =\sum_{j=-1}^{3}\mathfrak G_{q,j}(D),
 \qquad
 \mathfrak S_{q,D}[\Psi]
 =\frac{HL}{S}\mathfrak D_{q,D}^{(2)}.
\tag{4.46}
\]

Thus (4.32) is equivalent to

\[
 \boxed{
 \left|\sum_{j=-1}^{3}\mathfrak G_{q,j}(D)\right|
 \ll_{B,W}RS\,\mathscr L^{-B}.}
\tag{4.47}
\]

For fixed \(j\), (4.45) has the standard Kloosterman-fraction phase with
the exact scale assignment

\[
 M_{\mathrm{inv}}=D,\qquad
 N_{\mathrm{mod}}=S,\qquad
 A_{\mathrm{num}}=HL.
\tag{4.48}
\]

At the hard box, let \(D=T^\delta\).  Even if the joint coefficient in
(4.45) is optimistically replaced by separated coefficients, the two
Bettin--Chandee terms and their deficit against the exponent-six target
in (4.47) are

\[
\begin{array}{c|c|c|c}
 \delta&\mathrm{BC}_1&\mathrm{BC}_2&
 \max(\mathrm{BC}_1,\mathrm{BC}_2)-6\\ \hline
 1&89/10&75/8&27/8\\
 3/2&363/40&153/16&57/16\\
 2&37/4&39/4&15/4\\
 5/2&387/40&163/16&67/16\\
 3&101/10&85/8&37/8.
\end{array}
\tag{4.49}
\]

All deficits are positive.  Moreover, the optimistic coefficient
replacement is not valid: both
\(\mu((j+1)s+w)\) and \(\Psi((j+1)s+w,s,h,\delta_0)\) couple the inverse
and modulus variables.  The exact-rational function
inverse_resonance_bcr_scales records (4.48)--(4.49).  Consequently direct
Bettin--Chandee treatment covers no far-resonance shell; a successful
argument must use the two Möbius weights before replacing coefficients by
their \(L^2\) norms.

### 4.6 An unconditional primitive-fraction large-sieve improvement

The inverse fractions in (4.45) have a feature absent from the completed
product fractions \(a/s\).  Since \((s,w)=1\), the fraction
\(\bar w/s\) is reduced.  If two shell pairs give the same point modulo
one, then

\[
 \frac{\overline{w_1}}{s_1}
 \equiv\frac{\overline{w_2}}{s_2}\pmod1,
\tag{4.50}
\]

uniqueness of reduced fractions first gives \(s_1=s_2\) and equality of
the inverse residues; inversion and the centered representative in
(4.37) then give \(w_1=w_2\).  Thus there is no fraction multiplicity.
For distinct points with \(s_1,s_2\le2S\),

\[
 \left\|
 \frac{\overline{w_1}}{s_1}
 -\frac{\overline{w_2}}{s_2}
 \right\|
 \ge\frac1{s_1s_2}\ge\frac1{4S^2}.
\tag{4.51}
\]

Apply the smooth separation (6.5) of the exact-audit note to (4.45).
For one separated component, grouping \(n=h\delta_0\) produces the
coefficient \(\nu(n)\) with

\[
 \operatorname{supp}\nu\subset\{HL\le|n|\le4HL\},
 \qquad
 \sum_n|\nu(n)|^2\ll_{\varepsilon,W}(HL)^{1+\varepsilon}.
\tag{4.52}
\]

The number of \((s,w)\) pairs in a shell is \(O(SD)\).  Cauchy--Schwarz,
(4.51), and the additive large sieve give

\[
\begin{aligned}
 |\mathfrak G_{q,j}(D)|
 &\ll_{\varepsilon,W}\mathscr L^{C_{\rm sep}}
 (SD)^{1/2}
 \left\{
 \sum_{\substack{s\asymp S\\D<|w|\le2D\\(s,w)=1}}
 \left|\sum_n\nu(n)e\left(-\frac{n\bar w}s\right)\right|^2
 \right\}^{1/2}\\
 &\ll_{\varepsilon,W}
 \mathscr L^{C_{\rm sep}}
 (SD)^{1/2}(HL+S^2)^{1/2}(HL)^{1/2+\varepsilon}.
\end{aligned}
\tag{4.53}
\]

All mollifier, Möbius, coprimality, and endpoint factors have modulus at
most one in this application.  The separated continuous twists do not
alter either the spacing or the \(L^2\) norm; integrating them costs only
the displayed \(\mathscr L^{C_{\rm sep}}\).  Hence (4.53) is an
unconditional estimate for the actual coupled box, not a new conjectural
adapter.

At the hard box, (4.53) has exponent

\[
 7+\frac{\delta}{2}.
\tag{4.54}
\]

Combining it with the centered absolute bound (4.31), multiplied by the
completion prefactor \(HL/S=T^2\), yields

\[
\begin{array}{c|c|c|c}
 \delta&\text{centered bound}&\text{large-sieve bound}
   &\text{best remaining saving against }T^6\\ \hline
 1&6&15/2&0\\
 3/2&7&31/4&1\\
 2&8&8&2\\
 5/2&17/2&33/4&9/4\\
 3&9&17/2&5/2.
\end{array}
\tag{4.55}
\]

Equivalently, the positive-power part of the missing fixed-slope estimate
is reduced from (4.34) to

\[
 \boxed{
 g_{\rm residual}(\delta)=
 \begin{cases}
 2\delta-2,&1\le\delta\le2,\\[1mm]
 1+\delta/2,&2\le\delta\le3.
 \end{cases}}
\tag{4.56}
\]

The improvement is strict for every \(\delta>2\); at the maximal shell it
reduces the missing saving from \(T^3\) to \(T^{5/2}\).  The function
primitive_fraction_large_sieve_scales records (4.51)--(4.56) and
explicitly fixes the fraction-multiplicity exponent at zero.

This still does not prove FRSD\(_B\): the shells
\(1<\delta\le3\) retain the positive deficits in (4.56), while the
\(\delta=1\) face needs the separate logarithmic gain already identified
in (4.35)--(4.36).

### 4.7 Reciprocity clustering at numerator resolution

For the large shells, additive reciprocity exposes more spacing structure.
After splitting the sign of \(w\), the exact identity is

\[
 -\frac{\bar w}{s}
 \equiv \frac{\bar s}{w}-\frac1{sw}\pmod1.
\tag{4.57}
\]

The first term is a reduced Farey fraction of denominator \(|w|\asymp D\).
The second term moves it by \(O((SD)^{-1})\).  Put \(A=HL\).  Whenever

\[
 SD\ge A,
\tag{4.58}
\]

the displacement in (4.57) is at most the numerator resolution \(A^{-1}\).
A fixed reduced center \(\bar s/w\) determines \(w\), its sign, and one
residue class for \(s\bmod |w|\); hence it has

\[
 O(1+S/D)=O(S/D)
\tag{4.59}
\]

preimages in the present range.  The reduced centers have spacing
\(\gg D^{-2}\).  Therefore an interval of length \(O(A^{-1})\) contains
at most

\[
 O\left(\frac SD\left(1+\frac{D^2}{A}\right)\right)
\tag{4.60}
\]

actual frequencies \(-\bar w/s\).

The local-density form of the additive large sieve follows by partitioning
the frequency multiset into \(O((4.60))\) subsets separated by
\(\gg A^{-1}\).  Together with (4.52), it gives

\[
 \sum_{\substack{s\asymp S\\D<|w|\le2D\\(s,w)=1}}
 \left|\sum_n\nu(n)e\left(-\frac{n\bar w}s\right)\right|^2
 \ll_{\varepsilon,W}
 \frac SD(A+D^2)A^{1+\varepsilon}.
\tag{4.61}
\]

Applying outer Cauchy over the \(O(SD)\) shell pairs and restoring the
separation integral proves the unconditional bound

\[
 \boxed{
 |\mathfrak G_{q,j}(D)|
 \ll_{\varepsilon,W}
 \mathscr L^{C_{\rm sep}}
 S(HL+D^2)^{1/2}(HL)^{1/2+\varepsilon},
 \qquad SD\ge HL.}
\tag{4.62}
\]

At the hard box condition (4.58) is exactly \(\delta\ge2\), and (4.62)
has exponent

\[
 \begin{cases}
 8,&2\le\delta\le5/2,\\
 11/2+\delta,&5/2\le\delta\le3.
 \end{cases}
\tag{4.63}
\]

Combining (4.62) with both estimates used in (4.55) gives the new current
minimum

\[
\begin{array}{c|c|c|c}
 \delta&\text{centered}&\text{primitive LS}
   &\text{reciprocity-cluster best / remaining saving}\\ \hline
 2&8&8&8\ /\ 2\\
 5/2&17/2&33/4&8\ /\ 2\\
 3&9&17/2&17/2\ /\ 5/2.
\end{array}
\tag{4.64}
\]

Consequently (4.56) is sharpened to

\[
 \boxed{
 g_{\rm residual}^{\rm current}(\delta)=
 \begin{cases}
 2\delta-2,&1\le\delta\le2,\\[1mm]
 2,&2\le\delta\le5/2,\\[1mm]
 \delta-1/2,&5/2\le\delta\le3.
 \end{cases}}
\tag{4.65}
\]

The exact-rational function reciprocal_cluster_large_sieve_scales checks
the applicability condition (4.58), the multiplicity \(S/D\), the Farey
spacing \(D^{-2}\), and every exponent in (4.62)--(4.65).

This estimate is again unconditional, but it does not close FRSD\(_B\):
the current remaining power is \(g_{\rm residual}^{\rm current}(\delta)\)
for every \(\delta>1\), with maximum \(5/2\) at \(\delta=3\).

### 4.8 Endpoint-aware logarithmic collar

The two mollifier tapers enlarge the logarithmic collar on the genuine
top endpoint.  Assume the exact constant-scale conditions

\[
 \frac N4\le qR\le N,\qquad
 \frac N4\le qS\le N.
\tag{4.66}
\]

For every retained \(r,s\) with \(qr,qs\le N\), (2.12) gives

\[
 |p_N(qr)p_N(qs)|
 \le \frac{(\log 8)^2}{(\log N)^2}
 \ll \mathscr L^{-2}.
\tag{4.67}
\]

Keeping (4.67), rather than replacing both factors by one, upgrades
(4.21) to

\[
 |\mathfrak D_{q,\mathrm{near}}^{(2)}(D)|
 \ll_W (CV)^2D^2\mathscr L^{-2}.
\tag{4.68}
\]

For \(B>7\), define the endpoint-aware cutoff

\[
 D_{B,\mathrm{end}}
 :=\left(\frac{R}{CV}\right)^{1/2}
   \mathscr L^{-(B-2)/2}.
\tag{4.69}
\]

Equations (4.68)--(4.69) give

\[
 \boxed{
 |\mathfrak D_{q,\mathrm{near}}^{(2)}(D_{B,\mathrm{end}})|
 \ll_W RCV\,\mathscr L^{-B}.}
\tag{4.70}
\]

Thus this enlarged collar contributes
\(O_W(T\mathscr L^{7-B})=o_W(T)\) after the current global aggregation.
At the hard endpoint and the first integer gate \(B=8\),

\[
 D_{8,\mathrm{end}}=T\mathscr L^{-3},
\tag{4.71}
\]

compared with \(T\mathscr L^{-4}\) in (4.28).

The full power collar \(D=T\) is not covered by this observation alone.
Putting \(D=(R/(CV))^{1/2}\) in (4.68) gives only
\(RCV\mathscr L^{-2}\).  Against the present seven-logarithm aggregation,
the exact global margin is

\[
 2-7=-5.
\tag{4.72}
\]

Even under the optimistic application of the
Matomäki--Radziwiłł--Tao factor (4.35), the remaining shortfall for the
local \(B=8\) gate is

\[
 8-2-\frac1{3000}=\frac{17999}{3000};
\tag{4.73}
\]

the actual joint coefficient obstruction from Section 4.1 remains as
well.  Hence the endpoint tapers enlarge the rigorously covered collar by
one logarithmic power in \(D\), but do not prove the whole
\(\delta=1\) face.

The exact-rational function endpoint_centered_resonance_log_budget checks
the two endpoint power faces
\(\kappa+\rho=\kappa+\sigma=3\), the two taper logarithms, (4.69), and
the negative full-collar margin (4.72).  Certification still requires the
constant-scale hypotheses (4.66), which are not encoded by exponent data
alone.

### 4.9 Exact endpoint-critical aggregation ledger

The seven-logarithm ledger in (2.7) is deliberately uniform over the
whole core.  A sharp count on the full \(D=T\) power barrier must also
retain the dependence on \(q\).  This corrects the tempting but false
replacement of the \(q\)-sum by a harmonic logarithm after applying the
centered absolute bound.

At the pure logarithmic power face one has

\[
 \kappa=0,qquad \rho=\sigma=3,qquad
 k+\sigma=m+\rho,qquad
 h=\sigma-m,qquad \ell=m+\rho-1.
\tag{4.74}
\]

The condition \(\kappa=0\) is essential.  If \(q=T^\kappa\) with
\(\kappa>0\), then \(R=S=T^{3-\kappa}\), while \(CV=T\), and the
full collar \(D=T\) has the positive-power deficit \(T^\kappa\).

For the logarithmic refinement put

\[
 x:=\frac{HM}{S},\qquad y:=\frac{TL}{MR},qquad
 q\le\mathscr L^\gamma,qquad (xy)^{-1}\le\mathscr L^\beta,
 \qquad \beta,\gamma\ge0.
\tag{4.75}
\]

In addition, impose both exact endpoint conditions (4.66), the fixed
ratio window (5.7) of the exact-audit note, and polylogarithmic upper and
lower bounds on \(x,y\).  For each fixed \(q\), the endpoint conditions
leave \(O(1)\) dyadic choices for \(R,S\).  Ratio balance fixes \(K\)
from \(M,R,S\), and the logarithmic neighborhoods for \(x,y\) contain
\(O(\log\log T)\) dyadic choices each.  The \(M\)-sum remains genuine:
for \(R=S\), the line

\[
 0\le m=k\le\frac12,qquad h=3-m,qquad \ell=2+m
\tag{4.76}
\]

satisfies (4.74), and \(HL\asymp xyRS/T\).

The decisive normalization is as follows.  Equations (4.21) and (4.67)
give

\[
 |\mathfrak D^{(2)}_{q,D=T}|
 \ll_W (CV)^2T^2\mathscr L^{-2}.
\tag{4.77}
\]

Since \(HL/S\asymp xyR/T\), \(CV\asymp T/(xy)\),
\(qR\asymp T^3\), and the outer normalization is
\(2T/(qRS)\), one box contributes

\[
 \boxed{
 |\mathcal O^{\ne0}_{q;R,S,K,M,L,H}(D=T)|
 \ll_W T(xy)^{-1}\mathscr L^{-2}
 \ll_W T\mathscr L^{\beta-2}.}
\tag{4.78}
\]

The factor \(1/q\) from the desired local gate has disappeared in
(4.78).  Consequently the \(q\)-aggregation is cardinal, not harmonic.
Summing \(q\le\mathscr L^\gamma\), the genuine \(M\)-dyadic family, and
the two logarithmic frequency collars gives

\[
 \boxed{
 \mathcal R_{D=T}(\beta,\gamma)
 \ll_{W,B_0}
 T\mathscr L^{\beta+\gamma-1}(\log\log T)^2.}
\tag{4.79}
\]

Thus the endpoint absolute bound already proves \(o(T)\) on every fixed
subface \(\beta+\gamma<1\).  At \(\beta+\gamma=1\), the remaining
\((\log\log T)^2\) prevents little-oh.  The exact-rational function
endpoint_critical_aggregation_budget records (4.74)--(4.79), including
the cardinal \(q\)-sum and the strict inequality.

### 4.10 Improved averaged-Chowla subface

Menon, arXiv:2607.15574v1, Theorem
`improved_avg_chowla`, proves for Liouville correlations, with the paper
explicitly noting the analogous Möbius statement, the error factor

\[
 \frac{\log\log H}{\log H}
 +\frac{(\log\log X)^2}{\log X}.
\tag{4.80}
\]

For \(H=T\) and \(X\asymp T^3\), (4.80) is
\(O(\mathscr L^{-1}(\log\mathscr L)^2)\).  This improves the earlier
\(\mathscr L^{-1/3000}\) factor in (4.35).  If it could be applied to
the completed centered family before taking absolute values in the
frequency variables, (4.79) would become

\[
 \mathcal R_{D=T}^{\rm Menon}(\beta,\gamma)
 \ll T\mathscr L^{\beta+\gamma-2}
       (\log\mathscr L)^4,
\tag{4.81}
\]

and hence would close every fixed subface

\[
 \boxed{0\le\beta+\gamma<2.}
\tag{4.82}
\]

Equation (4.82) is conditional routing for the unit-slope sector, not
current MWKF coverage.  For the other fixed slopes, a weaker statement
does follow from Menon's stated exponential-sum theorem by an
elementary fixed-slope square-root transfer, as follows.

Let

\[
 E(X,H):=\frac{\log\log H}{\log H}
 +\frac{(\log\log X)^2}{\log X}.
\tag{4.83}
\]

Theorem `improved_exp_sum`, its stated Möbius analogue, the inequality
\(|Z|^2\le H|Z|\) for an \(H\)-term sum, and the Fourier identity quoted
in Menon's proof give, for a dyadically supported Möbius sequence \(f\),

\[
 \sum_{|w|\le H/2}
 \left|\sum_n f(n)\overline{f(n+w)}\right|^2
 \ll E(X,H)HX^2.
\tag{4.84}
\]

Indeed, if \(A_f(\alpha)\) is the integrated squared short exponential
sum, then
\(\sup_\alpha A_f(\alpha)\ll E(X,H)H^2X\) and
\(\int_{\mathbb T}A_f(\alpha)d\alpha\ll HX\).  Their product bounds the
fourth-moment side of the Fourier identity, and
\((2H-|w|)^2\gg H^2\) on \(|w|\le H/2\), proving (4.84).

For a fixed \(k\in\{1,2,3,4\}\), put

\[
 f_k(n):=\mathbf1_{k\mid n}\,\mu(n/k),\qquad g(n):=\mu(n).
\tag{4.85}
\]

Short exponential sums of \(f_k\) reduce, after \(n=km\), to those of
\(\mu(m)\) on intervals of length \(H/k\); uniformity in the additive
frequency absorbs the dilation by \(k\).  For
\(B_w(F,G)=\sum_nF(n)\overline{G(n+w)}\), the exact polarization identity

\[
 4B_w(f_k,g)=\sum_{a=0}^3 i^a
 B_w(f_k+i^ag,f_k+i^ag)
\tag{4.86}
\]

and (4.84), applied termwise using the triangle inequality for the two
short exponential sums, prove

\[
 \sum_{|w|\le H/2}
 \left|\sum_s\mu(s)\mu(ks+w)\right|
 \ll_k E(X,H)^{1/2}HX.
\tag{4.87}
\]

Thus the fixed-slope transfer is proved from the exponential-sum theorem,
but it supplies only
\(E^{1/2}\ll\mathscr L^{-1/2}\log\mathscr L\).  For all four sectors,
the conditional range furnished by this black-box transfer is therefore

\[
 \boxed{0\le\beta+\gamma<\frac32,}
\tag{4.88}
\]

while (4.82) remains available for the unit-slope sector alone.

To turn these correlation estimates into an MWKF estimate, it remains at
this point to control the completion weight by bounded variation.  The
required weight is

\[
 (s,w)\longmapsto
 \Theta_{(j+1)s+w,s}(c,v)
 \left\{e\left(\frac{cvw}{s}\right)-1\right\}
\tag{4.89}
\]

whose summed separation norm may cost \((1+x+y)^2\), but Section 4.11
shows that this cost is amortized by the same box's \(xy\)-gain and loses
no new positive power of \(\mathscr L\).  Section 4.12 then
Möbius-inverts the coprimality condition in \((s,w)\) and proves the
required uniform estimate for the resulting \(q,d\)-restricted Möbius
functions.

The function improved_averaged_chowla_shell_audit records the unit-slope
margin \(2-\beta-\gamma\) and the all-sector margin
\(3/2-\beta-\gamma\).  Section 4.11 supplies the bounded-variation step
for the smooth completion coefficient, and Section 4.12 supplies the
remaining arithmetic uniformity.  Thus the strict subface (4.88) is
covered.  Full published coverage remains false because
\(\beta+\gamma\ge3/2\), the positive-power far shells, and the transform
tail remain.  Apart from the bounded-zeta endpoint subfaces proved in
Sections 4.25 and 4.28 below, \(q=T^\kappa\), \(\kappa>0\), boxes remain
positive-power cells rather than part of this logarithmic adapter.

### 4.11 Finite Fourier bounded-variation separation

The symmetric completion has an exact lifted formula which is better
suited to weighted correlation estimates than the collapsed coefficient
\(\Lambda_{r,s}(a)\).  From (15.1)--(15.3) of the coefficient-first note,
orthogonality and the definition of the periodization give, for every
integer representatives \(c,v\),

\[
 \boxed{
 \Theta_{r,s}(c,v)
 =\frac1{HL}\sum_{h,\delta\in\mathbb Z}
 \Phi_{r,s}(h,\delta)
 e\!\left(-\frac{ch+v\delta}{s}\right).}
\tag{4.90}
\]

The sum is finite because \(\Phi\) is compactly supported.  Formula
(4.90) is exact even before using \(H,L<s\); periodization simply groups
the same finite set of integers by their residue classes.

Fix a slope \(k=j+1\in\{1,2,3,4\}\), put \(s=Sz\), \(w=Du\), and define

\[
 \mathcal B_{c,v}(z,u):=
 \Theta_{kSz+Du,Sz}(c,v)
 \left\{e\!\left(\frac{cvDu}{Sz}\right)-1\right\}.
\tag{4.91}
\]

The fixed dyadic cutoffs are included in \(\Phi\).  Recall

\[
 x=\frac{HM}{S},\qquad y=\frac{TL}{MR},\qquad
 P:=1+x+y.
\tag{4.92}
\]

Differentiate the explicit normalized kernel (5.13b).  The fixed support
ratios and square-root denominator have bounded normalized derivatives;
the exact \(t\)-phase costs at most \(1+y\), and the \(h\)-Fourier phase
costs at most \(1+x\).  Derivatives of the AFE weight are harmless because
\(Z^aV_t^{(a)}(Z)\ll_{a,A}(1+Z/T)^{-A}\).  Consequently, for
\(a,b\in\{0,1\}\), finite summation by parts in (4.90) gives, for every
fixed \(A>6\),

\[
 \left|\partial_z^a\partial_u^b
 \Theta_{kSz+Du,Sz}(c,v)\right|
 \ll_{A,W}P^{a+b}
 \left(1+\frac{|c|}{C}\right)^{-A}
 \left(1+\frac{|v|}{V}\right)^{-A}.
\tag{4.93}
\]

When a \(z\)-derivative hits the finite Fourier phase it introduces
\(|c|/C+|v|/V\); lowering \(A\) by two absorbs these factors.  A
\(u\)-derivative through \(r=kSz+Du\) costs \(D/R\le1\), already absorbed
in (4.93).

On the logarithmic hard face the centered phase has a full power of
slack:

\[
 \frac{CVD}{S}=T^{-1+o(1)}.
\tag{4.94}
\]

Thus throughout the effective frequency range, every normalized first or
mixed derivative of the braces in (4.91) is
\(O(|cv|D/S)\).  Combining this with (4.93), the two-dimensional
Hardy--Krause norm on the fixed \((z,u)\)-rectangle satisfies

\[
 \|\mathcal B_{c,v}\|_{\rm HK}
 \ll_{A,W}\frac{|cv|D}{S}P^2
 \left(1+\frac{|c|}{C}\right)^{-A+2}
 \left(1+\frac{|v|}{V}\right)^{-A+2}.
\tag{4.95}
\]

The elementary one-dimensional estimates

\[
 \sum_{n\in\mathbb Z}|n|
 \left(1+\frac{|n|}{Y}\right)^{-A+2}
 \ll_A Y^2\qquad(Y>0)
\tag{4.96}
\]

For \(0<Y\le1\), this follows from
\((1+n/Y)^{-A+2}\le(Y/n)^{A-2}\) and \(A>6\); for \(Y\ge1\), split at
\(n=Y\).  Thus (4.96) also covers endpoint boxes with \(C<1\) or \(V<1\).
Applying it in the two frequency coordinates gives the required summed separation
norm

\[
 \boxed{
 \sum_{c,v}\|\mathcal B_{c,v}\|_{\rm HK}
 \ll_W\frac{D}{S}(CV)^2(1+x+y)^2.}
\tag{4.97}
\]

The omitted effective-frequency tails are not a new hypothesis.  Choosing
the summation-by-parts order in (4.93) arbitrarily large makes their total
in (4.97) \(O_A(\mathscr L^{-A})\) relative to the displayed scale, so
after all box and \(q\)-sums they are \(o(T)\).

It remains to check that the factor \(P^2\) does not silently consume the
Menon saving.  Write \(x=\mathscr L^\xi\),
\(y=\mathscr L^\upsilon\).  The mixed BV derivative costs

\[
 2\max(0,\xi,\upsilon),
\tag{4.98}
\]

whereas the same box already contributes the gain \(\xi+\upsilon\) from
\(xy\).  Hence its net BV depth is

\[
 b_{\rm BV}=2\max(0,\xi,\upsilon)-\xi-\upsilon.
\tag{4.99}
\]

If \(\xi,\upsilon\le0\), this is exactly the original frequency depth
\(-\xi-\upsilon\).  If \(\xi=\upsilon>0\), it is zero: the derivative
cost exactly spends the positive \(xy\)-gain.  Finally, if
\(\max(\xi,\upsilon)>0\) and \(\xi\ne\upsilon\), the two terms in the
coupled physical \(X\)-phase have unequal logarithmic size.  For opposite
signs their difference is bounded below by the larger scale; for equal
signs they add.  Repeated integration by parts in \(X\) therefore gives
an arbitrary fixed negative power of \(\mathscr L\), removing that box.

This proves that (4.97) introduces no additional logarithmic depth on the
retained phase regimes.  Rectangular partial summation then transfers the
fixed-slope correlation bound (4.87) through the actual smooth completion
coefficient.  In particular, the former joint
base--shift--frequency dependence is no longer an analytic obstruction.

One arithmetic interface remains.  The correlation still contains

\[
 \mu(s)\mu(ks+w)\mathbf1_{(s,w)=1}
 \mathbf1_{(q,s(ks+w))=1}.
\tag{4.100}
\]

Section 4.12 Möbius-inverts \((s,w)=1\), truncates the resulting common
divisor with its \(d^{-2}\) volume weight, and proves Menon's fixed-slope
transfer uniformly for the resulting polylogarithmic \(qd\)-restricted
Möbius functions.  No completed smooth coefficient remains in that
interface.  The exact-rational function
completion_weight_bv_audit records (4.94) and (4.98)--(4.99), explicitly
distinguishing preservation of the raw \((CV)^2\) moment from preservation
of the global logarithmic depth.

### 4.12 Coprimality and polylogarithmic character twists

Put

\[
 \mu_Q(n):=\mu(n)\mathbf1_{(n,Q)=1}.
\tag{4.101}
\]

For \(r=ks+w>0\), ordinary Möbius inversion of \((s,w)=1\) gives the
exact finite identity

\[
\boxed{
 \mu_q(s)\mu_q(ks+w)\mathbf1_{(s,w)=1}
 =\sum_{\substack{d\mid s,\ d\mid w\\(d,q)=1}}
 \mu(d)\mu_{qd}(s/d)
 \mu_{qd}(ks/d+w/d).}
\tag{4.102}
\]

To verify (4.102), terms with nonsquarefree \(d\) vanish.  For squarefree
\(d\) coprime to \(q\), write \(s=dn\), \(w=du\).  Then

\[
 \mu_q(dn)=\mu(d)\mu_{qd}(n),\qquad
 \mu_q(d(kn+u))=\mu(d)\mu_{qd}(kn+u),
\tag{4.103}
\]

and \(\mu(d)^2=1\).  Summing \(\mu(d)\) over common divisors is exactly
\(\mathbf1_{(s,w)=1}\).  The finite helper
coprime_centered_mobius_reindex verifies (4.102) over exhaustive bounded
fixtures, including \(w=0\) and \((d,q)>1\); the displayed proof is the
general argument.

After \(s=dn\), \(w=du\), the base and shift lengths are \(S/d\) and
\(D/d\).  Hence the trivial two-dimensional correlation volume carries
the exact factor

\[
 \frac{SD}{d^2}.
\tag{4.104}
\]

For \(Y=\mathscr L^{A_0}\), absolute summation therefore gives

\[
 \sum_{d>Y}\frac{SD}{d^2}
 \ll \frac{SD}{Y}
 =SD\mathscr L^{-A_0}.
\tag{4.105}
\]

The same bound holds with the BV norm (4.97), because dilation by \(d\)
does not enlarge normalized \((n,u)\)-derivatives.  The exponent \(A_0\)
is arbitrary and fixed, so this tail is \(o(T)\) after the complete
polylogarithmic aggregation.

On \(d\le Y\) and \(q\le\mathscr L^\gamma\), the modulus in (4.102)
satisfies

\[
 qd\le\mathscr L^{\gamma+A_0}.
\tag{4.106}
\]

Moreover

\[
 \mu_{qd}(n)=\mu(n)\chi_{0,qd}(n),
\tag{4.107}
\]

where \(\chi_{0,qd}\) is the principal Dirichlet character modulo \(qd\).
Menon's character-twisted short-interval theorem is uniform for character
modulus at most \((\log X)^B\), for every fixed \(B\), and the paper states
that its Liouville argument carries over to Möbius.  Running the proof of
improved_exp_sum with (4.107) changes only the major arcs: there the
principal character is multiplied by a character of modulus at most
\(\mathscr L^{20}\), so the product still has modulus
\(\mathscr L^{\gamma+A_0+20}\).  The character-twisted theorem applies
after enlarging the fixed parameter \(B\).  The minor-arc proof uses only
one-boundedness and is unchanged.  Thus (4.80), and consequently the
fixed-slope transfer (4.87), hold uniformly for every function
\(\mu_{qd}\) occurring in (4.102).

Combining (4.97), (4.102), (4.105), and this uniform twisted transfer
proves

\[
 \boxed{
 \mathcal R_{D=T}(\beta,\gamma)
 =o(T)\qquad\text{for every fixed }\beta+\gamma<\frac32.}
\tag{4.108}
\]

For the unit-slope sector alone, the direct averaged-Chowla theorem gives
the larger strict range \(\beta+\gamma<2\).  Equality in either boundary
is not included because the displayed powers of \(\log\mathscr L\) remain.
The exact-rational function coprimality_restricted_menon_audit records the
\(d^{-2}\) volume, the \(\mathscr L^{-A_0}\) tail, the modulus exponent
\(\gamma+A_0\), and the strict all-sector margin
\(3/2-\beta-\gamma\).

### 4.13 Prime-factor trace twists do not pay the far-shell deficit

There is a second way to exploit the Möbius weight before a spectral
Cauchy inequality, but its published exponent is too small.  Suppose a
prime \(p\) divides the squarefree modulus \(s\), write \(s=pt\), and fix
one resonance slope \(r=ks+w\).  The exact CRT identity is

\[
 \frac{n\bar r}{pt}
 \equiv
 \frac{n\overline{rt}}p+
 \frac{n\overline{rp}}t
 \pmod1.
\tag{4.109}
\]

For \(p\nmid n\), the first factor in the exponential of (4.109), as a
function of \(r\), is the bounded-conductor nonexceptional rational
inverse trace weight

\[
 r\longmapsto e\!\left(-\frac{n\overline{rt}}p\right).
\tag{4.110}
\]

On a shell \(|w|\asymp D\), the variable \(r\) lies in an interval of
length \(D\).  The smoothed Möbius estimate of
Fouvry--Kowalski--Michel, arXiv:1211.6043v3, Theorem 1.7, states, for
every \(\eta<1/24\),

\[
 \sum_r\mu(r)K(r)V(r/D)
 \ll Q_VD(1+p/D)^{1/6}p^{-\eta}.
\tag{4.111}
\]

Write \(D=T^\delta\) and \(p=T^\pi\).  Ignoring the Sobolev factor
\(Q_V=T^{o(1)}\), the exact one-sided power saving in (4.111) is

\[
 \boxed{
 s_{\rm FKM}(\delta,\pi;\eta)
 =\left(\eta\pi-\frac{(\pi-\delta)_+}{6}\right)_+.}
\tag{4.112}
\]

Because \(\eta<1/6\), (4.112) increases up to \(\pi=\delta\) and
decreases afterwards.  Even granting a prime factor of exactly that
size and granting an independent application to each Möbius weight, the
total saving is strictly less than

\[
 2\eta\delta<\frac\delta{12}.
\tag{4.113}
\]

Subtracting the optimistic supremum (4.113) from the current residual
function (4.65) leaves

\[
 \begin{cases}
  23\delta/12-2,&1<\delta\le2,\\
  2-\delta/12,&2\le\delta\le5/2,\\
  11\delta/12-1/2,&5/2\le\delta\le3.
 \end{cases}
\tag{4.114}
\]

In particular the maximal shell still lacks \(T^{9/4+o(1)}\).  With
the admissible rational choice \(\eta=1/25\), two completely optimistic
applications save only \(T^{6/25}\), leaving the exact deficit

\[
 \frac52-\frac6{25}=\frac{113}{50}.
\tag{4.115}
\]

This is already a rejection under stronger hypotheses than the actual
sum satisfies.  A general squarefree \(s\) need not have a prime factor
in the selected dyadic band; the second factor in (4.109) remains a
joint cofactor-dependent weight; and frequencies \(p\mid n\) make the
\(p\)-trace constant.  Thus (4.111) is not itself an adapter for the
MWKF coefficient.  The exact-rational function
prime_factor_trace_twist_audit records all three failures as well as
(4.112)--(4.115).

### 4.14 Linear completion after the Type-I divisor expansion

The completed phase suggests a more elementary Type-I attack which must
also retain the original squarefree support.  Expand

\[
 c_U(a)=\sum_{d\mid a,\ d\le U}\mu(d),\qquad a=de,
 \qquad r=dbe.
\tag{4.116}
\]

For a fixed shell \(|r-ks|\asymp D\), the long quotient \(e\) lies in
an interval of length

\[
 Y=\frac{D}{db}.
\tag{4.117}
\]

The finite completion has ordinary linear phase

\[
 e\!\left(\frac{cv\,db\,e}{s}\right),
\tag{4.118}
\]

not an inverse phase in \(e\).  The double-zero-sum identity for
\(\Theta_{r,s}(c,v)\) removes the centered \(-1\) only after the full
\((c,v)\)-sum is retained.  Thus (4.118) is a legitimate entry point,
but replacing the \(e\)-coefficient by one is not: the exact support
still includes

\[
 \mu^2(dbe)=1,\qquad (dbe,sq)=1.
\tag{4.119}
\]

Write \(D=T^\delta\), \(db=T^\tau\), and let \(Q\) be the reduced
denominator in (4.118).  Since \((db,s)=1\), only \(cv\) can cancel a
factor of \(s\).  At the hard box \(|cv|\ll T\) and \(s\asymp T^3\),
so

\[
 Y=T^{\delta-\tau},\qquad Q\ge \frac{S}{CV}=T^2.
\tag{4.120}
\]

Schlage--Puchta, arXiv:1105.1616v1, Theorem 3, proves at a reduced
rational point \(A/Q\)

\[
 \sum_{e\le Y}\mu^2(e)e(Ae/Q)
 \ll_\varepsilon
 Y^\varepsilon\left(\frac YQ+Y^{1/2}+Q\right).
\tag{4.121}
\]

Smooth dyadic intervals follow by partial summation and subtraction of
two initial intervals.  Optimizing the exponent on the right of (4.121)
over every \(Q\) allowed by (4.120), and then taking the minimum with
the trivial bound \(Y\), gives

\[
 \operatorname{exp}_T |(4.121)|
 =\min(\delta-\tau,2),
\qquad
 s_{\rm sqfree}(\delta,\tau)
 =(\delta-\tau-2)_+.
\tag{4.122}
\]

Consequently, on the maximal shell \(\delta=3\), this route saves
\(T^{1-\tau}\) only for \(\tau<1\).  At and beyond the exact transition

\[
 \boxed{\tau=u+\beta\ge1,}
\tag{4.123}
\]

the published squarefree exponential-sum estimate gives no power saving
at all.  The allowed Type-I factor boxes have
\(0\le u,\beta\le1\), so (4.123) is a genuine two-dimensional residual
region, not an endpoint.  Even the favorable \(\tau=0\) box saves only
one power and leaves two of the original three powers missing.

This audit is optimistic in one further direction: it has not charged
the Möbius inversions needed for \((e,dbsq)=1\).  Therefore it can reject
the route but cannot certify coverage of a favorable subbox.  The
function squarefree_linear_completion_audit records (4.120)--(4.123)
and marks the coprimality progressions as uncharged.

### 4.15 Hecke--Möbius Euler product and the missing spectral adapter

Suppose first that an unramified Hecke--Maaß eigenform \(f\) has local
standard factor

\[
 L_p(z,f)^{-1}=1-\lambda_f(p)p^{-z}+\omega_f(p)p^{-2z}.
\tag{4.124}
\]

The local factor of the formal Möbius--Hecke Dirichlet series is exactly

\[
 D_{f,p}(z)=1-\lambda_f(p)p^{-z}.
\tag{4.125}
\]

Consequently, initially in the half-plane of absolute convergence and
with the ramified primes recorded separately,

\[
 D_f(z):=\sum_{n\ge1}\frac{\mu(n)\lambda_f(n)}{n^z}
 =\frac{H_f(z)}{L(z,f)},
\qquad
 H_{f,p}(z)
 =\frac{1-\lambda_f(p)p^{-z}}
 {1-\lambda_f(p)p^{-z}+\omega_f(p)p^{-2z}}.
\tag{4.126}
\]

In particular,

\[
 H_{f,p}(z)-1
 =-\frac{\omega_f(p)p^{-2z}}
 {1-\lambda_f(p)p^{-z}+\omega_f(p)p^{-2z}}.
\tag{4.127}
\]

Thus the Euler-factor identity itself is not the missing step.  The
exact-rational function `hecke_mobius_local_factor` records
(4.124)--(4.127).

The geometric-to-spectral passage is missing.  Knightly--Li, arXiv:1202.0189, Theorem 7.14,
inserts one fixed Hecke index \(n\) into a Kuznetsov formula: the
cuspidal side contains
\(\lambda_n(f)a_{m_1}(f)\overline{a_{m_2}(f)}\), while the geometric side
contains generalized twisted Kloosterman sums
\(S_{\omega'}(m_2,m_1;n;c)\).  Linearity in \(n\) would formally create
one Möbius--Hecke polynomial after summing those formulas against
\(\mu(n)\).  What has not been proved is an identity between that
geometric family and the QCT kernel in (2.3), or a transform which sends
both weights \(\mu(r)\mu(s)\) to two such Hecke polynomials.  In the QCT
kernel \(r,s\) are determinant-matrix entries and moduli, not already
the two Fourier indices of the classical Kuznetsov formula.

There is a second, independent obstruction.  Let \(X=T^\rho\) be the
length of a putative Möbius--Hecke polynomial and let a fixed contour
shift have width \(\eta_T\).  A saving \((\log T)^{-B}\) requires the
necessary displacement inequality

\[
 \boxed{\eta_T\log X\ge B\log\log T.}
\tag{4.128}
\]

If the spectral analytic conductor has polynomial size
\(\mathfrak C_f=T^\kappa\), the classical width
\(\eta_T\asymp1/\log\mathfrak C_f\) gives only
\(\eta_T\log X\asymp\rho/\kappa\), a constant.  Thorner, arXiv:2608.12257v1, Theorem 1.1,
proves a uniform but ineffective region of width
\(c_\varepsilon\mathfrak C_f^{-\varepsilon}\).  For every fixed
\(\varepsilon>0\) and \(\kappa>0\), this gives

\[
 \eta_T\log X
 \ll_{\varepsilon,\rho,\kappa}
 T^{-\kappa\varepsilon}\log T=o(1),
\tag{4.129}
\]

so it does not supply the required logarithmic saving in (4.128) for a
polynomial-conductor spectral family.  Allowing \(\varepsilon\) to
depend on \(T\) is not licensed because the theorem's constant depends
on \(\varepsilon\).  A successful route must therefore derive the
actual QCT spectral family and then use a family-average cancellation or
zero-density statement strong enough at its verified conductor; an
individual zero-free-region substitution is insufficient.

The audit records all three gates separately: local Euler identity true,
QCT spectral derivation false, and uniform logarithmic saving false.
Published coverage remains false.

### 4.16 Exact determinant orbit: the Hecke index is the shift

The pre-completion determinant equation has the matrix form

\[
 M=\begin{pmatrix}r&j\\s&v\end{pmatrix},
 \qquad \det M=rv-js=\delta.
\tag{4.130}
\]

Since \((r,s)=1\), reduction modulo the lower-left entry gives

\[
 rv\equiv\delta\pmod s,\qquad
 v\equiv\delta\bar r\pmod s,
\tag{4.131}
\]

and hence the original reciprocal phase becomes the exact linear orbit
phase

\[
 e\!\left(-\frac{h\delta\bar r}{s}\right)
 =e\!\left(-\frac{hv}{s}\right).
\tag{4.132}
\]

At level one, write the generalized Kloosterman orbit as

\[
 S(m_2,m_1;n;s)
 =\sum_{\substack{d,d'\bmod s\\dd'\equiv n\pmod s}}
 e\!\left(\frac{dm_2+d'm_1}{s}\right).
\tag{4.133}
\]

The exact substitution

\[
 (d,d',n,m_2,m_1)=(r,v,\delta,0,-h)
\tag{4.134}
\]

turns (4.133) into \(S(0,-h;\delta;s)\) and reproduces (4.132).
Therefore, in the Knightly--Li trace formula, the Hecke-operator index is
the shift \(\delta\).  It is not either of the two Möbius variables:
\(\mu(r)\) weights a residue-matrix entry, while \(\mu(s)\) weights the
Kloosterman modulus.  The QCT coefficient contains no factor
\(\mu(\delta)\).

The current kernel is also not the unweighted complete orbit (4.133).
It has the dyadic restrictions on \(r,v\), the coupled smooth kernel,
the mollifier tapers and \(q\)-coprimality, and the modulus weight
\(\mu(s)\).  Consequently, linearly superposing the Knightly--Li formula
over its Hecke index would insert a new weight \(\mu(\delta)\); it would
not transform either existing Möbius weight into a Hecke polynomial.

This is an invariant obstruction to the naive spectral adapter, not an
obstruction to every trace-formula approach.  A viable spectral route
would need a finite-place test function or a relative trace formula whose
geometric side itself carries the entry weight \(\mu(r)\) and modulus
weight \(\mu(s)\), followed by a family estimate before a positive
Parseval diagonal is created.  No published theorem establishing that
adapter is currently registered, so published coverage remains false.

### 4.17 Fixed-modulus completion and the 2026 bilinear bounds

The preceding orbit identity suggests completing the \(r\)-sum before
using the two long Möbius weights.  To give this route its most favorable
literal interpretation, first separate the \(r\)-coordinate of the
coupled kernel.  For fixed \(s\), let

\[
 F_s(r)=\mu(r)p_N(qr)U(r/R)
\tag{4.135}
\]

denote the resulting coefficient, with all fixed Mellin twists absorbed
into \(U\), and define

\[
 \widehat F_s(m)=\sum_rF_s(r)e\!\left(-\frac{mr}{s}\right).
\tag{4.136}
\]

Finite Fourier orthogonality gives the exact identity

\[
 \boxed{
 \sum_{\substack{r\\(r,s)=1}}
 F_s(r)e\!\left(-\frac{h\delta\bar r}{s}\right)
 =
 \frac1s\sum_{m\bmod s}\widehat F_s(m)
 S(-h\delta,m;s).}
\tag{4.137}
\]

The full additive Fourier range \(m\bmod s\) is present; smoothness of
the original \(r\)-cutoff does not shorten it because \(F_s\) contains
\(\mu(r)\).  Since \(R\asymp S\), each residue class meets the
\(r\)-interval only \(O(1)\) times, and Parseval gives

\[
 \|\widehat F_s\|_2^2
 =s\sum_{x\bmod s}
 \left|\sum_{r\equiv x\bmod s}F_s(r)\right|^2
 \ll sR.
\tag{4.138}
\]

At the hard box this norm has exponent \(3\), while the smooth
\(h\)-coefficient has \(L^2\)-exponent \(5/4\).

Fix \((\delta,s)\) and grant the unverified favorable conditions
\((\delta,s)=1\) and \((h,s)=1\) on the first bilinear variable.
Blomer--Pascadi, arXiv:2607.24311v1, Theorem 5.7,
applied to \(S(-\delta h,m;s)\) with

\[
 c=s=T^3,\qquad M=H=T^{5/2},\qquad N=s=T^3,
\tag{4.139}
\]

has dimensionless factor

\[
 \max\left\{
 \frac{(MN)^{1/2}}{c^{3/4}},
 \frac{N^{1/2}}{c^{1/2}},
 \frac{M^{1/2}}{c^{1/4}}
 \right\}
 =T^{1/2}.
\tag{4.140}
\]

Thus the fixed-\((\delta,s)\) bound before the \(s^{-1}\) completion
factor has exponent

\[
 3+\frac54+3+\frac12=\frac{31}{4}.
\tag{4.141}
\]

Charging \(s^{-1}\), then summing the \(T^{5/2}\) shifts and the
\(T^3\) moduli, gives the optimistic global bound

\[
 T^{31/4}\,T^{-3}\,T^{5/2}\,T^3
 =T^{41/4+o(1)}.
\tag{4.142}
\]

It saves only \(11-41/4=3/4\) over the original cardinal exponent
\(11\).  The CK target is \(T^{5999/1000}\), so even this optimistic
application leaves the exact deficit

\[
 \boxed{\frac{41}{4}-\frac{5999}{1000}
 =\frac{4251}{1000}.}
\tag{4.143}
\]

This termwise published-theorem insertion is not the best bound available
after (4.137).  Aggregate the product coefficient modulo \(s\):

\[
 A_s(a)=
 \sum_{\substack{h\asymp H,\ \delta\asymp L\\
                  h\delta\equiv a\pmod s}}
 U(h/H)V(\delta/L).
\tag{4.143a}
\]

Its squared norm counts solutions of

\[
 h\delta-h'\delta'=ks,\qquad |k|\ll 1+\frac{HL}{s}.
\tag{4.143b}
\]

For fixed \((h,\delta,k)\) with nonzero
\(n=h\delta-ks\), the number of allowed pairs
\((h',\delta')\) is at most \(\tau(|n|)\).  The case \(n=0\) contributes
nothing because \(h'\delta'\ne0\) on the dyadic support.  Hence

\[
 \sum_{a\bmod s}|A_s(a)|^2
 \ll_\varepsilon
 HL\left(1+\frac{HL}{s}\right)T^\varepsilon
 \ll T^{7+\varepsilon}.
\tag{4.143c}
\]

The Kloosterman matrix has the exact operator factor \(s\).  Indeed it
is a product of two unnormalised finite Fourier transforms and the
permutation \(x\mapsto\bar x\) on the unit residues; equivalently,

\[
 \sum_{m\bmod s}S(a,m;s)\overline{S(a',m;s)}
 =s\,c_s(a-a').
\tag{4.143d}
\]

Combining (4.138), (4.143c), and this operator norm, then charging the
\(s^{-1}\) in (4.137) and summing the \(T^3\) moduli, gives the stronger
unconditional estimate for the separated coefficient model

\[
 T^{7/2}\,T^3\,T^3\,T^{-3}\,T^3
 =T^{19/2+\varepsilon}.
\tag{4.143e}
\]

This saves \(T^{3/2}\) from the cardinal exponent, but it still leaves

\[
 \boxed{\frac{19}{2}-\frac{5999}{1000}
 =\frac{3501}{1000}}
\tag{4.143f}
\]

above CK.  Thus exact Kloosterman orthogonality, rather than the
termwise 2026 theorem, is the best registered estimate for this
completion; neither one closes the gate.

The newer normalized-Kloosterman estimate of
Milićević--Qin--Wu, arXiv:2511.07550v1, Theorem 1.1, is not directly
available in this range.  Its hypothesis \(M^{7/5}N<q^{3/2}\) becomes

\[
 T^{13/2}>T^{9/2},
\tag{4.144}
\]

with a fixed two-power violation.  Splitting the full \(m\bmod s\)
range into shorter intervals would require recombining \(T^2\) or more
pieces and does not follow from the displayed theorem without a new
square-function estimate for the query-dependent coefficients.

Equations (4.137)--(4.144) already favor the published theorems: the
actual kernel has not been separated, neither \((\delta,s)=1\) nor
\((h,s)=1\) is global,
and the surviving outer coefficient is \(\mu(s)\) with
query-dependent coprimality and tapers.  Hence this route neither proves
the coupled gate nor provides a direct published adapter.  Any successful
fixed-modulus completion must retain the \(\delta\)- and \(s\)-averages
inside a genuinely trilinear or dispersion estimate rather than apply
the current bilinear theorem separately.

### 4.18 Exact Linnik-centering audit: the existing minus one is not the diagonal subtraction

The second option listed after (4.3) needs one further distinction.  For
fixed \((r,s)\), put

\[
 Z(\Theta):=-\sum_{\substack{c\ne0\ (s)\\v\ne0\ (s)}}
                  \Theta_{r,s}(c,v).
\tag{4.145}
\]

The zero row and zero column identities imply, with no estimate,

\[
 \sum_{\substack{c\ne0\ (s)\\v\ne0\ (s)}}
       \Theta_{r,s}(c,v)=\Theta_{r,s}(0,0),
 \qquad
 Z(\Theta)=-\Theta_{r,s}(0,0).
\tag{4.146}
\]

Thus the exact completed amplitude is

\[
 \mathcal L_{r,s}(\Theta)
 =\sum_{\substack{c\ne0\ (s)\\v\ne0\ (s)}}
   \Theta_{r,s}(c,v)
   \left\{e\left(\frac{rcv}{s}\right)-1\right\}.
\tag{4.147}
\]

Both terms in (4.147) are linear in \(\Theta\).  In particular, for every
\(z\in\mathbb C\),

\[
 Z(z\Theta)=zZ(\Theta),
 \qquad
 \mathcal L_{r,s}(z\Theta)=z\mathcal L_{r,s}(\Theta).
\tag{4.148}
\]

The Parseval identity diagonal is instead

\[
 E(\Theta):=
 sum_{c,v\bmod s}|\Theta_{r,s}(c,v)|^2,
 \qquad
 E(z\Theta)=|z|^2E(\Theta).
\tag{4.149}
\]

Consequently the minus-one term in (4.147) cannot be identified with an
explicit subtraction of (4.149): the two quantities have different
homogeneity.  This is an algebraic obstruction, not an insufficient
estimate.  The role of the minus one is exactly to remove the additive
Fourier zero mode.

More generally, a finite Linnik square has the exact expansion

\[
 \begin{aligned}
 \mathcal V
 &:=\sum_\xi\left|\sum_j a_jK_\xi(j)\right|^2
   =\mathcal D+\mathcal O,\\
 \mathcal D
 &:=\sum_j|a_j|^2\sum_\xi|K_\xi(j)|^2,\\
 \mathcal O
 &:=\sum_{j\ne k}a_j\overline{a_k}
       \sum_\xi K_\xi(j)\overline{K_\xi(k)}.
 \end{aligned}
\tag{4.150}
\]

Here \(\mathcal O\) is signed, whereas \(\mathcal V\ge0\).  Subtracting
\(\mathcal D\) *after* Cauchy--Schwarz and estimating
\(\mathcal V-\mathcal D=\mathcal O\) does not bound the positive quantity
on the Cauchy right-hand side: it remains
\(\mathcal V=\mathcal D+\mathcal O\).  A dispersion proof below the
identity-diagonal scale must therefore take one of the following two
precise forms:

1. before Cauchy, replace the amplitude by an exact projected residual
   whose own identity diagonal already has the required logarithmic
   saving; or
2. retain the sign of \(\mathcal O\) and prove the cancellation
   \[
     \boxed{\mathcal O=-\mathcal D+
       O_{B,W}\!\left(\mathcal D(\log(2T))^{-B}\right)}.
   \tag{4.151}
   \]

At the hard box,

\[
 R=T^3,qquad C=V=T^{1/2},qquad RCV=T^4.
\tag{4.152}
\]

The normalized Parseval diagonal and the logarithmic local gate therefore
both have power exponent \(4\), while global aggregation consumes seven
logarithms.  Hence (4.151), or the amplitude-level alternative, must hold
with \(B>7\).  Replacing (4.151) by
\(\mathcal O\ll\mathcal D(\log T)^{-B}\) is insufficient and must be
rejected: it leaves the full \(\mathcal D\) term.

This audit does not disprove every Linnik-dispersion route.  It rejects
the naive identification of the existing centered minus one with the
quadratic diagonal and fixes the exact missing local condition.  No
published estimate proving (4.151) for the two Möbius weights and the
coupled kernel has been identified.  The exact-rational record is
`linnik_dispersion_centering_audit`; it preserves
`published_coverage=False`.

### 4.19 Exact determinant-line form of the surviving two-Möbius average

There is an exact one-dimensional parametrization of every fiber in
\(\mathrm{MD}_{2501/1000}\).  Isolate signed dyadic boxes

\[
 |j|\asymp J,\qquad |v|\asymp V,\qquad
 |\delta|\asymp L,
 \qquad J=V=T^{1/2},\quad L=T^{5/2}.
\tag{4.153}
\]

Put

\[
 g=(|j|,|v|),\qquad j=gj_0,qquad v=gv_0,qquad
 (j_0,v_0)=1.
\tag{4.154}
\]

The determinant equation has a solution only if \(g\mid\delta\).  Write
\(\delta=g\delta_0\).  Then

\[
 rv_0-sj_0=\delta_0.
\tag{4.155}
\]

For any one particular integral solution \((r_0,s_0)\), all integral
solutions of (4.155), with no omission or multiplicity, are

\[
 \boxed{r_n=r_0+j_0n,qquad s_n=s_0+v_0n,qquad n\in\mathbb Z.}
\tag{4.156}
\]

Define the exact coupled line weight

\[
 \mathcal W_{q,g,j_0,v_0,\delta_0}(n)
 :=p_N(qr_n)p_N(qs_n)
   \widehat\Psi_h(r_n,s_n,g\delta_0,gv_0),
\tag{4.157}
\]

including in \(\widehat\Psi_h\) all original dyadic cutoffs and the full
transform phase.  Reindexing (4.8av) by (4.154)--(4.156) gives the finite
identity

\[
\boxed{
\begin{aligned}
 \mathfrak M_q(J,V,L)
 ={}&\sum_{g\ge1}
 \sum_{\substack{|j_0|\asymp J/g,\ |v_0|\asymp V/g\\
                   (j_0,v_0)=1}}
 \sum_{|\delta_0|\asymp L/g}
 \sum_{\substack{n:\ r_n,s_n\asymp T^3\\
                   (r_n,s_n)=1,\ (q,r_ns_n)=1}}
 \mu(r_n)\mu(s_n)
 \mathcal W_{q,g,j_0,v_0,\delta_0}(n).
\end{aligned}}
\tag{4.158}
\]

Thus a fixed determinant fiber is not a single Möbius sum.  It is the
two-affine-form correlation

\[
 \mu(r_0+j_0n)\mu(s_0+v_0n)
\tag{4.159}
\]

with growing primitive slopes and a query-dependent coupled weight.

The coprimality in (4.158) also has an exact one-variable form.  Every
common divisor of \(r_n,s_n\) divides (4.155), hence divides
\(\delta_0\).  For every squarefree \(d\mid\delta_0\), coprimality of
\(j_0,v_0\) gives a unique residue \(\nu_d\bmod d\) for which
\(d\mid r_n\) and \(d\mid s_n\).  Therefore

\[
 \boxed{
 \mathbf1_{(r_n,s_n)=1}
 =\sum_{d\mid\delta_0}\mu(d)
   \mathbf1_{n\equiv\nu_d\ (d)}.}
\tag{4.160}
\]

This leaves \((q,r_ns_n)=1\) explicit.  For every prime \(p\mid q\),
each of the two linear congruences is either empty, one residue modulo
\(p\), or identically zero; in the last case the retained fiber is empty.

Write \(g\asymp T^\gamma\), \(0\le\gamma\le1/2\).  The exact exponent
ledger of (4.158) is

\[
 \begin{array}{c|c}
 \text{variable family}&\log_T\text{-scale}\ \\ \hline
 g&\gamma\\
 j_0,v_0&1/2-\gamma\quad\text{each}\\
 \delta_0&5/2-\gamma\\
 n&\min\{3-(1/2-\gamma),3-(1/2-\gamma)\}
       =5/2+\gamma.
 \end{array}
\tag{4.161}
\]

Consequently the complete \(g\)-layer has cardinality exponent

\[
 \gamma+2(1/2-\gamma)+(5/2-\gamma)+(5/2+\gamma)
 =6-\gamma.
\tag{4.162}
\]

The global gate remains \(T^{3499/1000}\).  Hence the exact local saving
required on this layer is

\[
 \boxed{
 s_{\rm line}(\gamma)
 =6-\gamma-\frac{3499}{1000}
 =\frac{2501}{1000}-\gamma,
 \qquad 0\le\gamma\le\frac12.}
\tag{4.163}
\]

It ranges from \(2501/1000\) at \(g\asymp1\) to
\(\frac{2001}{1000}\) at \(g\asymp T^{1/2}\).  Thus extracting a large common divisor never
reduces the problem to a merely logarithmic estimate.

The averaged-Chowla inputs used in Sections 4.10--4.12 cannot establish
(4.163).  Their conclusions save logarithms, whereas every layer in
(4.163) requires a fixed positive power.  Moreover, the proven transfer
there is for fixed slopes, while \(j_0,v_0\) in (4.161) grow up to
\(T^{1/2}\), and the weight (4.157) depends on the slopes, shift, and
line parameter simultaneously.  The determinant-line reindexing is
therefore an exact reduction, not a theorem adapter.

The remaining proposition can now be stated layerwise: uniformly for
all \(0\le\gamma\le1/2\), prove

\[
 \boxed{
 |\mathfrak M_q(G,J,V,L)|
 \ll_{B,W}T^{3499/1000}(\log(2T))^{-B},
 \qquad B>7,}
\tag{4.164}
\]

with the exact sum (4.158), the residue expansion (4.160), and the
coupled weight (4.157).  Equivalently, relative to cardinality, (4.164)
must save \(T^{s_{\rm line}(\gamma)}\).  This is recorded by
`determinant_line_mobius_audit`; no published positive-power estimate
matching its growing-slope and coupled-weight hypotheses is currently
registered.

### 4.20 Unimodular two-variable square-root gate and the small-\(g\) residual

The line form (4.156) has more algebraic structure than a general pair
of affine forms.  Choose Bezout coefficients \(x,y\in\mathbb Z\) with

\[
 xv_0+yj_0=1.
\tag{4.165}
\]

One may take the particular solution in (4.156) to be
\((r_0,s_0)=(x\delta_0,-y\delta_0)\).  Hence

\[
 \boxed{
 \begin{pmatrix}r\\s\end{pmatrix}
 =\begin{pmatrix}x&j_0\\-y&v_0\end{pmatrix}
  \begin{pmatrix}\delta_0\\n\end{pmatrix},
 \qquad
 \det\begin{pmatrix}x&j_0\\-y&v_0\end{pmatrix}=1.}
\tag{4.166}
\]

Thus \((\delta_0,n)\mapsto(r,s)\) is an exact unimodular change of
integer variables.  This does not separate the coupled transform weight,
but it identifies the natural two-dimensional square-root benchmark.

On the \(g=T^\gamma\) layer, (4.161) gives

\[
 \operatorname{vol}_{\delta_0,n}
 =T^{(5/2-\gamma)+(5/2+\gamma)}=T^5.
\tag{4.167}
\]

Accordingly, define the still unproved uniform fixed-slope gate

\[
\boxed{
 \mathrm{USR}_{B}(g,j_0,v_0):\quad
 \left|
  \sum_{\delta_0,n}
   \mu(x\delta_0+j_0n)\mu(-y\delta_0+v_0n)
   \mathcal W_{q,g,j_0,v_0,\delta_0}(n)
 \right|
 \ll_{B,W}T^{5/2}(\log(2T))^{-B}.}
\tag{4.168}
\]

The outer \(g,j_0,v_0\) cardinality has exponent

\[
 \gamma+2(1/2-\gamma)=1-\gamma.
\tag{4.169}
\]

Therefore cardinal summation of (4.168) gives

\[
 T^{1-\gamma}T^{5/2}=T^{7/2-\gamma}.
\tag{4.170}
\]

Comparison with the exact target \(T^{3499/1000}\) leaves the signed
margin

\[
 \boxed{
 \frac52-left(\frac{2501}{1000}-\gamma\right)
 =\gamma-\frac1{1000}.}
\tag{4.171}
\]

Consequently:

1. for \(\gamma>1/1000\), USR has fixed positive-power slack;
2. for \(\gamma=1/1000\), USR with a sufficiently large logarithmic
   saving reaches the gate;
3. for \(0\le\gamma<1/1000\), the exact remaining saving is
   \[
     T^{1/1000-\gamma},
   \tag{4.172}
   \]
   which must come from the primitive-slope average or from a stronger
   joint estimate.

This is a substantial narrowing of (4.163): a two-dimensional square
root in the unimodular inner box would settle every but the very small
common-gcd layer, and that residual asks for at most \(T^{1/1000}\) from
the two-dimensional primitive-slope family of cardinality
\(T^{1-2\gamma}\).  However, (4.168) is not a consequence of a standard
large sieve.  The two Möbius arguments are coordinate functions after
(4.166), while the thin determinant window and
\(\widehat\Psi_h\) remain coupled; applying Cauchy to either Möbius
coordinate recreates its full \(L^2\) diagonal.  No published theorem
establishing USR uniformly for \(|j_0|,|v_0|\le T^{1/2}\) is registered.

The exact-rational function `determinant_line_square_root_audit` records
(4.167)--(4.172), marks the square-root estimate unproved, and exposes
the small-\(g\) residual rather than treating USR as established.

### 4.21 Möbius progression variance: the published ranges do not prove USR

The primitive slopes in (4.168) suggest averaging Möbius sums in
arithmetic progressions.  The relevant published benchmark is the
Möbius Davenport--Halberstam formula

\[
 \boxed{
 \sum_{q\le Q}\sum_{a=1}^{q}|M(X;q,a)|^2
 =\frac6{\pi^2}XQ+O_A\!\left(X^2(\log X)^{-A}\right),}
\tag{4.173}
\]

where

\[
 M(X;q,a):=\sum_{\substack{n\le X\\n\equiv a\ (q)}}\mu(n).
\tag{4.174}
\]

The asymptotic in (4.173) is uniform in the range

\[
 X(\log X)^{-A}\le Q\le X.
\tag{4.175}
\]

This folklore Möbius analogue is given in Hooley, *On the
Barban--Davenport--Halberstam theorem III*, Theorem 2, and is reproved in
[Fan, *The Davenport--Halberstam theorem for Möbius
function*](https://math.dartmouth.edu/~stevefan/papers/The%20Davenport-Halberstam%20Theorem%20for%20Mobius%20Function.pdf).

For the determinant-line family,

\[
 X=T^3,qquad Q=T^{1/2-\gamma}.
\tag{4.176}
\]

The main and error exponents in (4.173) become

\[
 XQ=T^{7/2-\gamma},
 \qquad
 X^2(\log X)^{-A}=T^6(\log X)^{-A}.
\tag{4.177}
\]

Thus the error exceeds the variance main term by

\[
 \boxed{T^{5/2+\gamma}(\log X)^{-A},}
\tag{4.178}
\]

and the lower range condition (4.175) fails by the same fixed power
\(T^{5/2+\gamma}\).  Arbitrarily many logarithms cannot repair this
range failure for an asymptotic formula.

There is nevertheless a useful upper bound at small moduli.  The left
side of (4.173) is nonnegative and increases with \(Q\).  Given any
\(A>0\), apply (4.173) with

\[
 Q_1=X(\log X)^{-C},\qquad C>A+2.
\tag{4.181}
\]

For every \(Q\le Q_1\), positivity and (4.173) give

\[
 \boxed{
 \sum_{q\le Q}\sum_{a=1}^{q}|M(X;q,a)|^2
 \ll_A X^2(\log X)^{-A}.}
\tag{4.182}
\]

Thus at \(X=T^3\), the published *one-Möbius* variance does supply the
power-log scale

\[
 T^6(\log T)^{-A}
\tag{4.183}
\]

even though it supplies no small-\(Q\) asymptotic.  This distinction is
important for the slope square-function route below.

Granville--Shao,
[arXiv:1703.06865v2](https://arxiv.org/abs/1703.06865), Theorem 1.2,
does give a Bombieri--Vinogradov estimate for multiplicative functions in
the upper range \(Q\le X^{1/2-\varepsilon}\), after removing finitely many
exceptional character components.  At (4.176), its power-level margin is

\[
 \frac32-\left(\frac12-\gamma\right)=1+\gamma.
\tag{4.179}
\]

But that theorem bounds a one-function progression discrepancy with
logarithmic saving.  It does not permit the coefficient

\[
 \mu(-y\delta_0+v_0n)
 \mathcal W_{q,g,j_0,v_0,\delta_0}(n),
\tag{4.180}
\]

which depends jointly on the residue query, the second primitive slope,
the shift, and the line parameter.  Replacing (4.180) by an arbitrary
bounded coefficient invalidates the multiplicative-function theorem;
taking its absolute value destroys the first Möbius cancellation.  When
\(\gamma=1/2\), the primitive slopes are bounded and the lower modulus
range in Granville--Shao is not met; that endpoint instead belongs to the
fixed-slope logarithmic analysis of Sections 4.10--4.12.

Therefore neither published progression theorem proves USR.  The
function `mobius_progression_variance_audit` records the exact
\(5/2+\gamma\) Davenport--Halberstam range deficit, the
\(1+\gamma\) Granville--Shao upper-level margin, and the failure of the
second-Möbius/coupled-weight hypotheses.  It also records (4.182), so the
valid small-modulus upper bound is not discarded merely because the
asymptotic range fails.  It leaves
`published_coverage=False`.

### 4.22 Endpoint determinant slope square function and its positive diagonal

The preceding square-function idea needs a diagonal correction.  For
fixed \(g,j_0,v_0\), retain the exact signed inner sum

\[
\begin{aligned}
 \mathcal S_{q,g}(j_0,v_0)
 :={}&\sum_{|\delta_0|\asymp L/g}
 \sum_{\substack{n:\ r_n,s_n\asymp T^3\\
                   (r_n,s_n)=1,\ (q,r_ns_n)=1}}
 \mu(r_n)\mu(s_n)
 \mathcal W_{q,g,j_0,v_0,\delta_0}(n),
\end{aligned}
\tag{4.184}
\]

where \(r_n,s_n\) and \(\mathcal W\) are exactly (4.156)--(4.157),
including both mollifier tapers.  Expanding the positive square function
creates the identity diagonal

\[
 \mathcal D_g
 :=\sum_{j_0,v_0}\sum_{\delta_0,n}
 \mu(r_n)^2\mu(s_n)^2
 |\mathcal W_{q,g,j_0,v_0,\delta_0}(n)|^2.
\tag{4.185}
\]

For one fixed integer \(g\asymp T^\gamma\), the number of terms in
(4.185) has exponent

\[
 2(1/2-\gamma)+(5/2-\gamma)+(5/2+\gamma)
 =6-2\gamma.
\tag{4.186}
\]

In particular, at \(\gamma=0\), a nondegenerate kernel has a genuine
\(T^6\)-scale positive diagonal.  Therefore the previously proposed
bound \(T^6(\log T)^{-2B}\) for arbitrary \(B>0\) is impossible.  The
one-Möbius estimate (4.182) cannot be transferred with arbitrary
logarithmic saving to this two-Möbius square: its own identity diagonal
has the smaller scale \(XQ=T^{7/2-\gamma}\), whereas (4.185) already has
scale (4.186).

The correct hard-endpoint interface uses exactly the taper already
present in the problem.  Under

\[
 \frac N4\le qR\le N,
 \qquad
 \frac N4\le qS\le N,
\tag{4.187}
\]

(2.12) gives two logarithms in every amplitude and hence four in its
square.  The admissible endpoint proposition is

\[
\boxed{
 \mathrm{EDSSF}(g):\qquad
 \sum_{\substack{|j_0|\asymp J/g,\ |v_0|\asymp V/g\\
                   (j_0,v_0)=1}}
 |\mathcal S_{q,g}(j_0,v_0)|^2
 \ll_W T^6(\log(2T))^{-4}.}
\tag{4.188}
\]

At \(\gamma=0\), (4.188) is exactly the endpoint-weighted diagonal
scale, not a bound below it.  For \(\gamma>0\), the raw diagonal
(4.186) has additional power slack.

If \(g\asymp G=T^\gamma\), the number of primitive slope pairs satisfies

\[
 P_G\ll T^{1-2\gamma+o(1)}.
\tag{4.189}
\]

Cardinal summation in \(g\), followed by Cauchy in the complete signed
slope family, now gives

\[
\begin{aligned}
 \sum_{g\asymp G}\sum_{j_0,v_0}
 |\mathcal S_{q,g}(j_0,v_0)|
 &\le G P_G^{1/2}
 \sup_{g\asymp G}
 \left(\sum_{j_0,v_0}|\mathcal S_{q,g}(j_0,v_0)|^2\right)^{1/2}\\
 &\ll T^\gamma T^{1/2-\gamma}T^3
       (\log(2T))^{-2}\\
 &=T^{7/2}(\log(2T))^{-2}.
\end{aligned}
\tag{4.190}
\]

The exact endpoint aggregation ledger in Section 4.9 loses one
logarithm, so (4.190) leaves \((\log T)^{-1}\) and gives \(o(T)\) on the
hard endpoint.  This conclusion uses (4.187); it is not a general
nonendpoint gate.

For comparison, ordinary character orthogonality still gives the useful
finite identity

\[
\begin{aligned}
 \sum_{q\le Q}\sum_{a=1}^q|M(X;q,a)|^2
 ={}&\lfloor Q\rfloor\sum_{n\le X}\mu(n)^2\\
 &+2\sum_{1\le d<X}\tau_Q(d)
       \sum_{n\le X-d}\mu(n)\mu(n+d),
\end{aligned}
\tag{4.191}
\]

where \(\tau_Q(d)=\sum_{q\mid d,\ q\le Q}1\).  It explains why the
one-Möbius theorem reaches the coarse power \(T^6\), but it does not
prove EDSSF: the latter has two Möbius coordinates in each copy,
cross-slope pairs, determinant-line residue conditions, and two coupled
transform kernels.  The remaining endpoint theorem is precisely the
diagonal-scale estimate (4.188), with no fictitious extra logarithmic
saving.

The adapter `determinant_slope_square_function_audit` records the raw
diagonal exponent \(6-2\gamma\), the four squared taper logarithms, the
one-logarithm endpoint aggregation loss, and the resulting positive net
logarithm.  It explicitly sets
`arbitrary_log_saving_below_diagonal_requested=False`, while
`square_function_estimate_proved=False` and `published_coverage=False`
remain unchanged.

### 4.23 Cross-determinant expansion of EDSSF

The square in (4.188) can be split without discarding either Möbius
factor.  For two copies of the inner coordinates in (4.184), put

\[
 \delta_i=r_i v_0-s_i j_0,
 \qquad
 \Delta_{12}=r_1s_2-r_2s_1
 \quad(i=1,2).
\tag{4.192}
\]

Here, on one fixed dyadic \(g\asymp T^\gamma\) endpoint box,

\[
 \begin{gathered}
 |j_0|,|v_0|\asymp T^{1/2-\gamma},
 \qquad (j_0,v_0)=1,\\
 |\delta_i|\asymp T^{5/2-\gamma},
 \qquad |n_i|\ll T^{5/2+\gamma},\\
 r_i,s_i\asymp T^3,
 \qquad (r_i,s_i)=1,
 \qquad (q,r_is_i)=1,
 \end{gathered}
\tag{4.193}
\]

and \((r_i,s_i)\) is the exact affine-line solution attached to
\((j_0,v_0,\delta_i,n_i)\) in (4.156).  With
\(\mathcal W_i=\mathcal W_{q,g,j_0,v_0,\delta_i}(n_i)\), finite
expansion gives the identity

\[
 \sum_{j_0,v_0}|\mathcal S_{q,g}(j_0,v_0)|^2
 =\mathcal D_g+\mathcal O_g,
\tag{4.194}
\]

where \(\mathcal D_g\) is (4.185) and

\[
 \mathcal O_g=
 \sum_{\substack{j_0,v_0,\delta_1,n_1,\delta_2,n_2\\
                   \text{all conditions in (4.193)}\\
                   \Delta_{12}\ne0}}
 \mu(r_1)\mu(s_1)\mu(r_2)\mu(s_2)
 \mathcal W_1\overline{\mathcal W_2}.
\tag{4.195}
\]

There is no omitted proportional off-diagonal in (4.195).  Indeed,
if \(\Delta_{12}=0\), positivity makes the two primitive pairs
\((r_i,s_i)\) proportional by a positive rational number, and
primitivity forces \((r_1,s_1)=(r_2,s_2)\).  For the fixed primitive
slope, (4.192) then also forces \(\delta_1=\delta_2\), and the affine
parameterization forces \(n_1=n_2\).  Thus \(\Delta_{12}=0\) is exactly
the identity diagonal.

For \(\Delta_{12}\ne0\), Cramer's rule gives the exact inverse

\[
 v_0=\frac{\delta_1s_2-\delta_2s_1}{\Delta_{12}},
 \qquad
 j_0=\frac{\delta_1r_2-\delta_2r_1}{\Delta_{12}}.
\tag{4.196}
\]

Consequently, after eliminating \((j_0,v_0)\), the nonzero term is a
signed four-Möbius sum over the two primitive rows and two shifts,
subject to divisibility of both numerators in (4.196) by
\(\Delta_{12}\), coprimality of the two recovered quotients, and the
dyadic range in (4.193).  These are exact arithmetic conditions, not a
density heuristic.

The fraction collar is also explicit:

\[
 \frac{r_i}{s_i}-\frac{j_0}{v_0}
 =\frac{\delta_i}{s_iv_0}\ll T^{-1}.
\tag{4.197}
\]

Since \(s_1s_2\asymp T^6\), subtraction of the two instances of
(4.197) yields

\[
 0<|\Delta_{12}|\ll T^5.
\tag{4.198}
\]

The primitive-slope box has exponent \(1-2\gamma\), while each
\((\delta_i,n_i)\)-box has exponent \(5\).  Hence the expanded
off-diagonal cardinality is

\[
 (1-2\gamma)+2\cdot5=11-2\gamma.
\tag{4.199}
\]

The exact remaining endpoint proposition is therefore

\[
 \boxed{
 \mathrm{ODSF}(g):\qquad
 |\mathcal O_g|\ll_W T^6(\log(2T))^{-4}.}
\tag{4.200}
\]

It requires cancellation of exponent

\[
 (11-2\gamma)-6=5-2\gamma
\tag{4.201}
\]

from the ambient four-variable count.  Complete square-root
cancellation in (4.195) would have exponent
\((11-2\gamma)/2\), leaving the positive margin

\[
 6-\frac{11-2\gamma}{2}=\frac12+\gamma.
\tag{4.202}
\]

Equation (4.202) is only an exponent benchmark; no independence or
square-root theorem is asserted.  The identity diagonal is bounded at
the endpoint-weighted scale by (4.186)--(4.187), so ODSF would imply
EDSSF.  No cited result currently supplies (4.200) with its two coupled
rows, four Möbius factors, divisibility conditions (4.196), and the
transform weight \(\mathcal W_1\overline{\mathcal W_2}\).

The adapter `endpoint_slope_offdiagonal_audit` records the ambient
exponent \(11-2\gamma\), the required saving \(5-2\gamma\), the
cross-determinant range \(|\Delta_{12}|\ll T^5\), and the benchmark
margin \(1/2+\gamma\).  It leaves
`offdiagonal_estimate_proved=False` and `published_coverage=False`.

### 4.24 Smith normal form and the single cokernel character family

The two divisibility conditions in (4.196) must not be treated as two
independent congruences modulo \(\Delta_{12}\).  Put

\[
 B=
 \begin{pmatrix}
  r_1&-s_1\\
  r_2&-s_2
 \end{pmatrix},
 \qquad
 \boldsymbol\delta=
 \begin{pmatrix}\delta_1\\\delta_2\end{pmatrix},
 \qquad
 \boldsymbol u=
 \begin{pmatrix}v_0\\j_0\end{pmatrix}.
\tag{4.203}
\]

Then the two determinant equations are the single lattice equation

\[
 \boldsymbol\delta=B\boldsymbol u,
 \qquad \det B=-\Delta_{12}.
\tag{4.204}
\]

Every row \((r_i,s_i)\) is primitive.  Hence the gcd of all four
entries of \(B\) is one, which is the first Smith invariant.  Since the
product of the two Smith invariants is \(|\det B|\), one has the exact
normal form

\[
 \boxed{
 \operatorname{SNF}(B)=\operatorname{diag}(1,|\Delta_{12}|).}
\tag{4.205}
\]

In particular,

\[
 \mathbb Z^2/B\mathbb Z^2\simeq
 \mathbb Z/|\Delta_{12}|\mathbb Z,
 \qquad
 |B^{-T}\mathbb Z^2/\mathbb Z^2|=|\Delta_{12}|.
\tag{4.206}
\]

Let

\[
 \mathcal A_B=
 \left\{(a,b)\bmod |\Delta_{12}|:
 \begin{array}{l}
  ar_1+br_2\equiv0\pmod{|\Delta_{12}|},\\
  as_1+bs_2\equiv0\pmod{|\Delta_{12}|}
 \end{array}
 \right\}.
\tag{4.207}
\]

This annihilator has exactly \(|\Delta_{12}|\) elements.  Finite-group
orthogonality therefore gives, for every integral shift vector,

\[
 \boxed{
 \mathbf1_{\boldsymbol\delta\in B\mathbb Z^2}
 =\frac1{|\Delta_{12}|}
  \sum_{(a,b)\in\mathcal A_B}
  e\!\left(\frac{a\delta_1+b\delta_2}
                 {|\Delta_{12}|}\right).}
\tag{4.208}
\]

Formula (4.208) is exactly equivalent to integrality of both quotients
in (4.196).  It uses \(|\Delta_{12}|\) characters and the normalization
\(|\Delta_{12}|^{-1}\), not \(|\Delta_{12}|^2\) characters and
\(|\Delta_{12}|^{-2}\).  They are not two independent congruences: the
two Cramer divisibilities define one cyclic cokernel condition.  The
finite helper `determinant_cokernel_coordinates` exhaustively constructs
both the image residues and the annihilator and verifies that each has
cardinality \(|\Delta_{12}|\).

On the maximal shell (4.198), the cyclic character family has exponent
5.  Square-root cancellation in this family alone could save at most

\[
 T^{5/2}.
\tag{4.209}
\]

Against the ODSF requirement (4.201), that still leaves the exact
entry-side saving

\[
 (5-2\gamma)-\frac52=\frac52-2\gamma,
 \qquad 0\le\gamma\le\frac12.
\tag{4.210}
\]

It ranges from \(T^{5/2}\) at \(g\asymp1\) to \(T^{3/2}\) at
\(g\asymp T^{1/2}\).  Therefore Smith reduction removes a false second
character dimension, but it does not by itself prove ODSF.  The next
valid spectral interface is a hybrid character--entry estimate: retain
the single cyclic family (4.208), all four Möbius weights on the entries
of the two primitive rows, the recovered-slope cutoffs, and
\(\mathcal W_1\overline{\mathcal W_2}\), and obtain the residual saving
(4.210) after the character square root.  No published theorem checked in
this audit supplies that coupled estimate.

The adapter `endpoint_cokernel_character_audit` records the one Smith
invariant, the \(|\Delta_{12}|\)-element character family, the false
\(|\Delta_{12}|^2\) alternative, and the residual exponent
\(5/2-2\gamma\).  It leaves
`hybrid_character_entry_estimate_proved=False` and
`published_coverage=False`.

### 4.25 Unconditional large-q bounded-zeta endpoint

The boundary witness

\[
 (\rho,\sigma,m,k,\ell,h,\kappa)=(1,1,0,0,0,1,2)
\tag{4.211}
\]

does not require the Farey gate if the Poisson frequencies are regrouped
before taking an absolute value.  This subsection treats the exact
bounded-zeta family: \(K,M,L\asymp1\), \(R,S\asymp T\),
\(q\asymp T^2\), and

\[
 \frac N4\le qR,qS\le N.
\tag{4.212}
\]

Let

\[
 \mathcal U^{\ne0}_{q;R,S,K,M,L}
 :=\sum_H
 \mathcal O^{\ne0}_{q;R,S,K,M,L,H},
\tag{4.213}
\]

where the sum is over the complete smooth dyadic partition of all
\(h\ne0\).  It is essential that (4.213) is formed before an absolute
value.  Exact inverse Poisson summation says that (4.213) is the original
residue-class sum in \(m_2\), minus its \(h=0\) Poisson mode.

Before Poisson, the variables satisfy

\[
 m_1s-m_2r=\delta.
\tag{4.214}
\]

For fixed bounded \(m_1,m_2,\delta\), put
\(g=(m_1,m_2)\).  If \(g\nmid\delta\), (4.214) is empty.  Otherwise its
integer solutions form one affine line with step
\((m_1/g,m_2/g)\) in \((r,s)\).  In the dyadic rectangle
\(r\asymp R,s\asymp S\), with \(R\asymp S\), there are therefore

\[
 O_{K,M,L}(R)
\tag{4.215}
\]

solutions, uniformly in \(q\).  The original coefficient is
\(2/(q\sqrt{rs})\), the bounded \(m_1,m_2\) denominators cost only a
constant, and the height integral has absolute value \(O_W(T)\).
Consequently the pre-Poisson sum is

\[
 \ll_W \frac{T}{q}\,
 \sup_{r,s}|p_N(qr)p_N(qs)|.
\tag{4.216}
\]

The zero Poisson mode has the same bound directly from (4.4): for
\(h=0\), its kernel is \(O_W(T)\); the factor
\((q\sqrt{rs}\,s)^{-1}\) and the \(O(RS)\) pairs \((r,s)\) again give
\(O_W(T/q)\).  Thus subtracting the zero mode in (4.213) introduces no
larger term.

Under (4.212), each nonzero mollifier coefficient satisfies (2.12).
Using both endpoint factors in (4.216) gives the unconditional estimate

\[
 \boxed{
 |\mathcal U^{\ne0}_{q;R,S,K,M,L}|
 \ll_W\frac{T}{q}(\log(2T))^{-2}.}
\tag{4.217}
\]

Finally,

\[
 \sum_{q\asymp T^2}\frac1q\ll1,
\tag{4.218}
\]

and there are only \(O_{K,M,L}(1)\) bounded-zeta dyadic boxes.  Hence the
complete family (4.211)--(4.213) contributes

\[
 O_W\!\left(T(\log(2T))^{-2}\right)=o_W(T).
\tag{4.219}
\]

No Möbius cancellation, BCR estimate, or conjectural spectral input is
used.  The proof uses exact inverse Poisson, the elementary affine-line
count (4.215), the zero-mode bound, and the two endpoint tapers.  It does
not bound an individual \(H\)-box by (4.217); only their signed aggregate
(4.213) has been proved.

The route name is `covered_by_endpoint_unpoisson`.  The adapter
`large_q_endpoint_unpoisson_audit` records the exponent ledger

\[
 \underbrace{1}_{t\text{-integral}}
 +\underbrace{1}_{\text{shifted solutions}}
 -\underbrace{3}_{q\sqrt{RS}}
 =-1\quad\text{per }q,
 \qquad -1+2=1
\tag{4.220}
\]

after cardinal summation over \(q\asymp T^2\), together with the two
remaining logarithms.  It sets `unconditional_coverage=True`.

There is a precise polylogarithmic extension, but not coverage of the
whole exponent-zero cell.  Write \(K\asymp M\le\mathscr L^C\) and
\(L\le\mathscr L^\lambda\).  The elementary gcd average

\[
 \sum_{m_1\asymp K}\sum_{m_2\asymp M}(m_1,m_2)
 \ll KM\log(2\min\{K,M\})
\tag{4.221}
\]

combined with the factor \((m_1m_2)^{-1/2}\) shows that the weighted
version of (4.215), summed over \(m_1,m_2\), costs
\(O(R\log(2K)+K)\).  The bounded-zeta argument therefore gives, after
all polylogarithmic dyadic subdivisions,

\[
 \sum_q|\mathcal U^{\ne0}_{q;R,S,K,M,L}|
 \ll_W T\mathscr L^{\lambda-2}(\log\mathscr L)^{O_W(1)}.
\tag{4.222}
\]

Thus the strict logarithmic subface

\[
 \boxed{0\le\lambda<2}
\tag{4.223}
\]

is unconditionally \(o(T)\).  At \(\lambda=2\), the fixed positive
logarithmic margin vanishes, and the argument does not prove little-oh.
Since `ExponentBox` records only powers of \(T\), not \(\lambda\), the
global `route_box` deliberately does not promote the entire
`large_q_endpoint` exponent cell.  The direct
`endpoint_unpoisson_adapter` certifies (4.223) only after the shift log
depth is supplied explicitly.

### 4.26 q-first Euler factorization audit at the critical shift depth

It is tempting to include \(\lambda=2\) by summing \(q\) before applying
an averaged Möbius correlation theorem.  The Euler factorization below
is exact, but the final Menon step is invalid unless the original height
phase is retained.  This subsection records the useful arithmetic
identity and the obstruction; Section 4.28 gives the valid phase-based
coverage.  Insert a fixed smooth dyadic cutoff \(U(q/Q)\),
\(Q\asymp T^2\), and define

\[
 \mathcal Q_{r,s}(Q)
 :=\sum_{\substack{q\ge1\\(q,rs)=1}}
 \frac{\mu(q)^2}{q}U(q/Q)p_N(qr)p_N(qs).
\tag{4.224}
\]

The relevant Dirichlet series is exactly

\[
 \sum_{\substack{q\ge1\\(q,rs)=1}}
 \frac{\mu(q)^2}{q^{1+z}}
 =\frac{\zeta(1+z)}{\zeta(2+2z)}
  \prod_{p\mid rs}(1+p^{-1-z})^{-1}.
\tag{4.225}
\]

For \(Y=\log N\), set exactly

\[
 \mathcal A_{Q,U}(r,s):=
 \int_0^\infty U(x)
 \left(\log\frac{N}{Qrx}\right)_+
 \left(\log\frac{N}{Qsx}\right)_+\frac{dx}{x}.
\tag{4.226a}
\]

Apply Mellin inversion to the complete piecewise-smooth weight in
(4.226a), splitting its two possible endpoint orders along \(r=s\).
The Mellin contour may be shifted from \(\Re z>0\) to
\(\Re z=-1/4\).  Only the pole at \(z=0\) is crossed; the denominator
\(\zeta(2+2z)\) stays in \(\Re(2+2z)\ge3/2\).  Uniformly for
\(r,s\asymp T\), the residue gives

\[
 \mathcal Q_{r,s}(Q)
 =\frac{\mathfrak g(rs)}{\zeta(2)(\log N)^2}
   \mathcal A_{Q,U}(r,s)
 +O_{W,\varepsilon}(T^{-1/2+\varepsilon}),
\tag{4.226}
\]

Here \(\mathcal A_{Q,U}\) and its normalized first mixed variations are
uniformly bounded on each of the two endpoint-order regions, and

\[
 \boxed{
 \mathfrak g(n)=\prod_{p\mid n}\left(1+\frac1p\right)^{-1}.}
\tag{4.227}
\]

The error in (4.226), inserted into the absolute critical-shift count,
is \(O(T^{1/2+\varepsilon}\mathscr L^2)=o(T)\).  The local factors on
\(\Re z=-1/4\) cost only \(T^\varepsilon\), so this estimate is uniform
in the primitive pair.

Since the original support has \((r,s)=1\), (4.227) factors as
\(\mathfrak g(rs)=\mathfrak g(r)\mathfrak g(s)\).  Put

\[
 f(n):=\mu(n)\mathfrak g(n).
\tag{4.228}
\]

This is one fixed multiplicative function, independent of \(q\).  Its
Euler product has the exact factorization

\[
 \sum_{n\ge1}\frac{f(n)}{n^z}
 =\frac{H(z)}{\zeta(z)},
 \qquad
 H_p(z)=1+\frac1{p+1}\sum_{a\ge1}p^{-az}.
\tag{4.229}
\]

Equivalently,

\[
 \boxed{f=\mu*h,\qquad h(p^a)=\frac1{p+1}\quad(a\ge1),}
\tag{4.230}
\]

and, for every fixed \(\sigma>0\),

\[
 \sum_{n\ge1}\frac{|h(n)|}{n^\sigma}<\infty.
\tag{4.231}
\]

The finite helper functions `endpoint_q_density`,
`endpoint_density_convolution_coefficient`, and
`endpoint_weighted_mobius` verify (4.227)--(4.230) exactly on integer
fixtures; (4.231) follows from
\(\sum_p p^{-1-\sigma}<\infty\).

Truncating the two copies of \(h\) in (4.230) and the divisor expansion
of \(\mathbf1_{(r,s)=1}\) at a fixed integer \(D\) does leave fixed
arithmetic slopes when \(m_1,m_2\) are fixed.  It does **not** remove the
exact height phase

\[
 \exp\!\left(it\log\left(1+\frac{\delta}{m_2r}\right)\right)
 =\left(\frac{m_1s}{m_2r}\right)^{it}.
\tag{4.230a}
\]

The fixed-slope consequence (4.87) is an untwisted correlation estimate.
Smooth partial summation of \(\mathcal A_{Q,U}\) does not absorb
(4.230a), and deleting the phase changes the sum.  Thus the q-first
factorization alone is not a Menon adapter.

Next let \(T\to\infty\) with \(D\) fixed.  Only after obtaining the
resulting \(o_D(1)\) factor let \(D\to\infty\).  The \(h\)-tails vanish
by the following explicit estimate.  If

\[
 H_D(n):=\sum_{\substack{a\mid n\\a>D}}|h(a)|,
\]

then, for every fixed \(0<\sigma<1\),

\[
 \frac1X\sum_{X<n\le2X}H_D(n)
 \le \sum_{a>D}\frac{|h(a)|}{a}
 +2^\sigma X^{\sigma-1}
   \sum_{a\ge1}\frac{|h(a)|}{a^\sigma}.
\tag{4.231a}
\]

The first term tends to zero with \(D\), and the second tends to zero
with \(X\) for fixed \(D\).  Triangle inequality followed by
Cauchy--Schwarz transfers (4.231a) to either factor in the averaged
fixed-slope correlation.

For the coprimality tail, fix nonzero shifts \(1\le|\delta|\le L\).
The simultaneous dilation
\(r=dr',s=ds',\delta=d\delta'\) forces \(d\le L\).  Directly counting
the resulting affine lines gives, for fixed nonzero \(m_1,m_2\),

\[
 \frac1{XL}
 \sum_{\substack{r,s\asymp X\\
          1\le|m_1s-m_2r|\le L}}
 \sum_{\substack{d\mid(r,s)\\d>D}}1
 \ll_{m_1,m_2}
 \sum_{d>D}\frac1{d^2}+\frac{\log(2L)}{L}.
\tag{4.231b}
\]

Thus the two algebraic tails vanish in the order \(T\to\infty\), then
\(D\to\infty\), but this does not repair the missing twisted correlation
estimate.  In particular, the formerly claimed bound obtained by
inserting Menon's untwisted factor at \(L=\mathscr L^2\) is rejected.
The exact q-density and convolution remain available for any future
phase-compatible argument.

The adapter `large_q_endpoint_critical_shift_audit` records the
\(T^{-1/2}\) Mellin error, the \(d^{-2}\) coprimality tail, the fixed
convolution (4.230), and the two-limit order.  It sets
`q_restriction_removed_before_correlation=True` and
`fixed_zeta_scales_required=True` and
`full_height_phase_must_remain_in_correlation=True`.  It preserves
`critical_shift_subface_covered=False` and
`unconditional_coverage=False`.

### 4.27 Growing zeta scales: exact product lift and centered energy gate

The remaining \(\lambda=2\) family with polylogarithmically growing
\(K\asymp M=:P\) has a sharper exact reduction than the pointwise gcd
bound in (4.221).  Put \(g=(m_1,m_2)\).  The equation

\[
 m_1s-m_2r=\delta
\tag{4.234}
\]

has no solutions unless \(g\mid\delta\).  For a fixed admissible
nonzero \(\delta\), the number of solutions in \(r,s\asymp T\) is

\[
 \ll 1+\frac{Tg}{P}.
\tag{4.235}
\]

Retaining \(g\mid\delta\) before summing \(0<|\delta|\le L\), and using
\((m_1m_2)^{-1/2}\asymp P^{-1}\), gives the exact-scale inequality

\[
 \begin{aligned}
 &\sum_{m_1,m_2\asymp P}\frac1{\sqrt{m_1m_2}}
   \sum_{\substack{0<|\delta|\le L\\g\mid\delta}}
   \left(1+\frac{Tg}{P}\right)\\
 &\qquad\ll
 \frac{L}{P}\sum_{m_1,m_2\asymp P}\frac1g
 +\frac{TL}{P^2}\sum_{m_1,m_2\asymp P}1
 \ll LP+TL\ll TL.
 \end{aligned}
\tag{4.236}
\]

Thus the earlier \(\log P\) from summing \((m_1,m_2)\) pointwise is not
part of the minimal critical gate.  At \(L=\mathscr L^2\), the two
endpoint tapers turn (4.236) into \(O(T)\), but not \(o(T)\).  One still
needs cancellation of little-oh size, not a positive power saving.

There is an exact one-variable lift of that cancellation problem.  For
one tensor component in the absolutely convergent Mellin--Fourier
separation of the smooth coupled weight, write its left factor as
\(a_\nu(m,s)\) and define

\[
 \boxed{
 A_{P,\nu}(n):=\sum_{\substack{ms=n\\m\asymp P,\ s\asymp T}}
 \frac{f(s)}{\sqrt m}\,a_\nu(m,s).}
\tag{4.237}
\]

For the corresponding right coefficient \(B_{P,\nu}\), the finite
reindexing \(n=m_1s\), \(n-\delta=m_2r\) gives, with no error,

\[
 \boxed{
 \sum_{m_1,m_2,r,s}
 \frac{f(s)f(r)}{\sqrt{m_1m_2}}
 a_\nu(m_1,s)b_\nu(m_2,r)
 \mathbf1_{m_1s-m_2r=\delta}
 =\sum_n A_{P,\nu}(n)B_{P,\nu}(n-\delta).}
\tag{4.238}
\]

The helper functions `product_lift_coefficients` and
`product_lift_shifted_correlation` verify (4.238) exactly on finite
rational fixtures.  Möbius inversion of \((r,s)=1\) produces the same
identity for each \(d\mid\delta\); since \(\delta\ne0\), necessarily
\(d\le L\), and (4.231b) sums the resulting tail.

Consequently the remaining analytic input can be stated as the single
centered product-energy gate

\[
 \boxed{
 \mathfrak C_{P,L}[\Omega]
 :=\sum_{0<|\delta|\le L}\sum_n
 A_P(n)B_P(n-\delta)\Omega(n,\delta)
 =o_W(TL),}
\tag{4.239}
\]

uniformly for the polylogarithmic \(P\)-ranges generated by the exact
dyadic decomposition.  Here \(\Omega\) includes the remaining shared
Mellin--Fourier parameters and the summed tensor-variation norm; thus
(4.239) is the post-separation inequality needed by the original smooth
kernel, rather than an assertion that the kernel is a single elementary
tensor.  Since \(L=\mathscr L^2\), (4.239) and the two endpoint tapers
give \(o_W(T)\).

For the unweighted symmetric triangular kernel
\(\omega_L(\delta)=(1-|\delta|/L)_+\), (4.239) is precisely the centered
short-interval variance statement

\[
 \int_{\mathbb R}\left|
    \sum_{x<n\le x+L}A_P(n)\right|^2dx
 -L\sum_n|A_P(n)|^2
 =o_W(TL^2).
\tag{4.240}
\]

The subtracted term is exactly the \(\delta=0\) product diagonal; it is
not discarded by an upper bound.  Menon's theorem applies to \(\mu\)
(and the fixed
convolution transfer in Section 4.26), not uniformly to the growing
product coefficient (4.237) with its coprimality and coupled weight.
Therefore (4.240) is a new local variance theorem, not a published
adapter.

The exact-rational record
`large_q_growing_zeta_product_lift_audit` sets
`gcd_divisibility_removes_spurious_log_loss=True` and
`product_lift_identity_is_exact=True`, but preserves
`centered_product_energy_estimate_proved=False` and
`unconditional_coverage=False`.

### 4.28 Height-phase closure below the product-scale boundary

The original height phase already closes the part of (4.239) for which
the shift scale exceeds the zeta-variable scale.  Let \(M\asymp P\),
\(|\delta|\asymp D\), and retain the exact phase

\[
 \theta=\log\left(1+\frac{\delta}{m_2r}\right).
\tag{4.241}
\]

All derivatives of the completed AFE amplitude on \(t\asymp T\) satisfy
the normalized bounds needed for repeated integration by parts.  Hence,
for every fixed \(A\ge1\),

\[
 \boxed{
 \left|\int_{\mathbb R}G(t)
 e^{it\theta}W(t/T)\,dt\right|
 \ll_{A,W}T(1+T|\theta|)^{-A}.}
\tag{4.242}
\]

On the present support \(r\asymp T\), \(m_2\asymp M\), and
\(|\delta|\ll (m_2r)/2\).  The elementary inequalities
\(|x|/2\le|\log(1+x)|\le2|x|\) for \(|x|\le1/2\) give

\[
 \boxed{
 T(1+T|\theta|)^{-A}
 \ll_{A,W}T\left(1+\frac{|\delta|}{M}\right)^{-A}.}
\tag{4.243}
\]

Apply (4.243) in the pre-Poisson shifted equation before taking absolute
values, retain \((m_1,m_2)\mid\delta\) as in (4.236), and sum
\(q\asymp T^2\) using \(\sum q^{-1}\ll1\).  The contribution of the
dyadic shift box \(|\delta|\asymp D\) is

\[
 \ll_{A,W}
 \frac{T}{\mathscr L^2}
 D\left(1+\frac{D}{M}\right)^{-A}.
\tag{4.244}
\]

The separately subtracted zero Poisson mode is treated from the exact
common-kernel formula (4.5a) of the off-diagonal note.  On its dyadic
\(x\asymp M\) support it has the same phase
\(t\log(1+\delta/(xr))\), hence the same factor
\((1+D/M)^{-A}\).  The \(x\)-integral has bounded logarithmic mass, and
the factor \((q\sqrt{rs}\,s)^{-1}\) against the \(O(T^2)\) pairs
\((r,s)\) gives exactly the scale in (4.244).  Thus subtracting the zero
mode preserves that bound.  Summing (4.244) over dyadic \(D\le L\),
with \(A>3\), gives

\[
 \boxed{
 \mathcal R_{\mathrm{large}\ q}(L,M)
 \ll_W \frac{T}{\mathscr L^2}\min(L,M)
       (\log\mathscr L)^{O_W(1)}.}
\tag{4.245}
\]

Write \(L\le\mathscr L^\lambda\) and
\(M\le\mathscr L^\pi\).  Equation (4.245) is

\[
 \mathcal R_{\mathrm{large}\ q}(\lambda,\pi)
 \ll_W T\mathscr L^{\min(\lambda,\pi)-2}
       (\log\mathscr L)^{O_W(1)}.
\tag{4.246}
\]

Therefore every strict subface

\[
 \boxed{\min(\lambda,\pi)<2}
\tag{4.247}
\]

is unconditionally \(o_W(T)\).  In particular, for the critical shift
depth \(\lambda=2\), all zeta-variable depths

\[
 \boxed{0\le\pi<2}
\tag{4.248}
\]

are covered without a Möbius-correlation theorem.  At \(\pi=2\), the
ratio \(L/M\) may remain bounded and (4.243) supplies no logarithmic
decay; this is precisely where the centered product-energy gate (4.239)
becomes necessary.

The adapter `large_q_height_phase_audit` records the exact phase-ratio
depth \(\lambda-\pi\), the pre-phase logarithmic exponent
\(\lambda-2\), and the arbitrary integration-by-parts order.  It sets
`strict_subface_covered=True` at \((\lambda,\pi)=(2,3/2)\) and rejects
the boundary \((2,2)\).  The complete phase is retained throughout.

### 4.29 Restricted divisor completion and the reflected-tail boundary

At \((\lambda,\pi)=(2,2)\), complete the mollifier divisor sum before
estimating it.  Fix \(q\), put \(X=N/q\), and for every \(n\ge1\) define
the \(q\)-free part

\[
 n^{(q)}:=\prod_{\substack{p^a\parallel n\\p\nmid q}}p^a.
\tag{4.249}
\]

Euler multiplication, or direct Möbius inversion, gives the exact
formal-logarithmic identity

\[
 \boxed{
 \sum_{\substack{d\mid n\\(d,q)=1}}
 \mu(d)\log\frac{X}{d}
 =\log X\,\mathbf1_{n^{(q)}=1}+\Lambda(n^{(q)}).}
\tag{4.250}
\]

Indeed, the coefficient of \(\log X\) is
\(\sum_{d\mid n^{(q)}}\mu(d)=\mathbf1_{n^{(q)}=1}\), while

\[
 -\sum_{d\mid n^{(q)}}\mu(d)\log d=\Lambda(n^{(q)}).
\tag{4.251}
\]

The helper q_restricted_mobius_log_signature verifies
(4.250)--(4.251) exactly in the free abelian basis generated by the
prime logarithms.

The coefficient actually present in the endpoint mollifier is truncated
at \(d\le X\).  Therefore

\[
 \begin{aligned}
 B_{q,X}(n)
 &:=
 \sum_{\substack{d\mid n\\d\le X\\(d,q)=1}}
 \mu(d)\log\frac{X}{d}\\
 &=\log X\,\mathbf1_{n^{(q)}=1}+\Lambda(n^{(q)})
   -\mathcal T_{q,X}(n),
 \end{aligned}
\tag{4.252}
\]

where the reflected tail has either of the two exactly equivalent forms

\[
 \boxed{
 \begin{aligned}
 \mathcal T_{q,X}(n)
 &:=\sum_{\substack{d\mid n\\d>X\\(d,q)=1}}
       \mu(d)\log\frac{X}{d}\\
 &=\sum_{\substack{m\mid n\\m<n/X\\(n/m,q)=1}}
       \mu(n/m)\log\frac{Xm}{n}.
 \end{aligned}}
\tag{4.253}
\]

There is an important localization condition.  Formula (4.250) sums all
divisors \(d\mid n\), whereas one current box has only \(d=s\asymp T\).
Moreover the AFE factor \(V_t(m_1m_2)\) couples the two zeta variables.
Thus (4.252) becomes an identity for the actual remainder only after all
reduced-variable dyadic scales are regrouped and the AFE weight is
separated, with its residue and transform tail retained.  That
cross-scale aggregation is not proved here.  Section 4.30 below removes
the AFE weight with a power-saving error inside a subcritical endpoint
box, but also records why this does not authorize the full divisor
completion: at fixed product, adding the missing divisor scales changes
the complementary zeta scale and can cross the AFE transition.

Subject to that exact aggregation, the retained reduced mollifier
variable is squarefree, coprime to \(q\), and divides \(n^{(q)}\).
The mass term in (4.252) is then empty.  If the von Mangoldt term is
nonzero, then \(n^{(q)}=p^a\); squarefreeness forces \(s=p\).  Thus every
nonzero completed main coefficient forces the long reduced variable to
be prime.  This formal implication is recorded as
squarefree_reduced_variable_forces_prime=True.

Once the completed main is legitimately isolated, terms containing it
are below the critical scale by the elementary upper-bound sieve.  With
\(g=(m_1,m_2)\), the affine line for one admissible \(\delta\) has length
\(Tg/P+O(1)\).  Uniformly in the primitive pair of linear forms, the
one- and two-prime sieve bounds, followed by the exact
\(g\mid\delta\) aggregation of (4.236), give

\[
 \begin{aligned}
 \mathfrak C^{\mathrm{main}\times\mathrm{tail}}_{P,P}
 &\ll_W \frac{TP}{\log T}(\log\log(2P))^{O_W(1)},\\
 \mathfrak C^{\mathrm{main}\times\mathrm{main}}_{P,P}
 &\ll_W \frac{TP}{(\log T)^2}(\log\log(2P))^{O_W(1)}.
 \end{aligned}
\tag{4.254}
\]

The same first line covers tail × main.  The possible local singular
factors are divisor sums in \(m_1m_2\delta\); their average over the
three displayed variables is absorbed by the stated fixed power of
\(\log\log(2P)\).  Since \(P=\mathscr L^2\), both lines are
\(o_W(TP)\), as required by (4.239).

Consequently the formal completed expansion has only one unsolved term:

\[
 \boxed{
 \mathfrak C^{\mathrm{tail}\times\mathrm{tail}}_{P,L}[\Omega]
 =o_W(TL),
 \qquad P=L=\mathscr L^2.}
\tag{4.255}
\]

The moving cutoff \(m<n/X\) in (4.253) lies exactly at the product-scale
boundary, so the phase ratio need not grow.  Neither (4.243) nor the
published fixed-slope correlation theorem proves (4.255).  More
importantly, (4.255) is not yet the sole actual local residual until the
cross-scale AFE aggregation above is established.  The adapter
large_q_boundary_reflection_audit records the exact formal completion,
the prime-forcing main term, and the sieve estimates, but sets
cross_scale_aggregation_proved=False,
reflected_tail_energy_estimate_proved=False, and
unconditional_coverage=False.

### 4.30 Subcritical AFE residue and the remaining cross-scale obstruction

One part of the cross-scale interface in Section 4.29 can be completed
locally.  Fix \(\eta>0\) and restrict the original terms to

\[
 m_1m_2\le T^{1-\eta}.
\tag{4.256}
\]

From the completed Mellin definition (2.3) of the off-diagonal note,
shift the contour to \(\Re z=-c\), where \(0<c<1/4\).  The pole at
\(z=0\) has residue one, and the pole-cancelling factors in \(G_t\)
leave no other residue.  The uniform Stirling bound (2.5b) therefore
gives

\[
 \boxed{
 V_t(m_1m_2)
 =1+O_c\left(\left(\frac{m_1m_2}{T}\right)^c\right)
 =1+O_c(T^{-c\eta}).}
\tag{4.257}
\]

The last error can be aggregated before any cancellation theorem.  On
one dyadic family write

\[
 m_1\asymp K,\quad m_2\asymp M,\quad
 r\asymp R,\quad s\asymp S,\quad KS\asymp MR.
\tag{4.258}
\]

Put \(R\asymp KU\), \(S\asymp MU\).  For
\(g=(m_1,m_2)\), one admissible shift has
\(O(1+Ug)\) solutions, and the number of nonzero shifts in a box
\(|\delta|\asymp D\) is \(O(D/g)\).  Against the exact factor

\[
 \frac{T}{q\sqrt{KMRS}}\asymp\frac{T}{qKMU},
\]

the weighted sum over the \(O(KM)\) choices of \(m_1,m_2\) is

\[
 \boxed{\ll_W\frac{TD}{q}.}
\tag{4.259}
\]

This count is used when \(U\ge1\).  If \(U<1\), fix \((r,s)\) instead
and solve the same determinant equation in \((m_1,m_2)\); its line
length is \(U^{-1}(r,s)\), while there are \(O(KMU^2)\) choices of
\((r,s)\).  The identical calculation again gives (4.259).  This
reciprocal choice of the longer lattice direction removes the otherwise
spurious \(O(1)\)-per-fiber boundary loss.

The endpoint \(q\)-family satisfies
\(\sum_{q\asymp T^2}q^{-1}\ll1\).  Hence (4.257), all dyadic ratio
families, and every polylogarithmic shift box contribute

\[
 \ll_{c,\eta,W}
 T^{1-c\eta}(\log(2T))^{O_W(1)}
 =o_W(T).
\tag{4.260}
\]

Thus, inside any already selected subcritical dyadic family, the AFE
weight may be replaced by its residue one at a total cost \(o_W(T)\).
This does **not** yet make the coefficient equal to
\(B_{q,X}(n)/\log N\).  The reason is exact.  If an endpoint term has
\(n=ms\), with \(m\le P\) and \(s\asymp X\), completing (4.252) adds a
divisor \(d\mid n\) at every scale \(d\le X\).  The same product is then
represented as

\[
 n=m_dd,\qquad m_d=\frac nd.
\tag{4.260a}
\]

For small \(d\), the complementary zeta scale \(m_d\) is no longer
polylogarithmic.  On the two sides the condition
\(m_{d_1}m_{d_2}\le T^{1-\eta}\) is therefore not preserved by the full
divisor completion.  Equivalently, the indicator of the subcritical
region is a coupled function of \(d_1,d_2\) after the product
reindexing.

The scales introduced by (4.260a) can enter the transition collar

\[
 T^{1-\eta}<m_1m_2\ll T^{1+o(1)},
\tag{4.261}
\]

where replacing \(V_t\) by one has no fixed power saving.  The original
endpoint terms themselves do satisfy

\[
 K,M\le(\log T)^2,
 \qquad m_1m_2\ll(\log T)^4\le T^{1-\eta}
\tag{4.261a}
\]

for every fixed \(0<\eta<1\) and all sufficiently large \(T\), but the
new representations (4.260a) need not.  Consequently (4.260) proves the
local residue replacement and its aggregate error; it does not prove
the cross-scale reindexing needed to make (4.252)--(4.255) actual.

The adapter large_q_subcritical_afe_completion_audit records the Mellin
saving \(c\eta\) and the exact local scale (4.259).  It sets
local_endpoint_afe_weight_replaced_by_residue=True but records
all_reduced_dyadic_scales_regrouped_before_absolute_values=False,
subcritical_cross_scale_aggregation_proved=False,
full_divisor_completion_crosses_afe_transition=True, and
full_endpoint_cross_scale_aggregation_proved=False.  Hence
unconditional_coverage=False.

### 4.31 Why one left-line twisted-divisor energy is not exact

There is a tempting but invalid way to treat the other large-\(q\)
cells near the AFE transition.  Recording its exact failure prevents the
right-line Euler identity below from being promoted to a left-line
estimate.  Start on the original absolutely convergent line:

\[
 V_t(m_1m_2)
 =\frac1{2\pi i}\int_{(2)}
 G_t(z)g_t(z)(m_1m_2)^{-z}\frac{dz}{z}.
\tag{4.262}
\]

For the product variables \(n_1=m_1s\), \(n_2=m_2r\), the elementary
identity

\[
 (m_1m_2)^{-z}=(n_1n_2)^{-z}(sr)^z
\tag{4.263}
\]

puts one factor \(d^z\) into each reduced mollifier divisor sum.
Consequently, on \(\Re z=2\), after summing all smooth dyadic
partitions before taking absolute values, the divisor-dependent part of
the exact one-sided coefficient is

\[
 \boxed{
 D_{q,X,z}(n):=
 \frac{n^{-z}}{\log N}
 \sum_{\substack{d\mid n\\d\le X\\(d,q)=1}}
 \mu(d)d^z\log\frac{X}{d}.}
\tag{4.264}
\]

The remaining divisor-independent normalization is \(n^{-1/2}\); the
two sides therefore carry
\(n_1^{-1/2}n_2^{-1/2}D_{q,X,z}(n_1)D_{q,X,z}(n_2)\), together with the
exact \(q\)-weight, coprimality condition, height phase, and smooth
cutoffs.  Since \(\Re z=2\), this product expansion is absolutely
convergent and the reindexing is valid.

Let \(a=n^{(q)}\) and define

\[
 P_a(z):=\prod_{p\mid a}(1-p^z).
\tag{4.265}
\]

The complete, untruncated divisor coefficient has the exact Euler
formula

\[
 \boxed{
 \sum_{\substack{d\mid n\\(d,q)=1}}
 \mu(d)d^z\log\frac{X}{d}
 =\log X\,P_{n^{(q)}}(z)-P'_{n^{(q)}}(z).}
\tag{4.266}
\]

The finite helper q_restricted_twisted_log_signature verifies (4.266)
in independent formal variables \(p^z\), including every prime-log
coefficient.  At \(z=0\), (4.266) is exactly (4.250):

\[
 \log X\,P_a(0)-P'_a(0)
 =\log X\,\mathbf1_{a=1}+\Lambda(a).
\tag{4.267}
\]

For \(z\ne0\), however, \(P_a(z)\) is generally nonzero for every
squarefree kernel \(a\); the prime-power sparsity is lost.

One cannot now shift the already reindexed product energy from
\(\Re z=2\) to \(\Re z=-c\).  For example, if \(p>X\) is prime, the
only divisor retained in (4.264) is \(d=1\), and hence on the left line

\[
 p^{-1/2}|D_{q,X,-c+i\tau}(p)|
 =p^{c-1/2}\frac{\log X}{\log N}.
\tag{4.268}
\]

In particular the corresponding one-sided series, and therefore the
shifted \(n\)-energy obtained by termwise multiplication, is not
absolutely convergent.
The Gaussian decay of \(G_t(-c+i\tau)\) controls \(\tau\), not the
arithmetic \(n\)-tail, so it does not justify interchanging the contour
shift with the product sum.

Nor does inserting a smooth transition cutoff first preserve (4.264).
Indeed

\[
 \chi\!\left(\frac{m_1m_2}{T}\right)
 =\chi\!\left(\frac{n_1n_2}{rsT}\right)
\tag{4.269}
\]

depends simultaneously on the two reduced divisors \(r,s\).  Before a
further absolutely convergent kernel separation, it cannot be assigned
to two independent one-sided divisor coefficients.  Thus (4.266) is an
exact finite Euler identity, but it does **not** by itself reduce the AFE
transition to one twisted-divisor energy on \(\Re z=-c\).

The adapter large_q_transition_mellin_divisor_audit records the exact
right-line separation (4.263), the Euler polynomial (4.266), the loss of
sparsity away from \(z=0\), and the Gaussian transform tail.  It also
records
left_line_product_energy_is_absolutely_convergent=False,
transition_cutoff_preserves_one_sided_divisor_completion=False, and
transition_reduced_to_one_twisted_divisor_energy=False.  No transition
coverage is claimed; in particular
twisted_divisor_energy_estimate_proved=False and
unconditional_coverage=False.

### 4.32 Scale-stable transition gate on the zero Mellin line

There is a valid replacement for the rejected left-line operation, but
it must localize the product before Mellin separation.  Let
\(\chi\in C_c^\infty((1/2,2))\), let \(Y\asymp T\), and put

\[
 h_{t,Y}(y):=\chi(y)V_t(Yy),
 \qquad
 \widetilde h_{t,Y}(\tau)
 :=\int_0^\infty h_{t,Y}(y)y^{i\tau}\frac{dy}{y}.
\tag{4.270}
\]

Ordinary Mellin inversion on the zero line gives the exact identity

\[
 \chi\!\left(\frac{x}{Y}\right)V_t(x)
 =\frac1{2\pi}\int_{\mathbb R}
 \widetilde h_{t,Y}(\tau)Y^{i\tau}x^{-i\tau}\,d\tau.
\tag{4.271}
\]

Because \(y\) is confined to a fixed compact interval and \(Y\asymp T\),
the derivative bound (2.5) implies, for every \(A,j\ge0\),

\[
 \partial_t^j\widetilde h_{t,Y}(\tau)
 \ll_{A,j,W}T^{-j}(1+|\tau|)^{-A}.
\tag{4.272}
\]

Thus (4.271) has no real power \(n^c\) and its \(\tau\)-tail is
absolutely summable.

The coprimality condition must not be hidden in a one-sided coefficient.
For \(c\ge1\), define

\[
 \boxed{
D^{[c]}_{q,X,i\tau}(n)
 :=\frac{n^{-i\tau}}{\log N}
 \sum_{\substack{d\mid n,\ d\le X,\ (d,q)=1\\c\mid d}}
 \mu(d)d^{i\tau}\log\frac{X}{d}.}
\tag{4.273}
\]

For a local exponent statement the divisor and complementary zeta
scales must remain visible.  Define the exact dyadic projection

\[
 \begin{aligned}
 D^{[c]}_{q,X,i\tau;R,K}(n)
 :={}&\frac{n^{-i\tau}}{\log N}
 \sum_{\substack{d\mid n,\ d\le X,\ (d,q)=1\\c\mid d}}
 \mu(d)d^{i\tau}\log\frac{X}{d}
 F_R(d)F_K(n/d).
 \end{aligned}
\tag{4.273a}
\]

Since the dyadic partitions are exact and locally finite,
\(D^{[c]}_{q,X,i\tau}(n)=\sum_{R,K}
D^{[c]}_{q,X,i\tau;R,K}(n)\).

Möbius inversion of \(\mathbf1_{(r,s)=1}\), followed by
\(n_1=m_1s\), \(n_2=m_2r\), is finite and gives

\[
 \begin{aligned}
 \mathfrak E^{\mathrm{tr}}_{q,Y}
 (\tau;R,S,K,M)
 :={}&\sum_{c\ge1}\mu(c)
 \sum_{0<|\delta|\asymp L}\sum_n
 \frac{D^{[c]}_{q,X,i\tau;S,K}(n)
 D^{[c]}_{q,X,i\tau;R,M}(n-\delta)}
 {\sqrt{n(n-\delta)}}
 \Omega_{q,t,Y}(n,\delta).
 \end{aligned}
\tag{4.274}
\]

The summand is declared zero unless \(n>0\) and \(n-\delta>0\).
Here \(X=N/q\), and \(\Omega_{q,t,Y}\) retains the exact height phase
\(\exp(it\log(n/(n-\delta)))\), the remaining smooth shift cutoff, and
the original support conditions;
the product cutoff and AFE weight are already contained in
\(\widetilde h_{t,Y}\).  Since \(c\mid n,n-\delta\), the
outer sum in (4.274) automatically has

\[
 c\mid\delta,\qquad c\le|\delta|.
\tag{4.275}
\]

In particular it is finite on every nonzero shift box.  The original
finite helper coprime_divisor_pair_identity verifies both (4.274) and
the divisibility (4.275) on exact rational fixtures, with arbitrary
one-sided divisor weights.  The original
transition contribution on this product band is exactly

\[
 \boxed{
 2\sum_q\frac{\mu(q)^2}{q}
 \int_T^{2T}W(t/T)\frac1{2\pi}
 \int_{\mathbb R}\widetilde h_{t,Y}(\tau)Y^{i\tau}
 \sum_{R,S,K,M,L}
 \mathfrak E^{\mathrm{tr}}_{q,Y}
 (\tau;R,S,K,M)\,d\tau\,dt.}
\tag{4.276}
\]

All sums in (4.276) are finite before the absolutely convergent
\(\tau\)-integral, so the reindexing and inversion require no analytic
continuation.  Formula (4.273) is the scale-stable meaning of
\(D_{q,X,i\tau}(n)\); at \(c=1,\tau=0\) it returns the truncated
restricted-divisor coefficient (4.252), while nonzero \(\tau\) retains
the twisted Euler factors and the reflected tail.

The exact remaining local proposition is the integrated estimate

\[
 \sum_{q,Y,L,R,S,K,M}\frac1q
 \left|\int_T^{2T}\int_{\mathbb R}
 \widetilde h_{t,Y}(\tau)Y^{i\tau}
 \mathfrak E^{\mathrm{tr}}_{q,Y}
 (\tau;R,S,K,M)\,d\tau\,dt\right|
 =o_W(T),
\tag{4.277}
\]

with the dyadic ranges and smooth norms inherited from the exact
decomposition.  No estimate audited here proves (4.277).  The adapter
also records the exact transition-face exponent.  At

\[
 q\asymp T^2,\quad r,s\asymp T,\quad
 m_1,m_2\asymp T^{1/2},\quad |\delta|\asymp T^{1/2},
\tag{4.278}
\]

the product variable has length \(n\asymp T^{3/2}\).  The reciprocal
affine-line count (4.259) is \(TL/q\) per \(q\), so cardinal summation
over \(q\asymp T^2\) has absolute exponent

\[
 1+\frac12=\frac32.
\tag{4.279}
\]

Thus the critical required saving is exactly \(T^{1/2}\), and a
fixed-power local gate sufficient for the asymptotic is

\[
 \boxed{
 \frac1q\left|\int_T^{2T}\int_{\mathbb R}
 \widetilde h_{t,Y}(\tau)Y^{i\tau}
 \mathfrak E^{\mathrm{tr}}_{q,Y}
 (\tau;R,S,K,M)\,d\tau\,dt\right|
 \ll_{\varepsilon,W}
 \frac{TL}{q}\,T^{-501/1000+\varepsilon}.}
\tag{4.280}
\]

After \(O(T^2)\) choices of \(q\), (4.280) is
\(T^{999/1000+\varepsilon}=o(T)\) for
\(0<\varepsilon<1/1000\).  This is a new Möbius-weighted
\((c,\delta,n)\) energy estimate, not a consequence of Mellin inversion.

The adapter
large_q_transition_compact_mellin_audit records the exact zero-line
inversion, arbitrary \(\tau\)-decay, absence of real-power coefficient
growth, and retention of coprimality and the reflected tail.  It sets
transition_reduced_to_compact_mellin_energy=True but
compact_mellin_energy_estimate_proved=False and
unconditional_coverage=False.

### 4.33 Transition Type-II diagonal and the nonzero Gram gate

The transition box is materially easier than the balanced hard box at
the first Type-II Cauchy step.  Apply the exact identity (4.5) to
\(r\asymp T\), and in a Type-II block write

\[
 r=ab,qquad b\asymp T^\beta,qquad
 a\asymp T^{1-\beta},qquad
 \frac13\le\beta\le\frac23.
\tag{4.281}
\]

Let \(\mathcal A_b\) denote the complete remaining amplitude, with the
second Möbius weight, the \((h,\delta)\)-coefficient, the zero-line
Mellin parameter, all smooth weights, and the exact phases retained.
Cauchy gives

\[
 \left|\sum_{b\asymp T^\beta}\mu(b)\mathcal A_b\right|^2
 \le T^{\beta+o(1)}
 \sum_{b\asymp T^\beta}|\mathcal A_b|^2.
\tag{4.282}
\]

The target for the unsquared core is \(T^{2-1/500+\varepsilon}\).
Consequently the exact sufficient square target is

\[
 \boxed{
 \sum_{b\asymp T^\beta}|\mathcal A_b|^2
 \ll_{\varepsilon,W}
 T^{4-\beta-\frac1{250}+\varepsilon}.}
\tag{4.283}
\]

The literal identical-tuple contribution to (4.283) contains one copy
of \(b,a,s\), and the squared \((h,\delta)\)-coefficient norm.  Its
exponent is

\[
 \beta+(1-\beta)+1+
 \left(\frac12+\frac12\right)=3.
\tag{4.284}
\]

At the two endpoints of (4.281), the margins of the square target above
this positive identity diagonal are respectively

\[
 \left(4-\frac13-\frac1{250}\right)-3
 =\frac{497}{750},
 \qquad
 \left(4-\frac23-\frac1{250}\right)-3
 =\frac{247}{750}.
\tag{4.285}
\]

Thus the identity diagonal may be majorized separately throughout the
Type-II interval; unlike the hard box, no Linnik subtraction is forced
at this step.  This does not prove (4.283), because the expanded square
still has a nonzero Gram/determinant part with the second Möbius weight
and the complete CRT phase.  The remaining local theorem is precisely

\[
 \boxed{
 \sum_{b\asymp T^\beta}
 |\mathcal A_b|^2_{\mathrm{nonzero\ Gram}}
 \ll_{\varepsilon,W}
 T^{4-\beta-\frac1{250}+\varepsilon},
 \quad \frac13\le\beta\le\frac23.}
\tag{4.286}
\]

The generic BCR adapter on this box has saving \(-7/8\), both one-sided
completion adapters lack a cited coupled-kernel bound, and Wright's
fixed-factor hypothesis is absent.  Hence none proves (4.286).  The
deterministic audit records the uniform diagonal margin but keeps
transition_type_ii_nonzero_gram_estimate_proved=False and
unconditional_coverage=False.

### 4.34 Published average-shift theorem still has a power deficit

Kim, arXiv:2509.24152v2, Theorem 1.2
([paper](https://arxiv.org/abs/2509.24152v2)), proves the following
general comparison.  For
multiplicative functions \(f,g\) satisfying the paper's short-interval
second-moment hypotheses with exponents \(b_1,b_2\in(0,2]\),

\[
 \left|\sum_{h\le H}\sum_{X\le n\le2X-h}
 f(n)\overline{g(n+h)}\right|
 \ll
 XH^{4/(8-b_1-b_2)}(\log X)^{O(1)}.
\tag{4.287}
\]

The range hypothesis \(X^\varepsilon\ll H\ll X^{1-\varepsilon}\)
contains the transition values

\[
 X=T^{3/2},\qquad H=T^{1/2}=X^{1/3}.
\tag{4.288}
\]

Grant the optimistic short-interval exponents \(b_1=b_2=1\).  Then the
power of \(H\) in (4.287) is \(2/3\), and the resulting bound has
\(T\)-exponent

\[
 \frac32+\frac12\cdot\frac23=\frac{11}{6}.
\tag{4.289}
\]

The fixed transition gate (4.280), before the common normalization, asks
for exponent

\[
 \frac32-\frac1{1000}=\frac{1499}{1000}.
\tag{4.290}
\]

Thus even this optimistic numerical substitution leaves the positive
power deficit

\[
 \boxed{
 \frac{11}{6}-\frac{1499}{1000}
 =\frac{1003}{3000}.}
\tag{4.291}
\]

There is also a prior hypothesis failure.  The actual local coefficient

\[
 n\longmapsto D^{[c]}_{q,X,i\tau;R,K}(n)
\tag{4.292}
\]

is not multiplicative: the dyadic restrictions on both \(d\) and
\(n/d\), the logarithmic endpoint factor, and the condition \(c\mid d\)
all break Euler multiplication.  The common \(\tau\)-integral and height
phase are likewise not supplied by the theorem.  Therefore the theorem
fails both structurally and numerically; it is not an adapter for
(4.286) or (4.280).

The exact-rational function
transition_kim_average_shifted_convolution_audit records
localized_mobius_divisor_coefficient_is_multiplicative=False,
uniform_common_mellin_twist_hypothesis_verified=False, the deficit
\(1003/3000\), theorem_applicable=False, and
published_coverage=False.

### 4.35 Exact transition determinant gate after Type-II Cauchy

The phrase "nonzero Gram" in (4.286) can be made exact on the original
coupled sum (6.0) of the reduction note.  On the transition face put

\[
 R=S=T,\qquad H=L=T^{1/2},\qquad
 r=ab,\quad b\asymp T^\beta,\quad
 a\asymp T^{1-\beta},
 \quad \frac13\le\beta\le\frac23.
\tag{4.293}
\]

For a fixed dyadic component define, with no separated-kernel
replacement,

\[
\begin{aligned}
 \mathcal A_b:={}&
 \sum_{a,s,h,\delta}
 c_U(a)\mu(s)\,
 \mathbf1_{(ab,s)=1}\mathbf1_{(q,abs)=1}
 p_N(qab)p_N(qs)                                      \\
 &\qquad\qquad\times
 \Psi\!\left(\frac{ab}{R},\frac{s}{S},
               \frac\delta L,\frac hH\right)
 e\!\left(-\frac{h\delta\overline{ab}}s\right),
\end{aligned}
\tag{4.294}
\]

where every summation variable is restricted by the exact support in
(6.0), and \(a>U\).  The squarefree support of \(\mu(ab)\) makes
\((a,b)=1\), so (4.5) gives the exact Type-II component
\(-\sum_b\mu(b)\mathcal A_b\).  Thus (4.283) applies to the literal
amplitude (4.294), not to an arbitrary coefficient model.

Expand \(\sum_b|\mathcal A_b|^2\), and put

\[
 n_i=h_i\delta_i,\qquad y_i=s_i a_i,
 \qquad
 \boxed{\Delta=n_1y_2-n_2y_1}.
\tag{4.295}
\]

All inverses below exist because
\((b,y_1y_2)=(a_i,s_i)=(a_i,b)=(s_i,b)=1\).  Applying reciprocity and
CRT exactly as in (4.8a)--(4.8c'') gives the complete phase

\[
\begin{aligned}
 &e\!\left(-\frac{n_1}{a_1bs_1}
            +\frac{n_2}{a_2bs_2}\right)
 e\!\left(\frac{n_1\overline{s_1b}}{a_1}
            -\frac{n_2\overline{s_2b}}{a_2}\right)       \\
 &\hspace{24mm}\times
 e\!\left(\frac{\Delta}{b y_1y_2}\right)
 e\!\left(-\frac{\Delta\bar b}{y_1y_2}\right).
\end{aligned}
\tag{4.296}
\]

In particular the two fixed-\(a_i\) phases in the first line must not be
discarded when the last reciprocal phase is transformed.

The zero determinant is the full proportional ray, not just the
identical tuple.  For a common sign of \(n_1,n_2\), it has the unique
parametrization

\[
 |n_1|=gu,\quad |n_2|=gv,\quad
 y_1=ku,\quad y_2=kv,\quad (u,v)=1.
\tag{4.297}
\]

The opposite-sign case is empty.  If \(n_i\asymp N_0\) and
\(y_i\asymp Y_0\), summing first over the primitive pair gives the
elementary bound

\[
 \sum_{\substack{(u,v)=1,\ u\asymp v\\
                  \max(u,v)\le C_0\min(N_0,Y_0)}}
 \left(1+\frac{N_0}{\max(u,v)}\right)
 \left(1+\frac{Y_0}{\max(u,v)}\right)
 \ll N_0Y_0\log(2T),
\tag{4.298}
\]

where the bound on \(\max(u,v)\) comes from the nonempty dyadic
intervals for \(g,k\); the isolated
linear terms are smaller in the present ranges.  The divisor
representations \(n_i=h_i\delta_i\), \(y_i=s_i a_i\), and
\(|c_U(a_i)|\le\tau(a_i)\) cost \(T^\varepsilon\).  Here

\[
 N_0=T,\qquad Y_0=T^{2-\beta},\qquad B=T^\beta.
\tag{4.299}
\]

Consequently the **entire** \(\Delta=0\) contribution, including every
nonidentical proportional tuple, is

\[
 \ll_{\varepsilon,W}BN_0Y_0T^\varepsilon
 =T^{3+\varepsilon}.
\tag{4.300}
\]

Its margins below (4.283) are exactly \(497/750\) at
\(\beta=1/3\) and \(247/750\) at \(\beta=2/3\).  This strengthens the
literal-diagonal statement in Section 4.33 and proves that no
zero-determinant subtraction is needed on this face.

For \(\Delta\ne0\), the exact remaining local theorem is

\[
\boxed{
 \begin{aligned}
 \mathrm{TDG}_{\beta}:={}&
 \sum_{b\asymp T^\beta}
 \sum_{\substack{a_i\asymp T^{1-\beta},\ s_i\asymp T\\
                   h_i,\delta_i\asymp T^{1/2}\\
                   \Delta=n_1y_2-n_2y_1\ne0}}
 c_U(a_1)c_U(a_2)\mu(s_1)\mu(s_2)\,
 \mathscr W_q(\boldsymbol a,\boldsymbol s,
              \boldsymbol h,\boldsymbol\delta;b)\\
 &\quad\times
 e\!\left(-\frac{n_1}{a_1bs_1}
            +\frac{n_2}{a_2bs_2}
            +\frac{n_1\overline{s_1b}}{a_1}
            -\frac{n_2\overline{s_2b}}{a_2}
            +\frac{\Delta}{b y_1y_2}
            -\frac{\Delta\bar b}{y_1y_2}\right)
 \ll_{\varepsilon,W}T^{4-\beta-1/250+\varepsilon}.
 \end{aligned}}
\tag{4.301}
\]

The weight \(\mathscr W_q\) is precisely the product of the two coupled
weights in (4.294), the four endpoint tapers, the two \(q\)-conditions,
and the displayed coprimality indicators; no factor in (4.296) is
absorbed unless it is written in the phase of (4.301).

Formula (4.296) exhibits the following reciprocalized modulus:

\[
 0<|\Delta|\ll T^{3-\beta},\qquad
 y_1y_2\asymp T^{4-2\beta},\qquad
 B=T^\beta,qquad
 \frac{y_1y_2}{B}=T^{4-3\beta}.
\tag{4.302}
\]

This representation is exact, but \(y_1y_2\) is not the minimal
conductor of the total \(b\)-phase.  The fixed-\(a_i\) phases and the
last reciprocal phase must be recombined before assigning that
conductor.  The exact-rational adapter
transition_type_ii_determinant_audit records the zero-ray estimate and
keeps nonzero_determinant_estimate_proved=False.

### 4.36 Minimal common-b conductor is the lcm modulus

Before the reciprocity split (4.296), the squared phase in (4.294) is

\[
 e\!\left(-\frac{n_1\overline{a_1b}}{s_1}
            +\frac{n_2\overline{a_2b}}{s_2}\right).
\tag{4.303}
\]

Put

\[
 g=(s_1,s_2),\qquad
 \ell=[s_1,s_2]=\frac{s_1s_2}{g},
\tag{4.304}
\]

and let \(\overline{a_i}^{(s_i)}\) denote the inverse modulo \(s_i\).
Reduction of \(\bar b\pmod\ell\) modulo each \(s_i\) proves

\[
 \boxed{
 (4.303)=e\!\left(\frac{C\bar b}{\ell}\right),\qquad
 C\equiv
 -n_1\overline{a_1}^{(s_1)}\frac{\ell}{s_1}
 +n_2\overline{a_2}^{(s_2)}\frac{\ell}{s_2}
 \pmod\ell.}
\tag{4.305}
\]

Thus the primitive common-\(b\) conductor is \(\ell\), not
\(y_1y_2\).  On a gcd box \(g\asymp T^\gamma\),
\(0\le\gamma\le1\),

\[
 \ell\asymp T^{2-\gamma},\qquad
 \sqrt\ell=T^{1-\gamma/2},\qquad
 \frac{\ell}{B}=T^{2-\gamma-\beta}.
\tag{4.306}
\]

For a smooth \(b\)-weight, finite Poisson summation gives

\[
 \sum_{\substack{b\in\mathbb Z\\(b,\ell)=1}}
 w(b/B)e(C\bar b/\ell)
 =
 \frac B\ell\sum_{h\in\mathbb Z}
 \widehat w(hB/\ell)S(C,h;\ell).
\tag{4.307}
\]

The actual Cauchy square contains
\(\mu(b)^2\mathbf1_{(b,qa_1a_2)=1}\), so square-divisor and
coprimality inversion are required before (4.307); this arithmetic
weight is not silently declared smooth.

The single completed sum has a kinematic Weil saving only when

\[
 \boxed{\beta>1-\frac\gamma2
 \quad\Longleftrightarrow\quad
 \gamma>2-2\beta.}
\tag{4.308}
\]

Hence the generic low-gcd region remains below square root, while a
high-gcd subface can cross it.  Condition (4.308) alone is not coverage:
the divisor expansions and the complete outer average in (4.301) still
have to meet \(T^{4-\beta-1/250+\varepsilon}\).

Indeed the \(g\asymp T^\gamma\) box contains
\(T^{2-\gamma+\varepsilon}\) pairs \((s_1,s_2)\).  Before
oscillation, the nonzero square has cardinal exponent

\[
 \beta+2(1-\beta)+2+(2-\gamma)
 =6-\beta-\gamma.
\tag{4.308a}
\]

Against (4.301) it therefore requires the saving

\[
 T^{\,2-\gamma+1/250}.
\tag{4.308b}
\]

A single \(b\)-completion supplies at most
\(T^{(\beta-1+\gamma/2)_+}\).  Even at the most favorable endpoint
\((\beta,\gamma)=(2/3,1)\), the remaining exponent is

\[
 \frac{251}{250}-\frac16=\frac{314}{375}>0.
\tag{4.308c}
\]

Thus no gcd box is closed by a separate \(b\)-completion.  The
high-gcd inequality (4.308) only reduces the missing saving; it does not
remove the need for a joint average over the remaining variables.

Blomer--Pascadi, arXiv:2607.24311v1, Theorem 5.7, gives

\[
 \sum_{\substack{m\in I,\ n\in J\\(m,c)=1}}
 \alpha_m\beta_nS(am,n;c)
 \ll
 \|\alpha\|_2\|\beta\|_2c^{1+o(1)}
 \left(
 \frac{(MN)^{1/2}}{c^{3/4}}
 +\frac{N^{1/2}}{c^{1/2}}
 +\frac{M^{1/2}}{c^{1/4}}
 \right).
\tag{4.309}
\]

Even under the optimistic identification \(c=\ell\), \(M=\ell\), and
\(N=\ell/B\), the largest parenthetical term is \(c^{1/4}\).  It is a
positive loss \(T^{(2-\gamma)/4}\) relative to the exact Kloosterman
matrix operator scale, not a saving.  The actual coefficient is also
query-dependent through \(C\) and the coupled weight.  Therefore
Theorem 5.7 does not prove (4.301).

The adapter transition_type_ii_lcm_completion_audit records the exact
lcm conductor, the boundary (4.308), the dual length, the nonsmooth
squarefree-coprime \(b\)-weight, and the Blomer--Pascadi loss.  It keeps
published_coverage=False.

### 4.37 Long-cutoff Möbius trace route has only logarithmic saving

One can retain a genuine second long Möbius weight by moving the
factorization cutoff close to the transition length.  Let

\[
 U=T^{1-\eta},\qquad r=ab,\qquad
 b\asymp T^\beta,\quad a\asymp T^{1-\beta},
 \qquad 0\le\beta\le\eta<\frac12.
\tag{4.310}
\]

If \(a>U\) is squarefree, complete divisor cancellation gives

\[
\begin{aligned}
 c_U(a)
 &= -\sum_{\substack{d\mid a\\d>U}}\mu(d)\\
 &= \boxed{-\mu(a)
 \sum_{\substack{e\mid a\\e<a/U}}\mu(e)}.
\end{aligned}
\tag{4.311}
\]

The second equality uses \(d=a/e\) and
\(\mu(a)=\mu(d)\mu(e)\).  The reflected divisor has length

\[
 e<T^{\eta-\beta}.
\tag{4.312}
\]

Thus (4.294) becomes a short divisor sum whose long variables carry
\(\mu(a)\mu(s)\), a genuine improvement over arbitrary coefficients.

For a prime modulus \(s\asymp T\), fixed \(b,n\), and
\((n,s)=1\), the function

\[
 a\longmapsto e(-n\overline{ab}/s)
\tag{4.313}
\]

is a bounded-conductor nonexceptional trace function.
Korolev--Shparlinski, arXiv:1804.01337v2, Theorem 2.1, proves, for
interval length \(A\ge s^{1/2+\varepsilon_0}\),

\[
 \sum_{a\le A}\mu(a)K(a)
 \ll_{\varepsilon_0}
 A\frac{\log\log s}{\log s}.
\tag{4.314}
\]

The long cutoff lies in that range when
\(\beta<1/2-\varepsilon_0\).  But (4.314) supplies only one logarithm.
The transition sum before cancellation has exponent

\[
 \underbrace{\beta+(1-\beta)}_{r}
 +\underbrace{1}_{s}
 +\underbrace{(1/2+1/2)}_{h,\delta}
 =3.
\tag{4.315}
\]

The fixed Type-II target is \(T^{2-1/500+\varepsilon}\).  Even granting
two independent copies of (4.314), one for each long Möbius variable,
leaves the positive power deficit

\[
 \boxed{3-\left(2-\frac1{500}\right)
 =\frac{501}{500}.}
\tag{4.316}
\]

This optimistic comparison also suppresses two actual hypothesis
failures: \(s\) runs over all squarefree composite moduli, not only
primes, and \(s\mid n\) gives an exceptional constant phase.  Therefore
the theorem is neither a direct adapter nor numerically sufficient.

The adapter transition_long_cutoff_mobius_trace_audit records
(4.310)--(4.316), including the reflected divisor length, trace-range
margin, prime-modulus failure, and the remaining \(501/500\) power.  It
keeps published_coverage=False.

### 4.38 Unconditional square-root difference collar at transition

There is an unconditional transition region which should be removed
before any new Type-II theorem is attempted.  Partition the bounded
ratio \(r/s\) into the finitely many integer-slope sectors

\[
 r=ks+w,\qquad k\asymp1,\qquad (w,s)=1,
\tag{4.317}
\]

and put \(D\le |w|\le2D\).  On the transition face

\[
 R=S=T,\qquad H=L=T^{1/2},\qquad A:=HL=T.
\tag{4.318}
\]

The original reciprocal phase uses
\(\bar r\equiv\bar w\pmod s\).  Reciprocity gives

\[
 -\frac{\bar w}{s}
 \equiv \frac{\bar s}{w}-\frac1{sw}\pmod1.
\tag{4.319}
\]

Since \(SD\ge A\) for every integer \(D\ge1\), the correction
\((sw)^{-1}\) is below the numerator resolution \(A^{-1}\).  A reduced
Farey center \(\bar s/w\) has \(O(S/D)\) preimages, and a resolution
interval meets \(O(1+D^2/A)\) centers.  The local-density additive
large sieve therefore gives, with the actual numerator coefficient
\(\nu(a)\),

\[
 |\mathfrak S_{q,k}(D)|
 \ll_W
 S(A+D^2)^{1/2}\|\nu\|_2.
\tag{4.320}
\]

The exact product energy loses only one logarithm.  Indeed

\[
 \boxed{\sum_a|\nu(a)|^2\ll_W HL\log(2\min(H,L)).}
\tag{4.321}
\]

To prove (4.321), write a solution
\(h_1\delta_1=h_2\delta_2\) as

\[
 h_1=ga,\quad h_2=gb,\quad
 \delta_1=bv,\quad\delta_2=av,\qquad (a,b)=1,
\tag{4.322}
\]

For \(m=\max(a,b)\), the \(g\)- and \(v\)-intervals contain
\(O(1+H/m)\) and \(O(1+L/m)\) integers, while there are \(O(m)\)
coprime comparable pairs with maximum \(m\).  Summing over
\(m\le2\min(H,L)\) proves (4.321), including all sign choices.

Substituting (4.318)--(4.321) yields

\[
 |\mathfrak S_{q,k}(D)|
 \ll_W
 T^{3/2}(T+D^2)^{1/2}(\log T)^{1/2}.
\tag{4.323}
\]

Hence every shell \(1\le D\le T^{1/2}\) is at the raw \(T^2\)
barrier.  The two endpoint mollifier tapers satisfy

\[
 |p_N(qr)p_N(qs)|\ll(\log T)^{-2}
\tag{4.324}
\]

on this constant-ratio face.  Summing the \(O(\log T)\) dyadic
\(D\)-shells in (4.323), while retaining (4.324), gives

\[
 \sum_{\substack{D\ {\rm dyadic}\\D\le T^{1/2}}}
 |\mathfrak S_{q,k}(D)|
 \ll_W T^2(\log T)^{-1/2}.
\tag{4.325}
\]

No hidden separation logarithm occurs here: in (5.13a) the three
dimensionless parameters satisfy
\(T\lambda_0\asymp\omega_0\asymp\chi_0\asymp1\), so the fixed
compact-kernel seminorms are \(O_W(1)\).  There are only finitely many
slopes \(k\).  Finally,

\[
 \sum_{q\asymp T^2}\frac{2T}{qRS}
 T^2(\log T)^{-1/2}
 \ll_W T(\log T)^{-1/2}=o_W(T).
\tag{4.326}
\]

Thus the union

\[
 \boxed{\min_{k\asymp1}|r-ks|\le T^{1/2}}
\tag{4.327}
\]

is unconditionally covered on the fixed transition face.  For
\(D=T^\theta\), \(1/2<\theta\le1\), (4.323) has exponent
\(3/2+\theta\); the remaining positive saving is exactly
\(\theta-1/2\), reaching \(1/2\) at the top shell.

The adapter transition_reciprocal_cluster_closure_audit records the
power barrier, the exact product-energy logarithm, both endpoint
tapers, the dyadic-shell loss, the net \(1/2\) logarithmic saving, and
low_difference_union_covered=True.  It keeps
whole_transition_face_covered=False.

### 4.39 The remaining transition far-shell trilinear gate

After Section 4.38 the positive-power transition residual is one
explicit family.  For \(D=T^\theta\), \(1/2<\theta\le1\), and one of
the finitely many slopes \(k\), define

\[
\boxed{
\begin{aligned}
 \mathrm{TFS}_{\theta}(q,k):={}&
 \sum_{\substack{s\asymp T,\ w\asymp D\\
                  ks+w\asymp T,\ (w,s)=1\\
                  (q,s(ks+w))=1}}
 \mu(s)\mu(ks+w)
 p_N(qs)p_N(q(ks+w))                              \\
 &\quad\times
 \sum_{h,\delta\asymp T^{1/2}}
 \Psi_{q,k}\!\left(
   \frac sT,\frac wD,\frac h{T^{1/2}},
   \frac\delta{T^{1/2}}\right)
 e\!\left(-\frac{h\delta\bar w}{s}\right).
\end{aligned}}
\tag{4.328}
\]

Both signs of \(h,\delta,w\), the exact support restrictions, and all
fixed transition kernel factors are included in \(\Psi_{q,k}\).
Neither Möbius weight has been replaced by an arbitrary coefficient.

The reciprocity-cluster estimate (4.323) gives

\[
 |\mathrm{TFS}_{\theta}(q,k)|
 \ll_W T^{3/2+\theta}(\log T)^{O(1)}
\tag{4.329}
\]

before spending the endpoint tapers.  A fixed-power version sufficient
for the coupled gate is

\[
 \boxed{
 |\mathrm{TFS}_{\theta}(q,k)|
 \ll_{\varepsilon,W}
 T^{\,2-1/1000+\varepsilon}.}
\tag{4.330}
\]

Thus the exact new arithmetic saving demanded on this shell is

\[
 \boxed{\theta-\frac12+\frac1{1000}.}
\tag{4.331}
\]

This is smaller than the former undifferentiated transition saving
\(501/1000\) on every proper shell and equals it only at \(\theta=1\).

The Fouvry--Kowalski--Michel trace estimate does not close (4.330).
Grant, contrary to the actual uniform hypotheses, a prime modulus
factor of size \(T^\theta\), a nonzero frequency modulo that prime, and
complete separation of the cofactor phase.  Theorem 1.7 of
arXiv:1211.6043v3 saves at most \(T^{\eta\theta}\) per application,
where every \(\eta<1/24\).  Even granting two independent
applications and taking the admissible value \(\eta=1/25\), the top
shell retains

\[
 \boxed{
 \frac{501}{1000}-\frac2{25}
 =\frac{421}{1000}.}
\tag{4.332}
\]

The optimistic hypotheses fail separately: a squarefree \(s\) need not
have a prime factor in the prescribed power interval; product
frequencies divisible by that prime produce a constant trace; and the
complementary CRT phase remains joint.  Consequently (4.328)--(4.331),
not a prime-trace corollary, are the surviving theorem interface.

The adapter transition_far_shell_mobius_gate_audit records all variable
lengths, the current bound, the fixed target, the required saving, the
optimistic FKM comparison, and the three failed hypotheses.  It keeps
estimate_proved=False and published_coverage=False.

### 4.40 Exact Type-I/II factor boxes for the far-shell gate

Apply (4.5) only to the first Möbius weight in (4.328), with

\[
 U=V=T^{1/3}.
\tag{4.333}
\]

Since \(r=ks+w\asymp T>U\),

\[
 \mu(r)=-\sum_{\substack{ab=r\\a>U}}c_U(a)\mu(b).
\tag{4.334}
\]

Split at \(b\le V\), and dyadically put

\[
 b\asymp T^\beta,\qquad
 a\asymp T^{1-\beta},\qquad
 0\le\beta\le\frac23.
\tag{4.335}
\]

The shifted equation and reciprocal phase are exactly

\[
 \boxed{ab-ks=w,\qquad
 e(-h\delta\bar w/s)=e(-h\delta\overline{ab}/s).}
\tag{4.336}
\]

There is no complementary-divisor condition and no discarded CRT
factor.  Define the resulting factor box

\[
\boxed{
\begin{aligned}
 \mathcal F_{\theta,\beta}:={}&
 \sum_{\substack{b\asymp T^\beta,\ a\asymp T^{1-\beta}\\
                  s\asymp T,\ w=ab-ks\asymp T^\theta\\
                  (ab,s)=1,\ (q,abs)=1}}
 c_U(a)\mu(b)\mu(s)
 p_N(qab)p_N(qs)                                      \\
 &\quad\times
 \sum_{h,\delta\asymp T^{1/2}}
 \Psi_{q,k,\theta,\beta}(a,b,s,h,\delta)
 e\!\left(-\frac{h\delta\overline{ab}}s\right).
\end{aligned}}
\tag{4.337}
\]

The exact Type-I and Type-II pieces of
\(\mathrm{TFS}_\theta\) are the sums of (4.337) over respectively
\(\beta\le1/3\) and \(\beta>1/3\), with the outer minus sign in
(4.334).

A fixed-power estimate sufficient after the logarithmic number of
factor boxes is

\[
 |\mathcal F_{\theta,\beta}|
 \ll_{\varepsilon,W}T^{\,2-1/500+\varepsilon}.
\tag{4.338}
\]

For a Type-II box write
\(\mathcal F_{\theta,\beta}=\sum_b\mu(b)\mathcal A_b\).
Cauchy reduces (4.338) to

\[
 \boxed{
 \sum_{b\asymp T^\beta}|\mathcal A_b|^2
 \ll_{\varepsilon,W}
 T^{\,4-\beta-1/250+\varepsilon}.}
\tag{4.339}
\]

The literal identity tuple has one copy of \(b,a\), one
\(s\)-interval of length \(T^\theta\) from
\(|ab-ks|\asymp T^\theta\), and the product-coefficient energy \(HL=T\).
Its exponent is therefore

\[
 \beta+(1-\beta)+\theta+1=2+\theta.
\tag{4.340}
\]

The margin below (4.339) is

\[
 2-\beta-\theta-\frac1{250}.
\tag{4.341}
\]

It is smallest at \((\theta,\beta)=(1,2/3)\), where it equals

\[
 \boxed{\frac13-\frac1{250}=\frac{247}{750}>0.}
\tag{4.342}
\]

Thus the positive identity diagonal closes uniformly in every final
factor box.  The surviving analytic input is the nonzero joint Gram
part of (4.339), with the second Möbius weight, the equation (4.336),
the complete phase, and the coupled kernel retained.  No published
adapter registered above proves that estimate.

The adapter transition_far_shell_factor_box_audit records
(4.333)--(4.342), including the exact factor range, the current
cluster bound, the fixed target, and the uniform diagonal margin.  It
keeps nonzero_joint_gram_estimate_proved=False and
published_coverage=False.

### 4.41 Full zero geometric Gram closes after factorization

Fix a Type-II factor box and expand the square on the left of
(4.339), keeping the common variable \(b\).  Put

\[
 w_i=a_i b-ks_i,
 \qquad
 \Gamma=a_1s_2-a_2s_1.
\tag{4.343}
\]

Eliminating \(b\) from the two shifted equations gives the exact
cross relation

\[
 \boxed{a_2w_1-a_1w_2=k\Gamma.}
\tag{4.344}
\]

Consequently the support \(a_i\asymp T^{1-\beta}\) and
\(|w_i|\asymp T^\theta\) imposes

\[
 |\Gamma|\ll T^{\,1-\beta+\theta}.
\tag{4.345}
\]

Suppose first that \(\Gamma=0\).  Then
\(a_1/s_1=a_2/s_2\).  The coprimality in (4.337) gives
\((a_i,s_i)=1\); because all four variables are positive, the two
fractions are primitive and hence

\[
 a_1=a_2,
 \qquad
 s_1=s_2,
 \qquad
 w_1=w_2.
\tag{4.346}
\]

The last equality follows either from (4.343) or directly from the
common-\(b\) equations.  Notice that (4.346) does **not** force
\(h_1\delta_1=h_2\delta_2\).  Thus the whole product-frequency
off-diagonal must remain inside the positive square

\[
 \left|
   \sum_n \nu_{a,b,s}(n)
   e\!\left(-\frac{n\overline{ab}}s\right)
 \right|^2.
\tag{4.347}
\]

Apply the reciprocal-cluster large sieve used in Section 4.38 to
(4.347) before taking absolute values in the two \(n\)-variables.
Together with the exact product energy

\[
 \sum_n|\nu_{a,b,s}(n)|^2
 \ll_W HL\log(2\min(H,L)),
\tag{4.348}
\]

the power exponent of the complete \(\Gamma=0\) contribution is

\[
 \beta+(1-\beta)+\theta+1=2+\theta.
\tag{4.349}
\]

The harmless logarithm in (4.348) is absorbed by the fixed power
margin.  Comparing (4.349) with the square target (4.339), that margin
is exactly

\[
 \left(4-\beta-\frac1{250}\right)-(2+\theta)
 =2-\beta-\theta-\frac1{250}.
\tag{4.350}
\]

It is uniformly positive, with the same worst value
\(247/750\) at \((\theta,\beta)=(1,2/3)\).  Hence (4.339) is proved
for the full zero geometric Gram, including all unequal
\((h_1,\delta_1),(h_2,\delta_2)\) pairs.

The sole remaining Type-II input is therefore the part of the square
with

\[
 0<|\Gamma|\ll T^{\,1-\beta+\theta},
\tag{4.351}
\]

subject to (4.343)--(4.345), both Möbius weights
\(\mu(s_1)\mu(s_2)\), both reciprocal phases, and the coupled kernel.
No estimate for (4.351) is asserted here.

The adapter transition_factor_square_geometry_audit records
(4.343)--(4.351).  It sets full_zero_geometry_closes=True but keeps
nonzero_geometric_determinant_gate_proved=False and
published_coverage=False.

### 4.42 Exact nonzero determinant shells and affine orbit

Dyadically decompose the remaining range (4.351) by

\[
 |\Gamma|\asymp T^\xi,\qquad
 (s_1,s_2)\asymp T^\gamma,\qquad
 (a_1,a_2)\asymp T^\alpha.
\tag{4.352}
\]

The exact support and the two determinant divisibilities give

\[
\boxed{
\begin{aligned}
 0&\le \xi\le 1-\beta+\theta,\\
 0&\le \gamma\le\min(1,\xi),\\
 0&\le \alpha\le\min(1-\beta,\xi).
\end{aligned}}
\tag{4.353}
\]

Indeed both \((s_1,s_2)\) and \((a_1,a_2)\) divide
\(\Gamma=a_1s_2-a_2s_1\).  Write

\[
 d_a=(a_1,a_2),\qquad a_i=d_au_i,\qquad (u_1,u_2)=1.
\tag{4.354}
\]

For fixed \(a_1,a_2,\Gamma\), choose one solution
\((s_1^{(0)},s_2^{(0)})\) of

\[
 u_1s_2-u_2s_1=\Gamma/d_a.
\tag{4.355}
\]

Every other integral solution, and no other pair, is

\[
 \boxed{s_i=s_i^{(0)}+u_i t\quad(i=1,2),\qquad t\in\mathbb Z.}
\tag{4.356}
\]

Along this orbit the common-\(b\) equations become

\[
 w_i=w_i^{(0)}-ku_it.
\tag{4.357}
\]

Since \(u_i\asymp T^{1-\beta-\alpha}\), the two windows
\(|w_i|\asymp T^\theta\) restrict the orbit parameter to an interval
of length

\[
 \ll 1+T^{\,\theta-1+\beta+\alpha}.
\tag{4.358}
\]

This is the exact complementary-divisor parametrization of the
geometric part; no second free \(s\)-variable remains.

There are two simultaneous exact descriptions of the phase.  First,
with \(g_s=(s_1,s_2)\) and \(\ell=[s_1,s_2]\), (4.305) gives

\[
 \ell\asymp T^{2-\gamma},\qquad
 \ell/B=T^{2-\gamma-\beta}.
\tag{4.359}
\]

Second, put \(\epsilon_i=\operatorname{sgn}(w_i)\).  Signed additive
reciprocity gives

\[
\boxed{
 e\!\left(-\frac{n_i\overline{w_i}}{s_i}\right)
 =
 e\!\left(\frac{\epsilon_i n_i\overline{s_i}}{|w_i|}\right)
 e\!\left(-\frac{\epsilon_i n_i}{|w_i|s_i}\right).}
\tag{4.360}
\]

Thus (4.360) moves each reciprocal modulus from \(T\) to
\(T^\theta\).  This is a strict conductor reduction when
\(\theta<1\), but gives no reduction on the top face \(\theta=1\).
The Archimedean factors in (4.360) remain part of the coupled weight
and cannot be deleted.

For completeness, define the last local sum by

\[
\boxed{
\begin{aligned}
 \mathcal G_{\theta,\beta;\xi,\gamma,\alpha}:={}&
 \sum_{\substack{b\asymp T^\beta,\ \mu(b)^2=1\\
                  a_i\asymp T^{1-\beta},\ s_i\asymp T\\
                  w_i=a_ib-ks_i,\ |w_i|\asymp T^\theta\\
                  |\Gamma|\asymp T^\xi,\ \Gamma\ne0\\
                  (s_1,s_2)\asymp T^\gamma\\
                  (a_1,a_2)\asymp T^\alpha\\
                  (q,a_1a_2bs_1s_2)=1\\
                  (a_ib,s_i)=1}}
 c_U(a_1)c_U(a_2)\mu(s_1)\mu(s_2)\\
 &\quad\times
 \sum_{n_1,n_2}
 \nu_1(n_1)\overline{\nu_2(n_2)}
 \mathscr W_{q,k,\theta,\beta}
   (\boldsymbol a,\boldsymbol s,b,\boldsymbol n)\\
 &\quad\times
 e\!\left(-\frac{n_1\overline{w_1}}{s_1}
           +\frac{n_2\overline{w_2}}{s_2}\right).
\end{aligned}}
\tag{4.361}
\]

The \(n_i=h_i\delta_i\) divisor-convolution coefficients, both
Möbius weights, all shell cutoffs, both endpoint tapers, and the full
coupled transform kernel are included in (4.361).  The estimate needed
uniformly on every admissible shell is

\[
 \boxed{
 |\mathcal G_{\theta,\beta;\xi,\gamma,\alpha}|
 \ll_{\varepsilon,W}
 T^{\,4-\beta-1/250+\varepsilon}.}
\tag{4.362}
\]

The proved direct reciprocal-cluster bound for one factor box is
\(T^{3/2+\theta+\varepsilon}\).  For comparison with the sufficient
Cauchy gate, its square-level exponent ledger, normalized by the
Cauchy length \(B=T^\beta\), is

\[
 T^{\,3+2\theta-\beta+\varepsilon}.
\tag{4.363}
\]

Equation (4.363) is not an independent bound for
\(\sum_b|\mathcal A_b|^2\): a bound for the signed \(b\)-sum cannot be
reversed through Cauchy.  Rather, it is the baseline that a
Cauchy-compatible reproduction of the cluster argument would have to
improve.  On that route the precise additional joint saving is

\[
\boxed{
 \left(3+2\theta-\beta\right)
 -\left(4-\beta-\frac1{250}\right)
 =2\theta-1+\frac1{250}.}
\tag{4.364}
\]

At the top shell
\[
 (\theta,\beta,\xi,\gamma,\alpha)
 =\left(1,\frac23,\frac43,0,0\right),
\tag{4.365}
\]
the affine-orbit length is \(T^{2/3}\), the lcm modulus is \(T^2\),
the \(b\)-completion dual length is \(T^{4/3}\), and the missing
saving is

\[
 \boxed{\frac{251}{250}.}
\tag{4.366}
\]

Thus separate \(b\)-completion and the conductor change (4.360) do
not close the top shell.  A proof of (4.362) must be genuinely joint in
the determinant orbit, the two \(\mu(s_i)\) weights, and the
product-frequency pair.  The adapter
transition_nonzero_gamma_shell_audit records (4.352)--(4.366), while
factor_determinant_orbit_parameter and
signed_reciprocity_phase_identity verify (4.356) and (4.360) on exact
finite fixtures.  It keeps cluster_square_bound_independently_proved=False,
complete_nonzero_shell_estimate_proved=False, and
published_coverage=False.

### 4.43 Unconditional low-determinant graph-energy region

A positive part of (4.362) can be proved without any new cancellation.
For fixed \(b\), let the vertices be the admissible pairs

\[
 x=(a,s),\qquad
 a\asymp T^{1-\beta},\qquad
 s\asymp T,\qquad
 w=ab-ks\asymp T^\theta.
\tag{4.367}
\]

Join \(x_1=(a_1,s_1)\) to \(x_2=(a_2,s_2)\) when

\[
 |a_1s_2-a_2s_1|\asymp T^\xi.
\tag{4.368}
\]

For fixed \(x_1\) and \(a_2\), condition (4.368) restricts \(s_2\) to
an interval of length \(O(T^\xi/a_1)\).  The second shifted window in
(4.367) has length \(O(T^\theta)\).  Therefore, with

\[
 \lambda:=
 \max\!\left(0,\min\!\left(\theta,\xi-1+\beta\right)\right),
\tag{4.369}
\]

the maximum graph degree satisfies the uniform bound

\[
 \boxed{\Delta_{\max}\ll T^{\,1-\beta+\lambda+\varepsilon}.}
\tag{4.370}
\]

All gcd and congruence restrictions can only decrease this degree.
The bound also includes both signs of the determinant shell.

Let \(z_x\) denote the complete product-frequency sum at the vertex
\(x\), including \(c_U(a)\), the smooth shell weight, the endpoint
tapers, and the coupled kernel.  Applying the same local-density
additive large sieve as in (4.320) to the squared vertex family, before
taking absolute values in the two product frequencies, gives

\[
 \boxed{
 \sum_b\sum_{x\in\mathcal V_b}|z_x|^2
 \ll_{\varepsilon,W}T^{\,2+\theta+\varepsilon}.}
\tag{4.371}
\]

The factorization \(ab=r\) costs only the divisor multiplicity
\(T^\varepsilon\), and (4.321) supplies the product-frequency energy.
At \(\theta=1\), (4.371) has exponent \(3\), in agreement with the
full zero-geometry calculation (4.349).

For every finite graph of maximum degree \(\Delta_{\max}\),

\[
 \sum_{\{x,y\}\in E}|z_xz_y|
 \le
 \Delta_{\max}\sum_x|z_x|^2.
\tag{4.372}
\]

This follows directly from \(2|z_xz_y|\le|z_x|^2+|z_y|^2\).
Combining (4.370)--(4.372) proves, for the complete
\(\Gamma\ne0\) shell,

\[
 \boxed{
 |\mathcal G_{\theta,\beta;\xi,\gamma,\alpha}|
 \ll_{\varepsilon,W}
 T^{\,3-\beta+\theta+\lambda+\varepsilon}.}
\tag{4.373}
\]

Neither Möbius cancellation nor cancellation between different
vertices is used in (4.373).  Comparison with (4.362) gives the exact
unconditional coverage condition

\[
\boxed{
 \theta+\lambda\le\frac{249}{250}.}
\tag{4.374}
\]

Equivalently, the newly covered polytope is

\[
\boxed{
 \frac12<\theta\le\frac{249}{250},
 \qquad
 0\le\xi\le
 1-\beta+\frac{249}{250}-\theta.}
\tag{4.375}
\]

For example, at

\[
 (\theta,\beta,\xi)=\left(\frac34,\frac23,\frac13\right)
\tag{4.376}
\]

one has \(\lambda=0\), graph bound exponent \(37/12\), and margin

\[
 \left(4-\frac23-\frac1{250}\right)-\frac{37}{12}
 =\boxed{\frac{123}{500}}.
\tag{4.377}
\]

At the largest determinant on the same distance shell,
\(\xi=13/12\), one has \(\lambda=3/4\); (4.373) has exponent
\(23/6\) and misses the target by \(63/125\).  At the top distance
\(\theta=1\), even \(\lambda=0\) misses by \(1/250\).  Hence the exact
residual after (4.374) is

\[
\boxed{
\begin{cases}
 \xi>1-\beta+249/250-\theta,
   &1/2<\theta\le249/250,\\
 0\le\xi\le1-\beta+\theta,
   &249/250<\theta\le1.
\end{cases}}
\tag{4.378}
\]

The adapter transition_gamma_graph_energy_audit records
(4.367)--(4.378), including both a covered and an uncovered rational
witness.  It sets shell_covered_unconditionally=True exactly on
(4.374), but keeps published_coverage=False because this is the new
local graph-energy argument above rather than an external theorem.  It
does not mark the whole transition face covered.

### 4.44 Gcd-sensitive graph-degree sharpening

The graph degree in (4.370) deliberately ignored the two gcd shells in
(4.352).  They give an additional unconditional reduction.  Fix the
first vertex \(x_1=(a_1,s_1)\).  On the shell

\[
 d_a=(a_1,a_2)\asymp T^\alpha,
\tag{4.379}
\]

the integer \(d_a\) is a divisor of \(a_1\).  There are
\(T^\varepsilon\) possible divisors in the shell, and for each one
there are \(O(T^{1-\beta-\alpha})\) multiples \(a_2\) in its dyadic
interval.  This replaces the \(T^{1-\beta}\) factor in (4.370).

Likewise \(d_s=(s_1,s_2)\asymp T^\gamma\) is a divisor of \(s_1\).
The intersection of the determinant interval and the shifted window
has raw length exponent

\[
 \lambda_0=
 \max\!\left(0,\min\!\left(\theta,\xi-1+\beta\right)\right).
\tag{4.380}
\]

Counting only multiples of \(d_s\) changes this to

\[
 \boxed{\lambda_\gamma=\max(0,\lambda_0-\gamma).}
\tag{4.381}
\]

Thus the gcd-sensitive maximum degree is

\[
 \boxed{
 \Delta_{\max}(\alpha,\gamma)
 \ll T^{\,1-\beta-\alpha+\lambda_\gamma+\varepsilon}.}
\tag{4.382}
\]

Combining (4.382) with the same vertex energy (4.371) proves

\[
 \boxed{
 |\mathcal G_{\theta,\beta;\xi,\gamma,\alpha}|
 \ll_{\varepsilon,W}
 T^{\,3-\beta+\theta-\alpha+\lambda_\gamma+\varepsilon}.}
\tag{4.383}
\]

The exact enlarged coverage condition is therefore

\[
\boxed{
 \theta-\alpha+\lambda_\gamma\le\frac{249}{250}.}
\tag{4.384}
\]

This removes part of the top distance face.  On the maximal determinant
shell \((\theta,\xi)=(1,1-\beta+1)\), one has
\(\lambda_0=1\), so (4.384) becomes

\[
 \boxed{\alpha+\gamma\ge\frac{251}{250}.}
\tag{4.385}
\]

For the rational witness

\[
 \left(\theta,\beta,\xi,\gamma,\alpha\right)
 =
 \left(1,\frac23,\frac43,1,\frac1{100}\right),
\tag{4.386}
\]

one has \(\lambda_\gamma=0\), maximum-degree exponent \(97/300\),
graph exponent \(997/300\), and positive target margin

\[
 \boxed{\frac3{500}}.
\tag{4.387}
\]

By contrast, the primitive-gcd top witness

\[
 \left(1,\frac23,\frac43,0,0\right)
\tag{4.388}
\]

has \(\lambda_\gamma=1\), maximum-degree exponent \(4/3\), graph
exponent \(13/3\), and deficit \(251/250\).  Thus the remaining top
problem is forced toward small \((a_1,a_2)\) and small
\((s_1,s_2)\), rather than being uniform over all gcd geometries.

The adapter transition_gamma_gcd_graph_energy_audit records
(4.379)--(4.388).  It sets shell_covered_unconditionally=True exactly
when (4.384) holds, uses no Möbius cancellation, and keeps
published_coverage=False.

### 4.45 Primitive cross-determinant lattice removes the rounding loss

There is a further exact improvement in the small-\(\xi\) region.
Return to the common-\(b\) identities

\[
 w_i=a_ib-ks_i,\qquad (a_i,s_i)=1.
\tag{4.389}
\]

They imply both

\[
 \boxed{a_2w_1-a_1w_2=k\Gamma}
\tag{4.390}
\]

and

\[
 \boxed{(a_i,w_i)=(a_i,ks_i)\mid k.}
\tag{4.391}
\]

The slope \(k\) belongs to a fixed finite set, so the content of the
linear form in (4.390) is uniformly bounded.

Fix the first vertex \((a_1,w_1)\), and fix one value
\(\Delta=k\Gamma\).  If a solution \((a_2^{(0)},w_2^{(0)})\) exists,
all solutions are

\[
 (a_2,w_2)=
 (a_2^{(0)},w_2^{(0)})
 t\left(\frac{a_1}{g},\frac{w_1}{g}\right),
 \qquad g=(a_1,w_1).
\tag{4.392}
\]

Because \(a_2\asymp a_1\), \(w_2\asymp w_1\), and \(g\mid k\),
only \(O_k(1)\) integers \(t\) occur in the dyadic rectangle.  A
determinant shell \(|\Gamma|\asymp T^\xi\) contains
\(O_k(T^{\xi+\varepsilon})\) admissible values of \(\Delta\).
Consequently its graph degree satisfies

\[
 \boxed{\Delta_{\max}\ll_k T^{\,\xi+\varepsilon}.}
\tag{4.393}
\]

This removes the \(T^{1-\beta}\) rounding term that appeared when one
bounded the number of \(s_2\) separately for every \(a_2\).
Combining (4.393) with the reciprocal-cluster vertex energy (4.371)
gives

\[
 \boxed{
 |\mathcal G_{\theta,\beta;\xi,\gamma,\alpha}|
 \ll_{\varepsilon,W,k}
 T^{\,2+\theta+\xi+\varepsilon}.}
\tag{4.394}
\]

No Möbius or inter-vertex phase cancellation is used.  Comparing
(4.394) with (4.362), the exact coverage condition is

\[
 \boxed{\theta+\xi\le2-\beta-\frac1{250}.}
\tag{4.395}
\]

This condition is stronger than (4.374) whenever
\(\xi<1-\beta\).  In particular, on the top distance face
\(\theta=1\), it closes

\[
 \boxed{0\le\xi\le1-\beta-\frac1{250}.}
\tag{4.396}
\]

At the rational covered witness

\[
 (\theta,\beta,\xi)=\left(1,\frac23,\frac14\right),
\tag{4.397}
\]

the graph exponent is \(13/4\) and the target margin is

\[
 \boxed{\frac{119}{1500}}.
\tag{4.398}
\]

The exact boundary is \(\xi=247/750\), where the margin is zero.  At
\(\xi=1/3\), (4.394) has exponent \(10/3\) and misses the fixed target
by \(1/250\).  Thus the primitive top residual is no longer the full
determinant range: it begins only in the thin high-determinant region

\[
 \boxed{
 1-\beta-\frac1{250}<\xi\le1-\beta+1.}
\tag{4.399}
\]

The adapter transition_cross_determinant_lattice_audit records
(4.389)--(4.399).  The helper factor_cross_determinant_identity
verifies (4.390)--(4.391) on exact finite fixtures.  The adapter sets
shell_covered_unconditionally=True exactly on (4.395) and keeps
published_coverage=False.

### 4.46 Exact Farey--Hecke orbit of the remaining band

The high-determinant residual in (4.399) has an exact generalized
Kloosterman interpretation.  Split the signs of \(w_i\), and put

\[
 \epsilon_i=\operatorname{sgn}(w_i),\qquad
 W_i=|w_i|,\qquad x_i=\epsilon_i s_i.
\tag{4.400}
\]

Then \((x_i,W_i)=1\), and the cross determinant is

\[
\boxed{
 x_1W_2-x_2W_1
 =-\epsilon_1\epsilon_2\,b\Gamma.}
\tag{4.401}
\]

The full square phase, including the reciprocity corrections, is

\[
\boxed{
 e\!\left(
   \frac{n_1\overline{x_1}}{W_1}
  -\frac{n_2\overline{x_2}}{W_2}
  -\frac{n_1}{s_1w_1}
  +\frac{n_2}{s_2w_2}
 \right).}
\tag{4.402}
\]

No sign is hidden in (4.402).  Moreover the two factor weights are
recovered from the matrix entries by the exact formula

\[
\boxed{
 a_i=\frac{\epsilon_i(W_i+kx_i)}b.}
\tag{4.403}
\]

Thus \(b\mid W_i+kx_i\), with the positivity and dyadic support of
\(a_i\) retained.

For fixed signs, define the remaining determinant-orbit sum

\[
\boxed{
\begin{aligned}
 \mathcal H_{\theta,\beta;\xi,\gamma,\alpha}
 :={}&
 \sum_{\substack{b\asymp T^\beta,\ \mu(b)^2=1\\
                  \epsilon_i x_i\asymp T,\ W_i\asymp T^\theta\\
                  (x_i,W_i)=1\\
                  b\mid W_i+kx_i\\
                  a_i=\epsilon_i(W_i+kx_i)/b
                       \asymp T^{1-\beta}\\
                  x_1W_2-x_2W_1
                    =-\epsilon_1\epsilon_2b\Gamma\\
                  |\Gamma|\asymp T^\xi\\
                  (|x_1|,|x_2|)\asymp T^\gamma\\
                  (a_1,a_2)\asymp T^\alpha}}
 c_U(a_1)c_U(a_2)\mu(|x_1|)\mu(|x_2|)\\
 &\quad\times
 \sum_{n_1,n_2}
 \nu_1(n_1)\overline{\nu_2(n_2)}
 \widetilde{\mathscr W}_{q,k}
 (b,\boldsymbol x,\boldsymbol W,\boldsymbol n)\\
 &\quad\times
 e\!\left(
   \frac{n_1\overline{x_1}}{W_1}
  -\frac{n_2\overline{x_2}}{W_2}
  -\frac{n_1}{\epsilon_1x_1\epsilon_1W_1}
  +\frac{n_2}{\epsilon_2x_2\epsilon_2W_2}
 \right).
\end{aligned}}
\tag{4.404}
\]

The last two rational terms have deliberately not been suppressed;
\(\epsilon_i^2=1\) reduces their denominators to \(x_iW_i=s_iw_i\),
but the displayed form records their origin.  All \(q\)-coprimalities,
endpoint tapers, shell cutoffs, and the coupled transform kernel are
part of \(\widetilde{\mathscr W}_{q,k}\).

The determinant/Hecke index in (4.401) has exponent

\[
 \boxed{\beta+\xi.}
\tag{4.405}
\]

At the first uncovered top witness
\((\theta,\beta,\xi)=(1,2/3,1/3)\), this index has length \(T\); at the
maximal determinant \(\xi=4/3\), it has length \(T^2\).  The required
local inequality remains

\[
 \boxed{
 |\mathcal H_{\theta,\beta;\xi,\gamma,\alpha}|
 \ll_{\varepsilon,W}
 T^{\,4-\beta-1/250+\varepsilon}.}
\tag{4.406}
\]

The location of the arithmetic weights matters.  Cauchy has changed
the common factor from \(\mu(b)\) to \(\mu(b)^2\), while \(\Gamma\)
has no Möbius weight.  Hence the Hecke index
\(-\epsilon_1\epsilon_2b\Gamma\) is not Möbius weighted.  The two
genuine Möbius weights remain on the residue entries \(x_1,x_2\), and
the coefficients \(c_U(a_i)\) depend jointly on \(x_i,W_i,b\) through
(4.403).  A classical Kuznetsov formula for freely completed residue
classes therefore does not directly imply (4.406).

The helper factor_farey_hecke_orbit_identity verifies
(4.401)--(4.403), including both signs and the complete rational
phase, on exact finite fixtures.  The adapter
transition_farey_hecke_orbit_audit records the index, entry, modulus,
and product-frequency scales.  It keeps
classical_kuznetsov_adapter_verified=False,
new_entry_weighted_hecke_estimate_proved=False, and
published_coverage=False.

### 4.47 Second Möbius factorization and exact double reciprocity

Factor one of the two remaining entry Möbius weights with the same
cutoff \(U=T^{1/3}\).  For \(|x|>U\),

\[
 \mu(|x|)
 =-\sum_{\substack{cd=|x|\\c>U}}c_U(c)\mu(d).
\tag{4.407}
\]

Put

\[
 x=\epsilon cd,\qquad
 d\asymp T^\eta,\qquad
 c\asymp T^{1-\eta},\qquad
 0\le\eta\le\frac23.
\tag{4.408}
\]

The second reciprocity step is especially clean.  The Farey phase and
the correction retained in (4.402) satisfy the exact identity

\[
\boxed{
 e\!\left(
   \frac{n\overline{x}}W-\frac{n}{xW}
 \right)
 =
 e\!\left(-\frac{\epsilon n\overline W}{cd}\right).}
\tag{4.409}
\]

Thus the first Archimedean correction cancels; it is not being
discarded.  Formula (4.409) produces a denominator \(cd\) with fixed
factor \(c\), and the formal Wright variables have exponent scales

\[
 M=W=T^\theta,\qquad
 N=d=T^\eta,\qquad
 R_{\mathrm{fix}}=c=T^{1-\eta},\qquad
 A=n=T.
\tag{4.410}
\]

The size hypothesis \(M\le N^2\) becomes

\[
 \boxed{\theta\le2\eta.}
\tag{4.411}
\]

On the top face this already rejects every \(\eta<1/2\).

The actual coefficient is not separated after (4.409).  From (4.403),

\[
 \boxed{
 a=\frac{\epsilon W+kcd}{b},}
\tag{4.412}
\]

so \(c_U(a)\), the condition \(a\asymp T^{1-\beta}\), the determinant
shell, and the coupled transform kernel all depend jointly on
\((W,c,d,b)\).  Fixing \(c\) does not remove that dependence.

Even if these coefficient failures are ignored, the exponent ledger
does not close.  At the most favorable Type-II endpoint
\(\eta=2/3\), the fixed-factor adapter, including the outer trivial
\(c\)-sum, returns saving exponent

\[
 -1.
\tag{4.413}
\]

The factor-box target requires saving \(1/500\), so the optimistic
deficit is

\[
 \boxed{\frac1{500}-(-1)=\frac{501}{500}.}
\tag{4.414}
\]

Both entry Möbius weights would have to be treated jointly with the
determinant equation to avoid the two outer fixed-factor losses.
Applying the published fixed-factor theorem separately is therefore
neither formally applicable nor exponent-sufficient.

The helper entry_double_reciprocity_identity verifies (4.409) for both
signs on exact rational fixtures.  The adapter
transition_entry_mobius_factorization_audit records (4.407)--(4.414),
including the failed size range, the endpoint deficit, and all three
joint coefficient dependencies.  It keeps
actual_wright_coefficient_hypotheses_verified=False,
two_entry_type_ii_estimate_proved=False, and
published_coverage=False.

### 4.48 Combined factor/shift gcd reduction

The cross-determinant lattice in Section 4.45 has another exact
divisibility.  Put

\[
 d_a=(a_1,a_2)\asymp T^\alpha,\qquad
 d_w=(w_1,w_2)\asymp T^\omega.
\tag{4.415}
\]

Both \(d_a\) and \(d_w\) divide the left side of (4.390), hence divide
\(k\Gamma\).  Their common divisor satisfies

\[
 (d_a,d_w)\mid(a_1,w_1)\mid k.
\tag{4.416}
\]

Since \(k\) is fixed, (4.416) proves

\[
 \boxed{\frac{d_ad_w}{(d_a,d_w)}\mid k\Gamma}
\tag{4.417}
\]

with only bounded content.  In exponent language every nonempty shell
therefore satisfies

\[
 0\le\alpha\le1-\beta,\qquad
 0\le\omega\le\theta,\qquad
 \alpha+\omega\le\xi.
\tag{4.418}
\]

For fixed \(d_a,d_w\), the determinant values in a
\(T^\xi\)-shell are restricted to multiples of their lcm.  There are
at most

\[
 T^{\,(\xi-\alpha-\omega)_++\varepsilon}
\tag{4.419}
\]

such values.  Section 4.45 gives \(O_k(1)\) points in the dyadic
rectangle for each value, so the gcd-sensitive graph degree is

\[
 \boxed{
 \Delta_{\max}(\alpha,\omega)
 \ll_{\varepsilon,k}
 T^{\,(\xi-\alpha-\omega)_++\varepsilon}.}
\tag{4.420}
\]

Combining (4.420) with (4.371) proves

\[
 \boxed{
 |\mathcal G_{\theta,\beta;\xi,\gamma,\alpha,\omega}|
 \ll_{\varepsilon,W,k}
 T^{\,2+\theta+(\xi-\alpha-\omega)_++\varepsilon}.}
\tag{4.421}
\]

The new exact coverage condition is

\[
\boxed{
 \theta+(\xi-\alpha-\omega)_+
 \le2-\beta-\frac1{250}.}
\tag{4.422}
\]

On the first top residual \((\theta,\beta,\xi)=(1,2/3,1/3)\),
already \(\alpha+\omega\ge1/250\) makes (4.422) true.  For example,
\((\alpha,\omega)=(1/100,0)\) gives graph exponent \(997/300\)
and margin

\[
 \boxed{\frac3{500}}.
\tag{4.423}
\]

On the maximal top determinant \(\xi=4/3\), condition (4.422)
becomes

\[
 \boxed{\alpha+\omega\ge\frac{251}{250}.}
\tag{4.424}
\]

The witness \((\alpha,\omega)=(1/3,3/4)\) has reduced determinant
exponent \(1/4\), graph exponent \(13/4\), and margin \(119/1500\).
The primitive witness \((\alpha,\omega)=(0,0)\) retains graph exponent
\(13/3\) and deficit \(251/250\).

Thus the surviving high-determinant band must satisfy the strict
reverse inequality

\[
 \boxed{
 \theta+(\xi-\alpha-\omega)_+
 >2-\beta-\frac1{250},}
\tag{4.425}
\]

in addition to the earlier \(a\)- and \(s\)-gcd residual condition.
It is now concentrated simultaneously near primitive factor pairs and
primitive shifted pairs.

The helper factor_cross_gcd_divisibility verifies (4.416)--(4.417) on
exact finite fixtures.  The adapter transition_cross_gcd_lattice_audit
records (4.415)--(4.425), uses no Möbius cancellation, sets
shell_covered_unconditionally=True precisely on (4.422), and keeps
published_coverage=False.

### 4.49 Triple-gcd determinant-value reduction

The entry gcd from (4.352) can be combined with both gcds in
Section 4.48.  Write

\[
 d_a=(a_1,a_2),\qquad
 d_s=(s_1,s_2),\qquad
 d_w=(w_1,w_2).
\tag{4.426}
\]

Primitivity of each column gives the exact coprimalities

\[
 \boxed{(d_a,d_s)=1,\qquad(d_s,d_w)=1.}
\tag{4.427}
\]

As before, \((d_a,d_w)\mid k\).  Since \(d_a,d_s\mid\Gamma\) and
\(d_w\mid k\Gamma\), equations (4.416)--(4.427) imply

\[
 \boxed{
 \frac{d_ad_sd_w}{(d_a,d_w)}\mid k\Gamma.}
\tag{4.428}
\]

Consequently a nonempty exponent shell must satisfy

\[
 \boxed{\alpha+\gamma+\omega\le\xi.}
\tag{4.429}
\]

After fixing the three gcd shells, the number of possible determinant
values is at most

\[
 T^{\,(\xi-\alpha-\gamma-\omega)_++\varepsilon}.
\tag{4.430}
\]

The bounded fixed-value fiber from (4.392) therefore gives

\[
 \boxed{
 \Delta_{\max}(\alpha,\gamma,\omega)
 \ll_{\varepsilon,k}
 T^{\,(\xi-\alpha-\gamma-\omega)_++\varepsilon}.}
\tag{4.431}
\]

Together with (4.371), this proves

\[
 \boxed{
 |\mathcal G_{\theta,\beta;\xi,\gamma,\alpha,\omega}|
 \ll_{\varepsilon,W,k}
 T^{\,2+\theta+
       (\xi-\alpha-\gamma-\omega)_++\varepsilon}.}
\tag{4.432}
\]

The complete triple-gcd coverage criterion is

\[
\boxed{
 \theta+(\xi-\alpha-\gamma-\omega)_+
 \le2-\beta-\frac1{250}.}
\tag{4.433}
\]

Thus, on the first top residual
\((\theta,\beta,\xi)=(1,2/3,1/3)\), any

\[
 \alpha+\gamma+\omega\ge\frac1{250}
\tag{4.434}
\]

closes.  The witness \((\alpha,\gamma,\omega)=(0,1/100,0)\) has
graph exponent \(997/300\) and margin \(3/500\).

On the maximal determinant \(\xi=4/3\), condition (4.433) becomes

\[
 \boxed{\alpha+\gamma+\omega\ge\frac{251}{250}.}
\tag{4.435}
\]

For
\[
 (\alpha,\gamma,\omega)
 =\left(\frac13,\frac13,\frac5{12}\right),
\tag{4.436}
\]
the reduced determinant exponent is \(1/4\), the graph exponent is
\(13/4\), and the margin is \(119/1500\).  The triple-primitive
witness \((0,0,0)\) still has exponent \(13/3\) and deficit
\(251/250\).

After all unconditional graph reductions, a residual shell must obey

\[
\boxed{
 \theta+(\xi-\alpha-\gamma-\omega)_+
 >2-\beta-\frac1{250}.}
\tag{4.437}
\]

This is the sharpest current elementary localization: the new
two-entry Möbius estimate is needed only where all three pairwise gcd
exponents are jointly too small to offset the determinant length.

The helper factor_triple_gcd_divisibility verifies
(4.427)--(4.428) on exact nonzero-determinant fixtures.  The adapter
transition_triple_gcd_lattice_audit records (4.426)--(4.437), sets
shell_covered_unconditionally=True exactly on (4.433), uses no Möbius
cancellation, and keeps published_coverage=False.

### 4.50 One final two-entry square-root theorem

Sections 4.45--4.49 show that the remaining transition-face estimate
has a natural normalization which removes the artificial \(1/250\)
slack.  Put

\[
 g=\alpha+\gamma+\omega,\qquad
 \rho_\Gamma=(\xi-g)_+.
\tag{4.438}
\]

The current graph-energy exponent is

\[
 2+\theta+\rho_\Gamma.
\tag{4.439}
\]

There are two genuine length-\(T\) Möbius residue entries in (4.404).
Square-root cancellation in each entry means one full power of saving
in the expanded square.  The resulting local exponent is

\[
 \boxed{1+\theta+\rho_\Gamma.}
\tag{4.440}
\]

Compare (4.440) with the raw Type-II square target \(4-\beta\).
Using \(\rho_\Gamma=\xi-g\) on every nonempty residual shell gives the
exact identity

\[
\boxed{
\begin{aligned}
 &(4-\beta)-(1+\theta+\rho_\Gamma)\\
 &\qquad=
 2(1-\theta)+(1-\beta+\theta-\xi)+g
 \ge0.
\end{aligned}}
\tag{4.441}
\]

Every term on the right is nonnegative by support.  Equality holds if
and only if

\[
 \boxed{
 \theta=1,\qquad
 \xi=1-\beta+\theta,\qquad
 \alpha=\gamma=\omega=0.}
\tag{4.442}
\]

Thus there is only one power-critical face.

To state the missing theorem without hiding logarithms, let
\(\mathcal H^\circ\) denote (4.404) with the four squared endpoint
tapers replaced by bounded smooth cutoffs, while retaining the
product-frequency coefficients and every other weight.  The exact
transition theorem required is

\[
\boxed{
 |\mathcal H^\circ_{\theta,\beta;\xi,\gamma,\alpha,\omega}|
 \ll_W
 T^{\,1+\theta+\rho_\Gamma}
 (\log T)^{1+o(1)}.}
\tag{4.443}
\]

The single displayed logarithm is the product energy (4.321);
(4.443) permits no additional fixed positive power of \(\log T\).
Equivalently, after restoring the four actual endpoint tapers, the
critical face must satisfy

\[
 |\mathcal H_{\mathrm{crit},\beta}|
 \ll_W
 T^{\,4-\beta}(\log T)^{-3+o(1)}.
\tag{4.444}
\]

Cauchy in \(b\) turns (4.444) into

\[
 |\mathcal F_{\mathrm{crit},\beta}|
 \ll_W
 T^2(\log T)^{-3/2+o(1)}.
\tag{4.445}
\]

There are \(O(\log T)\) dyadic \(\beta\)-boxes, while the top
\(\theta\)-shell, maximal determinant shell, signs, and slopes have
bounded multiplicity at the critical face.  Hence their union is

\[
 \ll_W T^2(\log T)^{-1/2+o(1)}.
\tag{4.446}
\]

Finally the same \(q\)-normalization as in (4.326) gives

\[
 \boxed{
 O_W\!\left(T(\log T)^{-1/2+o(1)}\right)=o_W(T).}
\tag{4.447}
\]

Every noncritical shell has the positive power margin in (4.441), so
all fixed polylogarithmic partition losses are absorbed there.
Consequently (4.443), together with the unconditional graph regions
already proved, closes the entire remaining far-shell transition
family.  It does not by itself certify the separate nontransition
residual families recorded elsewhere in this document.

The adapter transition_final_two_entry_gate_audit records
(4.438)--(4.447), verifies the margin identity and uniqueness of the
critical face, and records the net \(1/2\) logarithmic saving.  It
keeps two_entry_square_root_gate_proved=False and
whole_transition_face_covered=False until (4.443) is proved.

### 4.51 Critical h-Poisson determinant line

There is a second exact representation of the same transition
obstruction which does not first factor either Möbius entry.  It exposes
an additional unimodularity that is hidden in (4.404).  Return to
\(\mathrm{TFS}_\theta(q,k)\) in (4.328), put

\[
 H=L=T^{1/2},\qquad D=T^\theta,
 \qquad \frac12<\theta\le1,
\tag{4.448}
\]

and, with all the other variables fixed, define

\[
 \phi_{s,w,\delta}(u)
 :=\Psi_{q,k}\!\left(
   \frac sT,\frac wD,u,\frac\delta L\right),
 \qquad
 \widehat\phi_{s,w,\delta}(\xi)
 :=\int_{\mathbb R}\phi_{s,w,\delta}(u)e(-u\xi)\,du.
\tag{4.449}
\]

Poisson summation in the complete integer \(h\)-sum is the exact
identity

\[
\boxed{
 \sum_{h\in\mathbb Z}
 \phi_{s,w,\delta}(h/H)
 e\!\left(-\frac{h\delta\bar w}{s}\right)
 =H\!\sum_{\substack{v,j\in\mathbb Z\\wv-js=\delta}}
 \widehat\phi_{s,w,\delta}\!\left(\frac{Hv}{s}\right).}
\tag{4.450}
\]

Indeed, ordinary Poisson gives
\(H\sum_{\ell\in\mathbb Z}\widehat\phi
(H(\ell+\delta\bar w/s))\).  Setting
\(v=\ell s+\delta\bar w\) and
\(j=(wv-\delta)/s\) is a bijection onto the right side of
(4.450).  Thus no congruence class, sign, or normalization is omitted.
The sum over \(v,j\) in (4.450) is infinite and exact; the derivative
bounds of \(\Psi_{q,k}\) give arbitrary-power decay outside the dual
boxes below.

On the boundary dual box the variables have the scales

\[
 |v|\asymp T^{1/2},\qquad
 |j|\asymp T^{\theta-1/2},\qquad
 |\delta|\asymp T^{1/2}.
\tag{4.451}
\]

Neither \(v\) nor \(j\) is zero on this box.  Put

\[
 g=(|v|,|j|),\qquad v=gv_0,\qquad j=gj_0,
 \qquad \delta=g\delta_0,
 \qquad (v_0,j_0)=1.
\tag{4.452}
\]

Choose \(x,y\in\mathbb Z\) with
\(xv_0+yj_0=1\).  Every solution of the divided determinant equation
\(wv_0-j_0s=\delta_0\), with no omission or multiplicity, is

\[
 w=x\delta_0+j_0n,qquad
 s=-y\delta_0+v_0n,qquad n\in\mathbb Z.
\tag{4.453}
\]

The second Möbius entry is \(r=ks+w\), hence

\[
\boxed{
 \begin{pmatrix}s\\r\end{pmatrix}
 =
 \begin{pmatrix}
  -y&v_0\\x-ky&j_0+kv_0
 \end{pmatrix}
 \begin{pmatrix}\delta_0\\n\end{pmatrix},
 \qquad
 \det\begin{pmatrix}
  -y&v_0\\x-ky&j_0+kv_0
 \end{pmatrix}=-1.}
\tag{4.454}
\]

Thus the two arguments of
\(\mu(s)\mu(r)\) are exactly unimodular integer coordinates, not two
arbitrary affine forms.

Let \(\mathcal K_{q,k,g,v_0,j_0}(\delta_0,n)\) denote

\[
 p_N(qs)p_N(qr)
 \widehat\phi_{s,r-ks,g\delta_0}
 \!\left(\frac{Hgv_0}{s}\right),
\tag{4.455}
\]

multiplied by the original signed dyadic cutoffs.  It is declared zero
unless

\[
 s\asymp T,\quad r\asymp T,\quad r-ks\asymp T^\theta,
 \quad (r,s)=1,\quad(q,rs)=1,
 \quad g\delta_0\asymp T^{1/2}.
\tag{4.456}
\]

All fixed transition factors and the complete transformed kernel remain
inside \(\mathcal K\).  Equations (4.450)--(4.456) give the finite-input,
absolutely convergent identity

\[
\boxed{
 \mathrm{TFS}_\theta(q,k)
 =H\sum_{g\ge1}
  \sum_{\substack{v_0,j_0\in\mathbb Z\setminus\{0\}\\
                   (v_0,j_0)=1}}
  \sum_{\delta_0,n\in\mathbb Z}
  \mu(-y\delta_0+v_0n)
  \mu((x-ky)\delta_0+(j_0+kv_0)n)
  \mathcal K_{q,k,g,v_0,j_0}(\delta_0,n).}
\tag{4.457}
\]

The dependence of \(x,y\) on the primitive slope is explicit.  Changing
the Bezout pair only translates the integer \(n\), so (4.457) is
independent of that choice.

Write \(g\asymp T^\gamma\).  Exact support gives

\[
 0\le\gamma\le\theta-\frac12
\tag{4.458}
\]

and the exponent ledger is

\[
\begin{array}{c|c}
 \text{family}&\log_T\text{-scale}\\ \hline
 g&\gamma\\
 v_0&1/2-\gamma\\
 j_0&\theta-1/2-\gamma\\
 \delta_0&1/2-\gamma\\
 n&1/2+\gamma.
\end{array}
\tag{4.459}
\]

In particular, the inner unimodular area is independent of the shell:

\[
 \boxed{(1/2-\gamma)+(1/2+\gamma)=1.}
\tag{4.460}
\]

The outer \((g,v_0,j_0)\)-family has exponent \(\theta-\gamma\).
Consequently the absolute cardinality before the Poisson factor has
exponent \(1+\theta-\gamma\), and after the factor \(H\) it is

\[
 \boxed{\frac32+\theta-\gamma.}
\tag{4.461}
\]

Comparison with the asymptotic-level local target \(T^2\) shows that
the exact inner saving required is

\[
 \boxed{s_{h\mathrm P}(\theta,\gamma)
 =\left(\theta-\frac12-\gamma\right)_+.}
\tag{4.462}
\]

A square root in the area (4.460) saves \(T^{1/2}\).  Its power margin
over (4.462) is

\[
 \boxed{\frac12-s_{h\mathrm P}(\theta,\gamma)
 =1-\theta+\gamma,}
\tag{4.463}
\]

because (4.458) makes the positive part active except at its upper
endpoint.  Equality in (4.463) occurs if and only if

\[
 \boxed{\theta=1,\qquad\gamma=0.}
\tag{4.464}
\]

This recovers the unique critical face of (4.442) without Type-II
factorization.  At the opposite endpoint
\(\gamma=\theta-1/2\), (4.461) already equals \(2\); the two original
mollifier tapers supply the logarithmic little-oh factor on that maximal
gcd layer without using Möbius cancellation.

The sharp averaged theorem suggested by (4.457) is the diagonal-scale
slope square function.  If \(\mathcal S(g,v_0,j_0)\) denotes the inner
\((\delta_0,n)\)-sum in (4.457) with the endpoint tapers replaced by
bounded smooth cutoffs, the required estimate is

\[
\boxed{
 \sum_{\substack{g\asymp T^\gamma\\
                  |v_0|\asymp T^{1/2-\gamma}\\
                  |j_0|\asymp T^{\theta-1/2-\gamma}\\
                  (v_0,j_0)=1}}
 |\mathcal S(g,v_0,j_0)|^2
 \ll_W T^{1+\theta-\gamma}(\log T)^{o(1)}.}
\tag{4.465}
\]

The right side is exactly the identity-diagonal cardinality.  Cauchy
in the slope family then gives

\[
 \sum_{g,v_0,j_0}|\mathcal S(g,v_0,j_0)|
 \ll_W T^{1/2+\theta-\gamma}(\log T)^{o(1)},
\tag{4.466}
\]

and multiplication by \(H\) yields
\(T^{1+\theta-\gamma}(\log T)^{o(1)}\), with equality at (4.464) and
positive power slack everywhere else.

Equation (4.465) is not yet proved.  Expanding its left side produces
a signed four-Möbius off-diagonal.  Fourier separation of the thin
determinant cutoff has a nonzero zero-frequency component; using the
Davenport bound on the two Möbius exponential sums separately loses the
full thin-strip factor and does not reach the diagonal scale.  Hence
(4.465), rather than a pointwise two-point Chowla assertion, is the
precise new spectral/large-sieve target of this route.

The helper transition_h_poisson_line_identity checks (4.453)--(4.454)
on exact integer fixtures.  The adapter transition_h_poisson_line_audit
records (4.451), (4.458)--(4.464), marks the maximal-gcd layer closed by
absolute counting plus the existing endpoint tapers, and keeps
fixed_slope_square_root_proved=False,
averaged_slope_square_function_proved=False, and
whole_far_shell_covered=False.

### 4.52 Cross-determinant expansion of the critical slope square

The critical case of (4.465) can be reindexed once more.  Fix
\(\theta=1\), \(g=1\), and write the two entries in the expanded square
as

\[
 w_iv-j s_i=\delta_i,qquad
 r_i=ks_i+w_i,qquad i=1,2.
\tag{4.467}
\]

Put

\[
 \boxed{\Delta=r_1s_2-r_2s_1=w_1s_2-w_2s_1.}
\tag{4.468}
\]

If \(\Delta=0\), positivity and
\((r_i,s_i)=1\) give \((r_1,s_1)=(r_2,s_2)\), hence also
\(w_1=w_2\) and \(\delta_1=\delta_2\).  This is exactly the positive
identity diagonal of (4.465), not an off-diagonal family.

For \(\Delta\ne0\), Cramer's rule recovers the unique dual slope:

\[
\boxed{
 v=\frac{s_2\delta_1-s_1\delta_2}{\Delta},
 \qquad
 j=\frac{w_2\delta_1-w_1\delta_2}{\Delta}.}
\tag{4.469}
\]

The signs in (4.469) follow directly from the coefficient matrix

\[
 B=\begin{pmatrix}w_1&-s_1\\w_2&-s_2\end{pmatrix},
 \qquad \det B=-\Delta.
\tag{4.470}
\]

On the critical support
\(|s_i|,|w_i|\asymp T\),
\(|\delta_i|\asymp T^{1/2}\), and
\(|v|,|j|\asymp T^{1/2}\).  Equation (4.469) therefore gives the exact
fraction collar

\[
 \boxed{0<|\Delta|\ll_W T.}
\tag{4.471}
\]

In particular the determinant conductor is one full power smaller than
the unrestricted entry determinant bound \(T^2\).

Let \(\mathcal K_i\) be the two copies of (4.455), with the recovered
\((v,j)\) from (4.469), and retain every support, coprimality, sign, and
endpoint factor.  Removing only the identity diagonal gives the exact
critical off-diagonal

\[
\boxed{
\begin{aligned}
 \mathfrak Q^{\mathrm{crit}}_{q,k}
 :={}&
 \sum_{\substack{r_i,s_i\asymp T\\
                   w_i=r_i-ks_i\asymp T\\
                   (r_i,s_i)=1,\ (q,r_is_i)=1\\
                   0<|\Delta|\ll_W T}}
 \mu(r_1)\mu(s_1)\mu(r_2)\mu(s_2)\\
 &\quad\times
 \sum_{\substack{\delta_1,\delta_2\asymp T^{1/2}\\
  \Delta\mid s_2\delta_1-s_1\delta_2\\
  \Delta\mid w_2\delta_1-w_1\delta_2\\
  |(s_2\delta_1-s_1\delta_2)/\Delta|\asymp T^{1/2}\\
  |(w_2\delta_1-w_1\delta_2)/\Delta|\asymp T^{1/2}\\
  ((s_2\delta_1-s_1\delta_2)/\Delta,
   (w_2\delta_1-w_1\delta_2)/\Delta)=1}}
 \mathcal K_1\overline{\mathcal K_2}.
\end{aligned}}
\tag{4.472}
\]

The desired square-function inequality (4.465) is equivalent to

\[
 \boxed{
 |\mathfrak Q^{\mathrm{crit}}_{q,k}|
 \ll_W T^2(\log T)^{o(1)},}
\tag{4.473}
\]

together with the already retained identity diagonal.  The raw expanded
off-diagonal in (4.472) has exponent

\[
 \boxed{1+2\cdot1=3,}
\tag{4.474}
\]

where the first term is the primitive \((v,j)\)-family and each inner
line has area exponent one.  Thus (4.473) requires exactly one power of
saving.

The two divisibilities in (4.472) do not define two independent
character families.  Each row \((w_i,-s_i)\) is primitive, since
\((w_i,s_i)=(r_i,s_i)=1\).  Hence the first Smith invariant of \(B\)
is one and

\[
 \boxed{
 \operatorname{SNF}(B)=\operatorname{diag}(1,|\Delta|),
 \qquad
 \mathbb Z^2/B\mathbb Z^2\simeq\mathbb Z/|\Delta|\mathbb Z.}
\tag{4.475}
\]

Exact orthogonality therefore uses one cyclic family of
\(|\Delta|\) characters.  On the top shell \(|\Delta|\asymp T\), a
square root in that character family saves \(T^{1/2}\).  The remaining
new saving is precisely

\[
 \boxed{T^{1/2}}
\tag{4.476}
\]

from the signed four-Möbius Hecke-entry sum with the coupled kernel.
This is the same arithmetic obstruction seen from the Farey--Hecke
orbit in Section 4.46, now with conductor, normalization, and residual
exponent fixed by (4.471)--(4.476).

No registered Kuznetsov or spectral-large-sieve theorem supplies
(4.476) with four simultaneous Möbius entry weights and the recovered
shift kernel.  Accordingly, (4.473) and its top-conductor hybrid
Möbius--Hecke saving (4.476) remain unproved.

The helper transition_h_poisson_square_cramer_identity checks
(4.468)--(4.470) on exact integer fixtures.  The adapter
transition_h_poisson_square_offdiagonal_audit records the exponents
\(3\to2\), the determinant collar exponent one, the single cyclic
character family, and the remaining \(1/2\) entry saving; it keeps
hybrid_mobius_hecke_estimate_proved=False and
critical_square_function_proved=False.

### 4.53 Published Kloosterman bilinear bounds do not close the entry gate

The 2025--2026 Kloosterman estimates can now be inserted at their exact
critical scales.  On the top shell of (4.471), put

\[
 c=|\Delta|\asymp T,qquad M=N=T^{1/2}.
\tag{4.477}
\]

Blomer--Pascadi,
[arXiv:2607.24311v1](https://arxiv.org/abs/2607.24311), Theorem 1.1,
states for arbitrary sequences on intervals of length at most \(N\)
that

\[
\begin{aligned}
 &\sum_{m,n}\alpha_m\beta_n S(am,n;c)\\
 &\quad\ll
 \|\alpha\|_2\|\beta\|_2c^{1+o(1)}
 \left(
  \frac{N^{1/8}}{c^{3/32}}
 +\frac{N^{5/16}}{c^{3/16}}
 +\frac{N^{2/3}}{c^{7/18}}
 \right).
\end{aligned}
\tag{4.478}
\]

At (4.477), the three saving exponents are respectively

\[
 \boxed{\frac1{32},\qquad\frac1{32},\qquad\frac1{18}.}
\tag{4.479}
\]

Thus the uniform theorem saves \(T^{1/32-o(1)}\), whereas (4.476)
requires \(T^{1/2}\).  The exact deficit is

\[
 \boxed{\frac12-\frac1{32}=\frac{15}{32}.}
\tag{4.480}
\]

Milićević--Qin--Wu,
[arXiv:2511.07550v1](https://arxiv.org/abs/2511.07550), Theorem 1.1,
has uniform square-root-range saving \(T^{1/100-o(1)}\).  Its deficit is

\[
 \boxed{\frac12-\frac1{100}=\frac{49}{100}.}
\tag{4.481}
\]

Pascadi,
[arXiv:2511.08445v1](https://arxiv.org/abs/2511.08445), obtains the
larger saving \(T^{1/12-o(1)}\) for products of two primes of comparable
size.  This is not uniform over the determinant moduli in (4.471), and
even on that favorable family the deficit remains

\[
 \boxed{\frac12-\frac1{12}=\frac5{12}.}
\tag{4.482}
\]

These comparisons already grant more than the present kernel justifies.
In (4.472), the modulus \(\Delta\), the two recovered Cramer
frequencies, and the coefficient \(\mathcal K_1\overline{\mathcal K_2}\)
all vary jointly with the four matrix entries.  They have not been
reduced to a standard \(S(am,n;c)\) kernel with two coefficient
sequences independent of the external entries and fixed modulus.
Consequently the hypotheses of (4.478) are not verified for the actual
sum.

Even if one grants four independent applications of the strongest
uniform saving in (4.479), contrary to the shared-modulus and coupled
coefficient geometry, the total saving would be only

\[
 4\cdot\frac1{32}=\frac18,
 \qquad
 \boxed{\frac12-\frac18=\frac38}
\tag{4.483}
\]

short of the entry gate.  Hence no routing or tensor-separation repair
can turn these published exponents into (4.473); a genuinely stronger
use of the simultaneous Möbius structure is necessary.

The adapter transition_published_kloosterman_entry_audit records
(4.477)--(4.483), including the optimistic hypothesis failures.  It
keeps standard_kloosterman_kernel_verified=False,
coefficients_separate_from_matrix_entries=False,
fixed_modulus_before_entry_sum_verified=False, and
published_coverage=False.

### 4.54 Exact two-dimensional Poisson formula for the critical shift lattice

There is one further exact normalization available before estimating
(4.472).  For a fixed off-diagonal entry pair put

\[
 B=\begin{pmatrix}w_1&-s_1\\w_2&-s_2\end{pmatrix},
 \qquad z=\binom vj,
 \qquad Bz=\binom{\delta _1}{\delta _2}.
\tag{4.484}
\]

Then

\[
 \det B=s_1w_2-w_1s_2=-\Delta,
 \qquad \operatorname{covol}(B\mathbb Z^2)=|\Delta|.
\tag{4.485}
\]

Let \(F_B\in C_c^\infty(\mathbb R^2)\) be the exact pullback of the
two factors \(\mathcal K_1\overline{\mathcal K_2}\), including their
dyadic shift cutoffs, recovered-\((v,j)\) cutoffs, endpoint tapers, and
the coupled AFE transform.  Thus the inner sum for this entry pair is

\[
 \sum_{\substack{z\in\mathbb Z^2\\(v,j)=1}}F_B(Bz).
\tag{4.486}
\]

The support already recorded in (4.472) gives a fixed constant \(C_W\)
such that \(F_B(Bz)=0\) unless
\(0<\max(|v|,|j|)\le C_WT^{1/2}\).  Hence Möbius inversion is finite:

\[
 \mathbf 1_{(v,j)=1}
 =\sum_{d\mid(v,j)}\mu(d),
 \qquad 1\le d\le C_WT^{1/2}.
\tag{4.487}
\]

With the Fourier convention
\(\widehat F(\xi)=\int_{\mathbb R^2}F(x)e(-x\cdot\xi)\,dx\), Poisson
summation on \(dB\mathbb Z^2\) now gives the exact identity

\[
\boxed{
 \sum_{\substack{z\in\mathbb Z^2\\(v,j)=1}}F_B(Bz)
 =\frac1{|\Delta|}
  \sum_{1\le d\le C_WT^{1/2}}\frac{\mu(d)}{d^2}
  \sum_{m\in\mathbb Z^2}
   \widehat F_B\!\left(\frac{B^{-t}m}{d}\right).}
\tag{4.488}
\]

No primitivity factor or Euler factor has been suppressed in (4.488).
The zero dual frequency is exactly

\[
 \boxed{
 \frac{c_W(T)}{|\Delta|}\widehat F_B(0),
 \qquad
 c_W(T):=\sum_{1\le d\le C_WT^{1/2}}\frac{\mu(d)}{d^2}.}
\tag{4.489}
\]

The comparison with the limiting Euler factor is a separate, absolutely
convergent tail estimate,

\[
 \left|c_W(T)-\frac1{\zeta(2)}\right|
 \le \sum_{d>C_WT^{1/2}}\frac1{d^2}
 \le \frac1{C_WT^{1/2}-1}.
\tag{4.490}
\]

For \(|\Delta|\asymp T^\kappa\), \(0<\kappa\le1\), the shift square
has area exponent one and its lattice covolume has exponent \(\kappa\).
The zero-mode density exponent is therefore \(1-\kappa\).  The entry
pair shell has exponent \(2+\kappa\): four variables of exponent four
subject to a determinant interval of relative width
\(T^{\kappa-2}\).  Consequently

\[
 \boxed{(2+\kappa)+(1-\kappa)=3}
\tag{4.491}
\]

on every determinant shell.  Thus the zero mode alone still requires
one full power to reach the square-function target exponent two; moving
to smaller determinants does not improve this obstruction.

The nonzero dual geometry is one-dimensional at the exponent level.
The largest singular value of \(B\) lies between fixed multiples of
\(T\), and the other equals \(|\Delta|/\sigma_{\max}(B)\).  On
\(d=T^\eta\), \(0\le\eta\le1/2\), the two Fourier-argument spacings in
(4.488) have exponents

\[
 -\frac12-\eta,
 \qquad
 \frac32-\kappa-\eta.
\tag{4.492}
\]

The second is nonnegative throughout the stated polytope.  There are
therefore \(T^{1/2+\eta}\) longitudinal modes and only a bounded number
of transverse modes in compact Fourier support.  After the exact
\(d^{-2}\) factor in (4.488), their weighted exponent is

\[
 \boxed{\frac12-\eta\le\frac12.}
\tag{4.493}
\]

Thus primitive-divisor layers do not enlarge the cyclic-frequency gate
of Section 4.52.  They also do not remove the zero mode: the integral
\(\widehat F_B(0)\) depends jointly on all four entries through the
coupled kernel and is not a product of two entry-independent
coefficients.

The helper transition_delta_lattice_dual_identity verifies
\(\langle Bz,B^{-t}m\rangle=\langle z,m\rangle\) using integral
adjugate numerators.  The adapter
transition_delta_lattice_poisson_audit records (4.489)--(4.493), the
finite primitive coefficient, and the unchanged one-power zero-mode
deficit.  It keeps zero_mode_weight_separates_in_the_entries=False,
zero_mode_mobius_variance_proved=False, and
whole_delta_lattice_covered=False.

### 4.55 Denominator-gcd extraction leaves one two-Möbius line-family gate

The zero mode in (4.489) can be reorganized without losing the four
Möbius weights.  On a dyadic determinant shell
\(D=T^\kappa\), extract

\[
 g=(s_1,s_2)=T^\gamma,
 \qquad s_1=ga,\quad s_2=gb,\quad(a,b)=1,
 \qquad 0\le\gamma\le\kappa.
\tag{4.494}
\]

The divisibility \(g\mid\Delta\) is exact.  With

\[
 h=\frac\Delta g,
\tag{4.495}
\]

the determinant equation becomes

\[
 \boxed{br_1-ar_2=h.}
\tag{4.496}
\]

Choose once and for all the representative
\(0\le\rho_1<a\) satisfying
\(b\rho_1\equiv h\pmod a\), and put
\(\rho_2=(b\rho_1-h)/a\).  Every integral solution of (4.496), and no
other pair, is

\[
 \boxed{r_1=\rho_1+an,\qquad r_2=\rho_2+bn,\qquad n\in\mathbb Z.}
\tag{4.497}
\]

If the original Möbius product is nonzero, then \(g,a,b\) are
squarefree where applicable and
\((g,ab)=(a,b)=1\).  Therefore

\[
 \boxed{\mu(s_1)\mu(s_2)
 =\mu(ga)\mu(gb)=\mu(a)\mu(b).}
\tag{4.498}
\]

In particular the common factor carries no residual Möbius sign.  Let
\(\Psi_{q,k,D,G}\) denote the exact pullback of the zero-mode weight in
(4.489).  It is supported on

\[
\begin{gathered}
 G<g\le2G,\qquad T/G<a,b\le2T/G,\qquad(a,b)=1,\quad(g,ab)=1,\\
 D/G<|h|\le2D/G,\qquad
 T<r_i=\rho_i+(a,b)_i n\le2T,\\
 w_i=r_i-ks_i\ \text{in its fixed signed dyadic interval},\\
 (r_i,s_i)=1,\qquad(q,r_1r_2s_1s_2)=1,
\end{gathered}
\tag{4.499}
\]

and retains both endpoint tapers, all AFE transforms, and the factor
\(c_W(T)/|gh|\).  The resulting local sum is exactly

\[
\boxed{
\begin{aligned}
 \mathfrak Z_{q,k}(D,G)
 :={}&\sum_{G<g\le2G}\mu^2(g)
 \sum_{\substack{a,b\asymp T/G\\(a,b)=1,(g,ab)=1}}
 \mu(a)\mu(b)\\
 &\times\sum_{D/G<|h|\le2D/G}
 \sum_{n\in\mathbb Z}
 \mu(\rho_1+an)\mu(\rho_2+bn)
 \Psi_{q,k,D,G}(g,a,b,h,n).
\end{aligned}}
\tag{4.500}
\]

Here \(a,b\asymp T/G\) is only an abbreviation for the two explicit
half-open intervals in (4.499); (4.500) contains no omitted arithmetic
condition.

The exact exponent table for (4.500) is

\[
\begin{array}{c|c}
\text{family}&\text{exponent}\\ \hline
(g,a,b)&2-\gamma\\
h=\Delta/g&\kappa-\gamma\\
n\text{ on the solution line}&\gamma\\ \hline
\text{raw total}&2+\kappa-\gamma.
\end{array}
\tag{4.501}
\]

Both remaining denominator Möbius variables have length exponent
\(1-\gamma\).  Square-root cancellation in their product saves
\(1-\gamma\), leaving

\[
 \boxed{(2+\kappa-\gamma)-(1-\gamma)=1+\kappa.}
\tag{4.502}
\]

The target is exponent two, so the power margin is exactly

\[
 \boxed{1-\kappa.}
\tag{4.503}
\]

All shells \(\kappa<1\) would therefore close with fixed power slack.
The only power-critical face is \(\kappa=1\), uniformly in \(\gamma\).
At the subface \(\gamma=\kappa\), absolute counting already reaches
the target.  Away from that subface, the minimal new local theorem is

\[
\boxed{
 |\mathfrak Z_{q,k}(T^\kappa,T^\gamma)|
 \ll_W T^{1+\kappa}\mathscr L^{-C_{\rm agg}-2},
 \qquad 0\le\gamma<\kappa\le1,}
\tag{4.504}
\]

where \(C_{\rm agg}\) is the already explicit global polylogarithmic
loss exponent.  The two extra logarithms make the dyadic
\((D,G)\)-sum and the \(q^{-1}\)-sum convergent at the required
\(o(T)\) level.  Formula (4.504), not four independent Kloosterman
bounds, is the precise Möbius Type-I/II gate left by this route.

No published result audited in Sections 4.46--4.53 proves (4.504) with
the two additional Möbius weights on the moving linear forms in
(4.497).  The helper transition_denominator_gcd_line_identity verifies
(4.494)--(4.497) on integers.  The adapter
transition_denominator_gcd_line_audit records (4.501)--(4.503), marks
the absolute endpoint \(\gamma=\kappa\) covered, and keeps
two_mobius_line_square_root_proved=False elsewhere.

### 4.56 Exact half-cutoff Type-I/II polytope inside the line-family gate

Apply the approved Möbius identity separately to the two cofactor
weights in (4.500).  Put

\[
 A=T^\alpha,\qquad \alpha=1-\gamma,
 \qquad U=V=A^{1/2}.
\tag{4.505}
\]

For the left cofactor, with different letters from the global \(q\),
the finite identity is

\[
\boxed{
 \mu(a)
 =-\sum_{\substack{xy=a\\x>U}}c_U(x)\mu(y)
 =-\sum_{\substack{dey=a\\de>U,\ d\le U}}
      \mu(d)\mu(y).}
\tag{4.506}
\]

The Type-I part has \(y\le V\), and the Type-II part has \(y>V\).
Since \(dey\asymp A\) and \(de>U=A^{1/2}\), every dyadic Type-II box
lies on the boundary exponent \(\log_T y=\alpha/2\); the strict
inequality is retained in the constant-sized dyadic endpoint rather
than replaced by an empty exponent cell.

Write the two factorizations as

\[
 a=d_1e_1y_1,\qquad b=d_2e_2y_2,
\tag{4.507}
\]

and put

\[
 \log_Ty_i=\beta_i,\qquad
 \log_Td_i=\pi_i,\qquad
 \log_Te_i=\varepsilon_i.
\tag{4.508}
\]

The exact rational polytope is

\[
\boxed{
 0\le\beta_i,\pi_i\le\frac\alpha2,
 \qquad
 \varepsilon_i=\alpha-\beta_i-\pi_i\ge0,
 \qquad i=1,2.}
\tag{4.509}
\]

After substitution, the determinant line and the complete arithmetic
weight are

\[
\boxed{
 (d_2e_2y_2)r_1-(d_1e_1y_1)r_2=h,}
\tag{4.510}
\]

\[
 \mu(d_1)\mu(y_1)\mu(d_2)\mu(y_2)
 \mu(r_1)\mu(r_2),
\tag{4.511}
\]

with every condition in (4.499) pulled back through (4.507).  In
particular, neither the moving \(r_i\)-weights nor the coupled kernel is
discarded.

The four new signed Möbius atoms in (4.511) have total exponent

\[
 M_{\rm sign}=\pi_1+\beta_1+\pi_2+\beta_2.
\tag{4.512}
\]

A square root in those four atoms would save \(M_{\rm sign}/2\).  The
total saving required by (4.501) is \(\kappa-\gamma\).  Using (4.509)
gives the exact identity

\[
\boxed{
 (\kappa-\gamma)-\frac{M_{\rm sign}}2
 =\frac{\varepsilon_1+\varepsilon_2}{2}-(1-\kappa).}
\tag{4.513}
\]

Hence the remaining completion requirement in one cell is precisely

\[
\boxed{
 C_{\rm comp}
 =\left(
   \frac{\varepsilon_1+\varepsilon_2}{2}-(1-\kappa)
  \right)_+.}
\tag{4.514}
\]

On the unique top face \(\kappa=1\), (4.514) is exactly half the
unsigned \((e_1,e_2)\)-volume.  Off that face, the previously identified
margin \(1-\kappa\) removes the same amount.  Thus the proposed local
proof has two noninterchangeable inputs:

1. square-root cancellation in the four signed atoms of (4.511), with
   the two moving \(\mu(r_i)\) weights retained; and
2. when \(C_{\rm comp}>0\), completion saving of exactly
   \(T^{C_{\rm comp}}\) in the two unsigned cofactors.

Cells with \(\varepsilon_1=\varepsilon_2=0\) need no unsigned
completion, but their signed-atom square-root estimate is still not a
registered theorem: the determinant equation (4.510) and its kernel
couple all six Möbius weights.  Conversely, applying completion while
discarding the signed weights loses the first term in (4.513) and cannot
close the top face.

The adapter transition_denominator_mobius_type_ii_audit implements
(4.509)--(4.514) with `Fraction`.  It keeps
signed_atom_square_root_proved=False and
unsigned_cofactor_completion_proved=False.  Therefore no non-endpoint
cell is reported covered merely because its exponent identity is
feasible.

### 4.57 Bourgain--Garaev multilinear Kloosterman audit at the balanced cell

The all-signed balanced top cell of Section 4.56 has

\[
 p=T,\qquad
 |d_1|,|y_1|,|d_2|,|y_2|=p^{1/4},
\tag{4.515}
\]

and requires saving \(p^{1/2}\).  Bourgain--Garaev,
[arXiv:1211.4184v1](https://arxiv.org/abs/1211.4184), treats incomplete
multilinear Kloosterman sums with phase

\[
 e_p(a x_1^{-1}\cdots x_n^{-1})
\tag{4.516}
\]

for a fixed prime modulus \(p\).  Its theorems can be compared with
(4.515) before asking whether the actual phase has this form.

Grouping \((d_1,y_1)\) and \((d_2,y_2)\) into two intervals of formal
length \(N_1=N_2=p^{1/2}\), Theorem 9 gives

\[
 p^{1/8}N_1^{3/4}N_2^{3/4}
 \left(\frac{N_1^3}{p}+1\right)^{1/16}
 \left(\frac{N_2^3}{p}+1\right)^{1/16}
 =p^{15/16+o(1)}.
\tag{4.517}
\]

Relative to the formal volume \(p\), this saves \(p^{1/16}\).  The
deficit from the required saving is

\[
 \boxed{\frac12-\frac1{16}=\frac7{16}.}
\tag{4.518}
\]

Theorem 10 with \(k_1=k_2=2\) gives the factor

\[
 p^{1/8}N_1^{-1/6}N_2^{-1/6}=p^{-1/24},
\tag{4.519}
\]

so its deficit is

\[
 \boxed{\frac12-\frac1{24}=\frac{11}{24}.}
\tag{4.520}
\]

The genuinely multilinear Theorem 11 requires \(n\ge7\).  Although
the four intervals in (4.515) satisfy the separate product condition

\[
 N^4=p>p^{1/3+\varepsilon},
\tag{4.521}
\]

their variable count is four, so the theorem does not apply.  Theorem
12 must be read with both its printed proof and the stronger published
remark.  Section 10.4 of the same paper proves the theorem with

\[
 C=9c^{-2},\qquad c\le\frac14,
\tag{4.522}
\]

hence that proof has \(C\ge144\).  Remark 3 immediately following the
theorem states that the result can instead be proved with \(C=4\).
The strongest published threshold at \(n=4\) is therefore

\[
 \boxed{N>p^{4/4^2}=p^{1/4}.}
\tag{4.523}
\]

The interval length in (4.515) is exactly \(p^{1/4}\), so the strict
inequality in (4.523) still fails.  The former \(p^9\) threshold was
only the constant supplied by Section 10.4's particular proof and is
not the strongest published statement; it is retained in the adapter
only as provenance.

Theorem 13, omitted from the earlier audit, permits unequal interval
lengths and assumes

\[
 \prod_{i=1}^n |I_i|>p^{1/2+\varepsilon}.
\tag{4.523a}
\]

The four formal intervals in (4.515) have product \(p\), so (4.523a)
holds for every fixed \(0<\varepsilon<1/2\).  Its conclusion, however,
is only

\[
 \left|\sum_{x_i\in I_i}\prod_i\alpha_i(x_i)
 e_p\!\left(a\prod_i x_i^{-1}\right)\right|
 <p^{-\delta(\varepsilon,n)}\prod_i |I_i|,
\tag{4.523b}
\]

with no numerical value for \(\delta\).  Section 10.5 obtains the
saving after \((2k)^n\)-fold Hölder, where \(k=[2/\varepsilon]\), and
invokes Lemma 1 with an unspecified absolute exponent in
\(\delta'>(\delta/n)^{Cn}\).  Consequently the paper certifies a fixed
positive power but does not certify the \(p^{-1/2}\) required by
(4.515).  This distinction is essential: a statement of
\(p^{-\delta}\) for some \(\delta>0\) cannot be substituted for the
specific half-power saving in (4.504).

Nor can one force Theorem 11 merely by iterating (4.506).  Formally
splitting each of the four \(p^{1/4}\)-atoms into two
\(p^{1/8}\)-atoms would give

\[
 n_{\rm formal}=8\ge7,\qquad (p^{1/8})^8=p>p^{1/3+\varepsilon}.
\tag{4.523c}
\]

But this is not a consequence of the finite Möbius identity.  If an
atom \(m\asymp p^{1/4}\) is prime and one reapplies (4.506) with cutoff
\(p^{1/8}\), then the only nonzero expanded factorization is

\[
 m=(1)\,(m)\,(1),
\tag{4.523d}
\]

where the long factor is unsigned and the two Möbius factors are
units.  Thus the recursive identity contains dyadic cells with one
positive-length factor, and it does not force seven equal positive-
length interval variables.  Such prime atoms occur in the dyadic range
for all sufficiently large conductors.

Even under the counterfactual assumption that (4.523c) were an exact
eight-variable box, Theorem 11 would still give only
\(p^{-\delta(\varepsilon,8)}\) for an unspecified positive \(\delta\),
not the certified \(p^{-1/2}\) saving required here.

These are again optimistic numerical comparisons.  The determinant
\(\Delta\) in (4.488) ranges over composite as well as prime moduli,
and the actual Fourier transform
\(\widehat F_B(B^{-t}m/d)\) has not been converted to the fixed-prime
reciprocal-product phase (4.516).  Thus even the savings in
(4.518)--(4.520) and (4.523b) are not direct inputs to (4.504).  In the
line-Fourier representation used in Section 4.58 the exact phase is

\[
 e_Q\!\left((d_2e_2y_2)r_1-(d_1e_1y_1)r_2-h\right),
\]

a difference of direct product monomials rather than
\(e_p(a\prod x_i^{-1})\).

The adapter transition_bourgain_garaev_multilinear_audit records the
four-variable count, the exact deficits \(7/16\) and \(11/24\), the
Theorem 11 count failure, both Theorem 12 constants, the corrected
threshold (4.523), Theorem 13's formal product margin \(1/2\), and the
missing quantitative half-power.  The separate adapter
transition_bourgain_garaev_iterated_factorization_audit records
(4.523c)--(4.523d).  Both keep published_coverage=False.

### 4.58 Exact line Fourier window and the constant-phase microarc

There is a final frequency boundary that every proposed completion of
(4.500) must retain.  Fix one integer \(g=T^\gamma\) on the top
determinant face, and put

\[
 A=T^{1-\gamma}.
\tag{4.524}
\]

Then \(a,b,h\) have length \(A\), while \(r_1,r_2\) have length \(T\).
For every integer tuple, ordinary character orthogonality gives

\[
\boxed{
 \mathbf1_{br_1-ar_2=h}
 =\int_0^1 e\!\left(\alpha(br_1-ar_2-h)\right)\,d\alpha.}
\tag{4.525}
\]

This identity is inserted before any tensor separation of
\(\Psi_{q,k,D,G}\).  If the signed \(h\)-cutoff is
\(\psi(h/A)\), its exact Poisson formula is

\[
 \sum_{h\in\mathbb Z}\psi(h/A)e(-\alpha h)
 =A\sum_{\ell\in\mathbb Z}
   \widehat\psi\!\left(A(\alpha+\ell)\right).
\tag{4.526}
\]

Thus the complete frequency window has width exponent

\[
 -(1-\gamma).
\tag{4.527}
\]

The two product phases \(br_1\) and \(ar_2\) have scale
\(AT=T^{2-\gamma}\).  Their phase is constant only on the microarc

\[
 \boxed{|\alpha|\ll(AT)^{-1}=T^{-(2-\gamma)}.}
\tag{4.528}
\]

The exponent difference between (4.527) and (4.528) is exactly one:
the full \(h\)-window contains one power of \(T\) constant-phase
microarc scales.  For fixed \(g\), the raw line-family exponent and its
allocated target are respectively

\[
 \boxed{1+2(1-\gamma)=3-2\gamma,\qquad
        1+(1-\gamma)=2-\gamma.}
\tag{4.529}
\]

Their difference is \(1-\gamma\), in agreement with (4.504).

The following calculation is only a diagnostic separated model, not a
replacement for the coupled kernel.  Suppose one tensor component were
constant in the cross variables, and set

\[
 B_{A,T}(\alpha)
 :=\sum_{a\asymp A}\sum_{r\asymp T}
   \mu(a)\mu(r)U(a/A)V(r/T)e(\alpha ar).
\tag{4.530}
\]

On (4.528), the contribution of this component is bounded at its natural
scale by

\[
 A\cdot\frac1{AT}\,|B_{A,T}(0)|^2
 =\frac1T|M_U(A)M_V(T)|^2,
\tag{4.531}
\]

where \(M_U(A)=\sum\mu(a)U(a/A)\), and similarly for \(M_V\).  To reach
the fixed-\(g\) target \(AT\), (4.531) would require

\[
\boxed{|M_U(A)M_V(T)|\ll T\sqrt A.}
\tag{4.532}
\]

The trivial exponent of the product on the left is
\(1+(1-\gamma)\); the target exponent is
\(1+(1-\gamma)/2\).  Hence the missing product saving is exactly

\[
 \boxed{\frac{1-\gamma}{2}.}
\tag{4.533}
\]

Classical zero-free-region bounds for either weighted Mertens sum give
arbitrary logarithmic or subpower savings, not the fixed power in
(4.533).  On the other hand, (4.532) is not declared a necessary
consequence of the actual line gate: the tensor expansion of
\(\Psi_{q,k,D,G}\) has not been proved to contain a nonzero constant
cross component.  The correct conclusion is narrower.  A Kloosterman
estimate valid only outside (4.528) cannot close (4.504) unless it is
paired with either

1. a proof that the actual coupled kernel annihilates the constant
   microarc component; or
2. a Möbius estimate supplying its exact share of (4.533).

The helper transition_line_finite_fourier_identity verifies (4.525) by
finite character orthogonality with a modulus larger than the integer
defect.  The adapter transition_line_fourier_microarc_audit records
(4.527)--(4.533).  It keeps
actual_coupled_weight_tensor_separated=False,
nonzero_constant_tensor_mode_verified=False,
microarc_mertens_reduction_is_actual_gate=False, and
whole_line_family_covered=False.

### 4.59 Balanced Möbius convolution and the exact short-interval variance gate

The determinant-line obstruction has a second formulation which does not
single out the constant microarc.  It packages the entire Fourier window
into one short-interval mean square.  Fix (g=T^\gamma), put

\[
 A=T^{1-\gamma},\qquad X=AT=T^{2-\gamma},
\tag{4.534}
\]

and first take one real tensor component of the smooth weight.  For
(U,V\in C_c^\infty((0,\infty))), define the finite balanced convolution

\[
 \boxed{
 c_{U,V}(n)
 :=\sum_{ar=n}\mu(a)\mu(r)U(a/A)V(r/T).}
\tag{4.535}
\]

Expanding both sides and using no estimate gives the exact identity

\[
\boxed{
\begin{aligned}
 &\sum_{a,b,r_1,r_2}
  \mu(a)\mu(b)\mu(r_1)\mu(r_2)
  U(a/A)U(b/A)V(r_1/T)V(r_2/T)\\
 &\qquad\qquad\times
  \psi\!\left(\frac{br_1-ar_2}{A}\right)\\
 &=\sum_{m,n}c_{U,V}(n)c_{U,V}(m)
  \psi\!\left(\frac{n-m}{A}\right).
\end{aligned}}
\tag{4.536}
\]

Thus the quotient (h=\Delta/g) in (4.496) is literally the additive
difference of two balanced Möbius products.  There is no loss from the
four-to-two reindexing.  For the Fejer weight
(\psi_\triangle(u)=(1-|u|)_+), interval overlap gives the second exact
identity

\[
\boxed{
 \sum_{m,n}c_{U,V}(n)c_{U,V}(m)
  \psi_\triangle\!\left(\frac{n-m}{A}\right)
 =\frac1A\int_{\mathbb R}
   \left|\sum_{x<n\le x+A}c_{U,V}(n)\right|^2dx.}
\tag{4.537}
\]

The left side of (4.537) is nonnegative.  In particular, the original
double centering (2.4) cannot be reused to declare this quadratic
determinant zero mode absent: linear zero rows and columns do not remove
the positive autocorrelation diagonal in (4.537).

The scales in (4.534)--(4.537) are exact.  The product centre has exponent
(2-\gamma), the difference interval has exponent (1-\gamma), and the
raw autocorrelation has exponent

\[
 (2-\gamma)+(1-\gamma)=3-2\gamma.
\tag{4.538}
\]

The diagonal-scale target is (X=T^{2-\gamma}).  Consequently the one
missing power is precisely

\[
 \boxed{A=T^{1-\gamma},}
\tag{4.539}
\]

the same deficit as (4.529).  At the top cell (gamma=0), the former
six-variable gate is therefore reduced to the single explicit inequality

\[
\boxed{
 \frac1T\int_{\mathbb R}
  \left|\sum_{x<n\le x+T}
    \sum_{ar=n}\mu(a)\mu(r)U(a/T)V(r/T)
  \right|^2dx
 \ll_{U,V}T^2(\log T)^{1+o(1)}.}
\tag{4.540}
\]

The four endpoint mollifier tapers occur after squaring, while the
multiplicative product energy costs one logarithm.  Hence (4.540), with
the uniform divisor and kernel seminorms needed below, leaves the same
net three-logarithm saving as (4.444).

Although (4.535) is not itself multiplicative, its multiplicative content
is exact.  With

\[
 \widetilde U(z)=\int_0^\infty U(x)x^{z-1}\,dx,
\tag{4.541}
\]

Mellin inversion gives the absolutely convergent formula

\[
\boxed{
 c_{U,V}(n)=\frac1{(2\pi)^2}\int_{\mathbb R^2}
 \widetilde U(i\tau)\widetilde V(i\upsilon)
 A^{i\tau}T^{i\upsilon}f_{\tau,\upsilon}(n)
 \,d\tau\,d\upsilon,}
\tag{4.542}
\]

where

\[
 f_{\tau,\upsilon}(n)
 :=\sum_{ar=n}\mu(a)a^{-i\tau}\mu(r)r^{-i\upsilon},
 \qquad
 \sum_{n\ge1}\frac{f_{\tau,\upsilon}(n)}{n^s}
 =\frac1{\zeta(s+i\tau)\zeta(s+i\upsilon)}.
\tag{4.543}
\]

All exchanges in (4.542) are justified by the finite divisor sum and the
Schwartz decay of the two Mellin transforms.  This identifies the precise
multiplicative family to which a short-interval theorem would have to be
applied.

The published divisor-bounded theorem of Mangerel,
[arXiv:2108.11401, Theorem 1.7](https://arxiv.org/abs/2108.11401), does
not give (4.540).  Even if it is granted uniformly for every twisted
component in (4.542), its normalized variance estimate has the scale

\[
 \frac1X\int
 \left|\frac1A\sum_{x<n\le x+A}f_{\tau,\upsilon}(n)
 \right|^2dx
 \le o(1)(\log X)^{O(1)}.
\tag{4.544}
\]

Here the long-interval comparison term in the cited theorem has been
optimistically set to zero; retaining it can only add another obligation.
After multiplying by (XA), (4.544) has exponent
(3-2\gamma), exactly the raw exponent (4.538).  It gives logarithmic
decay but none of the required power (4.539).  The 2026 higher-uniformity
theorems concern (mu), (Lambda), or (d_k-d_k^\sharp); they do not
state the square-root variance (4.540) for the balanced coefficients of
(1/\zeta^2).

For the actual weight in (4.500), finite Möbius inversion separates
((a,b)=1), ((r_1,ga)=1), and ((r_2,gb)=1) into divisor layers, and
Mellin inversion separates every compact smooth tensor.  Section 4.60
proves the summable layer density and the required lifted-kernel nuclear
norm.  Thus the actual remaining input is a divisor-uniform version of
(4.540), not merely the separated diagnostic of Section 4.58.

The finite helper transition_balanced_convolution_identity verifies
(4.536)--(4.537) on exact integer data.  The adapter
transition_balanced_mobius_convolution_audit records (4.538)--(4.544),
the four endpoint tapers, and the remaining exponent (1-\gamma).  It
sets actual_coprimality_layers_aggregated=True and
actual_coupled_kernel_nuclear_norm_verified=True after Section 4.60, while
keeping published_square_root_variance_proved=False and
whole_line_family_covered=False.

### 4.60 Exact coprimality layers and a bounded lifted-kernel nuclear norm

It remains to connect (4.540) to every arithmetic condition and every
factor of the actual zero-mode weight in (4.500).  This can be done without
a positive-power loss on the top determinant face.  Assume first that
((q,g)=1); otherwise the local family is empty.  The complete
coprimality indicator is exactly

\[
\boxed{
\begin{aligned}
 &\mathbf1_{(a,b)=1}\mathbf1_{(r_1,ga)=1}
  \mathbf1_{(r_2,gb)=1}\mathbf1_{(q,abr_1r_2)=1}\\
 &\quad=\mathbf1_{(q,abr_1r_2)=1}
 \sum_{d_0\mid(a,b)}\mu(d_0)
 \sum_{d_1\mid(r_1,ga)}\mu(d_1)
 \sum_{d_2\mid(r_2,gb)}\mu(d_2).
\end{aligned}}
\tag{4.545}
\]

Every sum in (4.545) is finite.  For a nonzero layer put

\[
 e_i=(d_i,g),\qquad f_i=d_i/e_i\quad(i=1,2).
\tag{4.546}
\]

Since (d_i) and (g) are squarefree, ((f_i,g)=1).  The four divisibility
conditions in this layer are precisely

\[
 \operatorname{lcm}(d_0,f_1)\mid a,\qquad
 \operatorname{lcm}(d_0,f_2)\mid b,\qquad
 d_1\mid r_1,\qquad d_2\mid r_2.
\tag{4.547}
\]

Hence its exact four-variable volume density is

\[
\boxed{
 \omega_g(d_0,d_1,d_2)
 :=\frac1{d_1d_2
  \operatorname{lcm}(d_0,f_1)
  \operatorname{lcm}(d_0,f_2)}.}
\tag{4.548}
\]

This density is absolutely summable.  At a prime (p\nmid g), summing
over the eight possible memberships of (p) in (d_0,d_1,d_2) gives the
exact local factor

\[
 \boxed{1+\frac3{p^2}+\frac2{p^3}+\frac2{p^4}.}
\tag{4.549}
\]

At a prime (p\mid g), the corresponding factor is

\[
 \boxed{(1+p^{-1})^2(1+p^{-2}).}
\tag{4.550}
\]

Consequently

\[
 \sum_{d_0,d_1,d_2}|\mu(d_0)\mu(d_1)\mu(d_2)|
 \omega_g(d_0,d_1,d_2)
 \ll \prod_{p\mid g}(1+p^{-1})^2
 \ll (\log\log(3g))^2.
\tag{4.551}
\]

No (T^\varepsilon) placeholder is needed in (4.551).

The kernel must be separated in the right coordinates.  If one first
substitutes (h=(br_1-ar_2)) and then differentiates the determinant
cutoff, a normalized transverse derivative can spuriously cost (T).
Instead lift the exact top-shell weight to the five independent variables

\[
 \mathbf x=\left(\frac aA,\frac bA,
                  \frac{r_1}T,\frac{r_2}T,\frac hA\right),
\tag{4.552}
\]

using (gh) in every determinant denominator, and impose
(br_1-ar_2=h) only after the lift.  On the constraint this is exactly the
original weight.  Off the constraint it is merely a smooth extension and
does not change the sum.  Since (gA=T), every entry and every numerator
in the Cramer expressions has its natural normalized scale.  The top-shell
condition (|h|\asymp A) keeps (1/(gh)) away from zero.  The derivative
bounds of the original AFE kernel therefore give, for every multi-index
(\nu),

\[
 \|\partial_{\mathbf x}^{\nu}\mathscr W_{q,k,g}\|_1
 \ll_{\nu,W}(\log T)^{C_\nu},
\tag{4.553}
\]

with no positive power of (T).

Fourier inversion in the five variables is exact.  Moreover, applying
(1-\partial_{x_j}^2) in each coordinate gives

\[
\boxed{
 \int_{\mathbb R^5}|\widehat{\mathscr W}_{q,k,g}(\boldsymbol\xi)|
 \,d\boldsymbol\xi
 \ll
 \sum_{\epsilon_1,\ldots,\epsilon_5\in\{0,2\}}
 \|\partial_{x_1}^{\epsilon_1}\cdots
   \partial_{x_5}^{\epsilon_5}\mathscr W_{q,k,g}\|_1.}
\tag{4.554}
\]

Thus derivatives of total order at most ten give a summable tensor nuclear
norm, at polylogarithmic cost only.

For one Fourier tensor and one divisor layer, let
(\mathcal E_{q,g,\mathbf d}[U_1,U_2,V_1,V_2,\psi]) denote the right side
of (4.536), with possibly different one-variable weights on its two sides,
the four conditions (4.547), and the one-variable (q)-coprimality and
mollifier supports retained, but with the four endpoint taper sizes
factored out as in (4.443).  The exact local theorem which now suffices is

\[
\boxed{
 \left|\mathcal E_{q,g,\mathbf d}
   [U_1,U_2,V_1,V_2,\psi]\right|
 \ll_W AT\,\omega_g(d_0,d_1,d_2)
 (\log T)^{1+o(1)},}
\tag{DCV\(_\gamma\)}
\]

uniformly in (0\le\gamma<1), the Fourier parameters under the integrable
majorant (4.554), all squarefree divisor layers, and the stated
one-variable coprimality restrictions.  Equations (4.545)--(4.554) show
that DCV\(_\gamma), after restoring the four endpoint tapers, implies the
actual line-family bound (4.504).  The required power saving in one layer
is still exactly (A=T^{1-\gamma}); no extra power is consumed by kernel
separation or coprimality aggregation.

The helpers transition_line_coprimality_layer_identity and
transition_line_coprimality_layer_density verify (4.545)--(4.548) on
exact integers.  The adapter transition_coprimality_layer_audit records
the two Euler factors, the five lifted variables, the order-ten Fourier
majorant, and the zero derivative-power cost.  It sets
lifted_kernel_fourier_nuclear_norm_verified=True,
layer_density_aggregation_verified=True, and
actual_line_family_reduced_to_layered_variance=True.  It keeps
published_layer_variance_proved=False and whole_line_family_covered=False.

### 4.61 Exact Mellin normalization: the residual gate is a mixed Möbius fourth moment

There is no further combinatorial variable hidden in
DCV\(_\gamma\).  Its analytic content can be written exactly as a
Dirichlet-polynomial moment at the original physical height.  Keep one
Fourier tensor and one divisor layer from Section 4.60.  All divisibility
and \(q\)-coprimality restrictions below are the one-variable restrictions
in (4.547) and (4.545).  Put

\[
\begin{aligned}
 P_{A,j}(t)&:=\sum_{a\asymp A}
   \frac{\mu(a)U_j(a/A)}{a^{1/2+it}},\\
 P_{T,j}(t)&:=\sum_{r\asymp T}
   \frac{\mu(r)V_j(r/T)}{r^{1/2+it}},
 \qquad j=1,2,
\end{aligned}
\tag{4.555}
\]

where the smooth weights include the corresponding fixed additive Fourier
twists.  Define the restricted convolution

\[
 c_j(n):=\sum_{ar=n}\mu(a)\mu(r)U_j(a/A)V_j(r/T).
\tag{4.556}
\]

Both sums in (4.555) are finite, so finite Dirichlet multiplication gives,
with no convergence qualification,

\[
 \boxed{P_{A,j}(t)P_{T,j}(t)
 =\sum_n\frac{c_j(n)}{n^{1/2+it}}.}
\tag{4.557}
\]

Set \(X=AT=T^{2-\gamma}\).  Use the Fourier convention

\[
 \widehat\Omega(\xi)
 :=\int_{\mathbb R}\Omega(u)e(-u\xi)\,du,
 \qquad e(x)=e^{2\pi ix}.
\tag{4.558}
\]

Expanding the finite products and substituting \(t=Tu\) yields the exact
identity

\[
\boxed{
\begin{aligned}
 &\int_{\mathbb R}P_{A,1}(t)P_{T,1}(t)
  \overline{P_{A,2}(t)P_{T,2}(t)}\,\Omega(t/T)\,dt\\
 &\quad=T\sum_{m,n}\frac{c_1(n)\overline{c_2(m)}}{\sqrt{mn}}
 \widehat\Omega\!\left(\frac{T}{2\pi}\log\frac nm\right)\\
 &\quad=\frac1A\sum_{m,n}c_1(n)\overline{c_2(m)}
 \left(\frac{mn}{X^2}\right)^{-1/2}
 \widehat\Omega\!\left(\frac{T}{2\pi}\log\frac nm\right).
\end{aligned}}
\tag{4.559}
\]

The last equality uses only \(X=AT\).  It is the normalization which is
lost if the coefficient autocorrelation and the spectral moment are
compared by exponent alone.  There is no compact-support assertion for
the transformed kernel.  For every \(B\ge0\), integration by parts gives

\[
 \left|\widehat\Omega\!\left(
   \frac{T}{2\pi}\log\frac nm\right)\right|
 \le C_{B,\Omega}
 \left(1+T\left|\log\frac nm\right|\right)^{-B}.
\tag{4.559a}
\]

On \(m,n\asymp X\), the range
\(T|\log(n/m)|\asymp1\) has additive determinant scale
\(|n-m|\asymp X/T=A\); the exact half-open determinant shell remains the
one already imposed in (4.499).

The remaining centre and determinant dependence also separates exactly,
but the scaled coordinates are essential.  If \(J_T(x,y)\) is one
two-variable kernel after the lift, write

\[
 u=\log x,\qquad v=\log y,\qquad
 z=\frac{u+v}{2},\qquad w=T(u-v),
\]

and put
\(F_T(z,w)=J_T(e^{z+w/(2T)},e^{z-w/(2T)})\).  The lifted estimates give
uniform \(L^1\) bounds for fixed derivatives in \((z,w)\), not for an
unscaled transverse derivative in \((u,v)\).  Fourier inversion in
\((z,w)\) gives

\[
 \boxed{J_T(x,y)=\frac1{(2\pi)^2}
  \int_{\mathbb R^2}\mathcal J_T(\xi,\tau)
  x^{i(\xi/2+T\tau)}y^{i(\xi/2-T\tau)}
  \,d\xi\,d\tau,}
\tag{4.560}
\]

where \(\mathcal J_T\) has a uniform Schwartz majorant.  Applying
\((1-\partial_z^2)(1-\partial_w^2)\) proves the integrable majorant without
a power of \(T\).  The two powers in (4.560) are absorbed into the two
one-variable weights in (4.555).  Together with (4.554), this proves that
the actual coupled kernel is an exact signed superposition of the family
(4.559), with only the already recorded polylogarithmic nuclear norm.
Fourier inversion reconstructs the physical kernel, so the representation
is two-sided.  This does **not** mean that an estimate for the original
signed superposition implies the same estimate for each separated member;
that reverse inequality would be false without an additional projection
argument.

Before determinant-shell separation the original time weight is supported
in \([1,2]\).  After multiplying by the smooth determinant cutoff, the
effective spectral weight is a convolution of that compactly supported
weight with a Schwartz function in the scaled variable \(t/T\).  It is
Schwartz-localized at height \(T\), but it need not vanish at \(t=0\).
Accordingly M4\(_\gamma\) below is uniform for precisely this translated
Schwartz family; no false compact exclusion of zero frequency is used.

The coefficient target in DCV\(_\gamma\) is

\[
 AT(\log T)^{1+o(1)}=X(\log T)^{1+o(1)},
\tag{4.561}
\]

By (4.559)--(4.560), the following uniform separated estimate is sufficient
for that target:

\[
\boxed{
 \left|\int_{\mathbb R}P_{A,1}(t)P_{T,1}(t)
  \overline{P_{A,2}(t)P_{T,2}(t)}\,
  \Omega(t/T)\,dt\right|
 \ll_W T(\log T)^{1+o(1)}.}
\tag{M4\(_\gamma\)}
\]

At the top face \(\gamma=0\), \(A=T\).  A symmetric member
\(U_1=U_2=V_1=V_2=U\) of this sufficient family is the concrete fourth
moment

\[
 \boxed{
 \int_{\mathbb R}\left|
  \sum_{n\asymp T}\frac{\mu(n)U(n/T)}{n^{1/2+it}}
 \right|^4\Omega(t/T)\,dt
 \ll_{U,W}T(\log T)^{1+o(1)}.}
\tag{4.562}
\]

The converse from DCV\(_\gamma\) to every instance of
M4\(_\gamma\) is not asserted.  In particular, determinant-shell
separation convolves the compact physical band with a Schwartz transform,
and an individual separated weight can have a nonzero zero-frequency
component.  Bounding that component alone would reintroduce the Mertens
power gate of Section 4.58, even though cancellations among separated
components remain available in the original kernel.

The normalization nevertheless shows exactly why a generic mean-value
theorem cannot prove the sufficient bound.  Applied to the product polynomial of length
\(X\), Montgomery--Vaughan gives

\[
 \int |P_{A,1}(t)P_{T,1}(t)|^2|\Omega(t/T)|\,dt
 \ll_W (T+X)\sum_{n\asymp X}\frac{|c_1(n)|^2}{n}
 \ll_W X(\log T)^{O(1)}.
\tag{4.563}
\]

The exponent on the right is \(2-\gamma\), whereas the target exponent
in M4\(_\gamma\) is one.  The exact positive-power deficit is therefore

\[
 \boxed{(2-\gamma)-1=1-\gamma=\log_T A.}
\tag{4.564}
\]

The new large-value estimates of Guth--Maynard concern general large
values of Dirichlet polynomials; they do not state the uniform
Möbius-weighted mixed moment M4\(_\gamma\), and inserting their generic
coefficient bounds does not remove (4.564).  Radziwiłł's conditional
connection between long mollifiers and Montgomery pair correlation is a
structural warning that this scale is deep, but it is not used here as a
logical implication: his cited theorem assumes RH and concerns the error
norm \(1-\zeta M\), while (4.562) is the exact local gate extracted above.

The helper transition_mobius_dirichlet_product_identity checks (4.557)
on finite rational fixtures.  The adapter
transition_mobius_dirichlet_fourth_moment_audit records the exact
\(T/X=A^{-1}\) normalization, the exponents in (4.561)--(4.564), and
the fact that the separated transform is only Schwartz-localized and does
not compactly exclude zero.  It records an exact mixed-moment
superposition and a one-way uniform sufficient condition, while setting
dcv_implies_each_separated_moment=False.  It keeps
published_mixed_fourth_moment_proved=False and
whole_line_family_covered=False.  Thus Section 4.61 changes the analytic
language of the obstruction, but does not declare M4\(_\gamma\) proved.

### 4.62 Exact amplitude ledger for the stronger top fourth-moment route

The sufficient componentwise estimate (4.562) can itself be tested against
the strongest generic large-value inputs without confusing it with the
original signed DCV kernel.  Absorb the factor \(x^{-1/2}\) into the smooth
weight and write, exactly,

\[
 P_{T,U}(t)=T^{-1/2}D_U(t),\qquad
 D_U(t):=\sum_{T<n\le2T}\mu(n)\widetilde U(n/T)n^{-it},
 \quad \widetilde U(x)=x^{-1/2}U(x).
\tag{4.565}
\]

Thus (4.562) asks for the unnormalised fourth moment

\[
 \boxed{\int_{\mathbb R}|D_U(t)|^4\Omega(t/T)\,dt
 \ll_{U,W}T^3(\log T)^{1+o(1)}.}
\tag{4.566}
\]

Let \(R_\mu(V;T,U)\) be the maximum cardinality of a one-separated set
\(\mathcal T\) in an interval of length \(O(T)\) on which
\(|D_U(t)|\ge V\).  After removing the harmless phase \(T^{-it}\), the
frequencies of \(D_U\) lie in the fixed interval \([0,\log2]\).  The
Plancherel--Pólya sampling inequality for exponential polynomials,
followed by dyadic layer cake, shows that (4.566) follows from

\[
 \sum_{V\ {\rm dyadic}}R_\mu(V;T,U)V^4
 \ll T^3(\log T)^{1+o(1)}.
\tag{4.567}
\]

For a fixed amplitude \(V=T^\sigma\), \(1/2\le\sigma\le1\), the exact
power required by (4.567) is therefore

\[
 \boxed{R_\mu(T^\sigma;T,U)
 \ll T^{3-4\sigma+o(1)}.}
\tag{MLV\(_\sigma\)}
\]

At \(N=T\), the classical Montgomery--Halász--Huxley large-value bound
has total exponent

\[
 R(V)\ll T^{2+o(1)}V^{-2},
\tag{4.568}
\]

throughout \(\sigma\ge1/2\); its companion minimum is never larger on
this range.  Multiplying by \(V^4\) gives fourth-moment exponent

\[
 \boxed{2+2\sigma,}
\tag{4.569}
\]

and hence the exact deficit

\[
 \boxed{(2+2\sigma)-3=2\sigma-1.}
\tag{4.570}
\]

Guth--Maynard, arXiv:2405.20552v2, Theorem 1.1, gives at \(N=T\)

\[
 R(V)\ll T^{o(1)}
 \left(T^2V^{-2}+T^{18/5}V^{-4}+T^{17/5}V^{-4}\right).
\tag{4.571}
\]

After multiplication by \(V^4\), its three contribution exponents are

\[
 \boxed{2+2\sigma,\qquad\frac{18}{5},\qquad\frac{17}{5}.}
\tag{4.572}
\]

Taking the better of (4.568) and (4.571) leaves (4.569) unchanged.  For
example, at \(\sigma=2/3\) the required count exponent is \(1/3\), the
classical count exponent is \(2/3\), and the best fourth-moment exponent
is \(10/3\), leaving the fixed deficit \(1/3\).  The Guth--Maynard bound
alone has exponent \(18/5\) there and leaves deficit \(3/5\).

Menon's Theorems 1.1 and 1.5 give logarithmic decay for Möbius short
intervals and averaged Chowla correlations.  They contribute exponent zero
to (4.570), not a positive power.  In fact the paper identifies
\(1/\log H\) as the effective limit of the Matomäki--Radziwiłł averaged
shift method, so it cannot fill any interval \(\sigma>1/2\).

There is also a sharp pointwise warning for a nonnegative \(\Omega\) that
is bounded below on a fixed subinterval of \([1,2]\).  When
\(\sigma>3/4\), the
right side of MLV\(_\sigma\) has negative exponent.  The sampling
inequality then forces the large-value set to be empty for all sufficiently
large \(T\), up to the displayed subpower slack.  Thus a uniform proof of
(4.566) entails the pointwise threshold

\[
 \boxed{\sup_{T\le t\le2T}|D_U(t)|
 \le T^{3/4+o(1)}.}
\tag{4.573}
\]

No audited theorem proves (4.573) for Möbius coefficients.  This does not
turn (4.573) into a necessary consequence of the original signed line
family: Section 4.61 already showed that DCV is a signed superposition and
does not imply each separated fourth moment.  The correct routing decision
is therefore to reject generic/componentwise large values as a closure of
DCV, while retaining MLV\(_\sigma\) as the exact theorem needed if that
stronger route is pursued.

The adapter transition_mobius_large_value_audit implements
(4.566)--(4.572) with `Fraction`.  It records the exact deficit
\(2\sigma-1\), the threshold \(3/4\), and Menon's zero positive-power
saving.  It sets mobius_large_value_theorem_proved=False,
original_signed_dcv_requires_componentwise_large_values=False, and
whole_line_family_covered=False.

### 4.63 Exact Möbius--Hecke Euler factor and the reciprocal-\(L\) spectral gate

There is a spectral route which uses more than the arbitrary-coefficient
large sieve, but its arithmetic input must be stated exactly.  Let \(f\)
be an unramified normalized \(GL(2)\) Hecke eigenform and write
\(\lambda_f(p)=\lambda_p\).  For \(\Re s>1\), multiplicativity and the
support of \(\mu\) give

\[
 D_f(s):=\sum_{n\ge1}\frac{\mu(n)\lambda_f(n)}{n^s}
 =\prod_p(1-\lambda_p p^{-s}).
\tag{4.574}
\]

Put \(x=p^{-s}\).  The unramified Hecke \(L\)-factor and the local
zeta factor give the exact formal identity

\[
 1-\lambda_px
 =(1-\lambda_px+x^2)(1-x^2)K_{f,p}(x),
\tag{4.575}
\]

where

\[
 \boxed{K_{f,p}(x)
 =1-\lambda_px^3+(1-\lambda_p^2)x^4+O_f(x^5).}
\tag{4.576}
\]

The vanishing of the coefficients of \(x\) and \(x^2\) is exact, not a
heuristic cancellation.  Coefficient comparison in (4.575) supplies a
finite recurrence for every coefficient of \(K_{f,p}\); the helper
mobius_hecke_local_k_coefficients implements that recurrence over
`Fraction`.

Using the Kim--Sarnak bound
\(|\lambda_f(p)|\le p^{7/64}+p^{-7/64}\), the first two possible local
errors on \(\Re s=1/2\) have prime exponents

\[
 \frac32-\frac7{64}=\frac{89}{64}>1,
 \qquad
 2-\frac{14}{64}=\frac{114}{64}>1.
\tag{4.577}
\]

Thus \(K_f(s)=\prod_pK_{f,p}(p^{-s})\) is absolutely convergent on the
physical half-line (with the usual finite modifications at ramified
primes), and (4.574) has the meromorphic factorization

\[
 \boxed{D_f(s)=\frac{K_f(s)}{\zeta(2s)L(s,f)}.}
\tag{4.578}
\]

The actual coefficient in (4.543) contains two differently twisted
Möbius factors.  Put \(u=p^{-i\tau}\), \(v=p^{-i\upsilon}\), and again
\(x=p^{-s}\).  Its Hecke-twisted local series is exactly

\[
 1-\lambda_p(u+v)x+(\lambda_p^2-1)uvx^2.
\tag{4.578a}
\]

Define \(K_{f,p;u,v}\) by dividing (4.578a) by

\[
\begin{aligned}
 &(1-\lambda_pux+u^2x^2)(1-\lambda_pvx+v^2x^2)\\
 &\qquad\times(1-u^2x^2)(1-v^2x^2)(1-uvx^2).
\end{aligned}
\tag{4.578b}
\]

Direct coefficient comparison gives

\[
 K_{f,p;u,v}(x)
 =1-\lambda_p(u+v)(u^2+v^2)x^3+O_f(x^4),
\tag{4.578c}
\]

so the mixed correction again starts in degree three and is absolutely
convergent on \(\Re s=1/2\).  Therefore the exact unramified Euler
factor for the Mellin component is

\[
\boxed{
 \sum_{n\ge1}\frac{f_{\tau,\upsilon}(n)\lambda_f(n)}{n^s}
 =\frac{K_{f;\tau,\upsilon}(s)}{
 L(s+i\tau,f)L(s+i\upsilon,f)
 \zeta(2s+2i\tau)\zeta(2s+2i\upsilon)
 \zeta(2s+i\tau+i\upsilon)}.}
\tag{4.578d}
\]

Hence the actual spectral candidate needs a two-factor reciprocal-
\(L\) negative moment, not merely the single factor in (4.578).

Here "candidate" is conditional on a new geometric-to-spectral adapter.
Section 4.16 proves that in the classical Kuznetsov orbit attached to
the determinant equation, the Hecke index is the shift \(h\) (there
denoted \(\delta\)); the Möbius-weighted matrix entries are not Hecke
indices.  Therefore (4.578d) is the exact Euler series which would occur
if a relative trace formula placed the balanced coefficient in a
spectral Fourier slot.  The standard Kuznetsov formula does not by
itself produce that slot from (4.500).

This identifies the Möbius gain which a Kuznetsov treatment would have
to preserve.  It does not yet prove a bound for the determinant kernel:

1. an exact Kuznetsov expansion of (4.500), including the moving
   \(q,g\), divisor layers, and the coupled five-variable transform, has
   not been derived;
2. on \(\Re s=1/2\), (4.578) requires a truncated spectral negative
   moment of \(L(s,f)\), with the factor \(\zeta(2s)^{-1}\) retained near
   forced central zeros; and
3. the required gain in the critical cell is the numerical
   \(T^{1/2}\) from (4.476), whereas no audited negative-moment theorem
   certifies that half-power for the actual family.

In particular, replacing the two Möbius sequences by arbitrary
coefficients before the spectral expansion discards (4.578), while
formally inserting \(1/L(s,f)\) on the critical line crosses its zeros
and is not a proof.  The adapter
transition_mobius_hecke_reciprocal_l_audit records the exact local
factorizations (4.575) and (4.578a)--(4.578d), their three zeta factors,
the degree-three start of both correction products, and the remaining
half-power gate.  It also records that the classical Hecke index is the
shift and marks the balanced factor as a conditional spectral
diagnostic.  It keeps actual_kuznetsov_reduction_derived=False,
reciprocal_l_negative_moment_proved=False, and
whole_line_family_covered=False.

### 4.64 Primorial conductor obstruction for an exact entry-weighted trace formula

Section 4.63 leaves open the possibility of placing the two Möbius
matrix-entry weights directly in the finite test function of a relative
trace formula.  There is a precise conductor cost for doing this
without first applying Type-I/II decomposition.

Let \(K_p=GL_2(\mathbb Z_p)\).  It acts transitively on the primitive
columns

\[
 \mathcal P_p
 :=\{(x,y)\in\mathbb Z_p^2:\min(v_p(x),v_p(y))=0\}.
\tag{4.579}
\]

On such a column the exact local factor of \(\mu(x)\mu(y)\) is

\[
 w_p(x,y)=
 \begin{cases}
  +1,&v_p(x)=v_p(y)=0,\\
  -1,&\{v_p(x),v_p(y)\}=\{0,1\},\\
  0,&\min(v_p(x),v_p(y))=0,\ \max(v_p(x),v_p(y))\ge2.
 \end{cases}
\tag{4.580}
\]

In particular \((1,1)\) and \((1,p)\) lie in the same \(K_p\)-orbit,
while their weights in (4.580) are \(+1\) and \(-1\).  Therefore no
spherical local vector can encode (4.580).  A locally constant exact
test must have level at least \(p\); for \(p^2\le2T\), distinguishing
the last two rows of (4.580) requires depth at least two and only raises
the conductor further.

Every prime \(p\le T\) divides some integer in \([T,2T]\).  Hence an
exact factorizable finite test for both entries throughout their dyadic
ranges must be nonspherical at every such prime.  If \(Q_T\) is a
common level of the resulting global test, then

\[
 \boxed{Q_T\ge\prod_{p\le T}p.}
\tag{4.581}
\]

Writing \(\vartheta(T)=\sum_{p\le T}\log p\), the prime number theorem
gives

\[
 \boxed{\log Q_T\ge\vartheta(T)=T+o(T),\qquad
        Q_T\ge\exp((1+o(1))T).}
\tag{4.582}
\]

Thus the exact entry-weighted test does not preserve the polynomial
analytic conductor required by the present exponent ledger.  The
adelic Kuznetsov formula of Knightly--Li permits finite-place test
functions, but its standard Hecke insertion is spherical and puts the
arithmetic weight on the shift index, as already recorded in Section
4.16; it does not remove (4.581).

This does not exclude a hybrid argument which first uses a finite
Möbius identity, encodes only a bounded set of local factors
spectrally, and treats the remaining cofactors by dispersion.  It does
exclude the proposed one-step exact relative-trace adapter at polynomial
conductor.  The adapter
transition_entry_weighted_relative_trace_audit computes the finite
primorial exactly, records the asymptotic scale (4.582), and keeps
polynomial_conductor_preserved=False,
published_entry_weighted_adapter=False, and
whole_line_family_covered=False.

### 4.65 Small-prime spectral truncation cannot force fixed multilinearity

One can keep the finite-place conductor polynomial by encoding only the
local factors at primes \(p\le z\).  For a squarefree integer \(n\), put

\[
 d_z(n):=(n,P(z)),\qquad m_z(n):=n/d_z(n),\qquad
 P(z):=\prod_{p\le z}p.
\tag{4.583}
\]

Then the decomposition

\[
 \boxed{\mu(n)=\mu(d_z(n))\mu(m_z(n)),\quad
 d_z(n)\mid P(z),\quad (m_z(n),P(z))=1}
\tag{4.584}
\]

is exact and unique on the support of \(\mu\).  Choosing
\(z=C\log T\) gives

\[
 P(z)=\exp(\vartheta(C\log T))=T^{C+o(1)},
\tag{4.585}
\]

and the number of allocations \(d_z\mid P(z)\) is
\(2^{\pi(z)}=T^{o(1)}\).  Thus this small-prime part can be retained at
polynomial conductor and subpower combinatorial cost.

The remaining cofactor is only \(z\)-rough.  Its possible number of
prime factors is bounded by

\[
 \Omega(m_z)\le\frac{\log T}{\log z}
 =\frac{\log T}{\log\log T+O_C(1)},
\tag{4.586}
\]

which tends to infinity.  Conversely, to force
\(\Omega(m_z)\le K\) for a fixed integer \(K\), it is necessary and
sufficient at the exponent boundary to take

\[
 \boxed{z>T^{1/(K+1)}.}
\tag{4.587}
\]

The corresponding local level then satisfies

\[
 P(z)=\exp\!\left(T^{1/(K+1)+o(1)}\right),
\tag{4.588}
\]

which is superpolynomial.  At the logarithmic cutoff, the usual rough
density is logarithmic and contributes power-saving exponent zero; it
does not reduce the critical requirement \(1/2\) from (4.476).

For the Bourgain--Garaev count \(K=7\), the boundary in (4.587) is
\(z=T^{1/8}\).  Hence the two desired properties

1. polynomial finite-place level, and
2. a fixed seven-atom rough decomposition,

cannot hold simultaneously in this exact local-test scheme.  The
adapter transition_small_prime_spectral_hybrid_audit records the
boundary \(1/(K+1)\), the zero rough-density power saving, and the
unchanged deficit \(1/2\).  It keeps
published_rough_cofactor_half_power_bound=False and
whole_line_family_covered=False.

### 4.66 An arbitrary Möbius cutoff only redistributes the critical volume

It remains to check that the preceding obstruction is not an artefact of
the particular Vaughan--Heath-Brown cutoff used in Section 4.60.  Write

\[
 \kappa:=\log_T |\Delta|,\qquad
 \gamma:=\log_T g,\qquad
 \alpha:=1-\gamma,
 \qquad U=A^u,\quad V=A^v,
\tag{4.589}
\]

where \(A=T^\alpha\), \(0<u<1\), and \(0\le v\le1-u\).  In either
entry, every dyadic term obtained from the exact Möbius identity has a
factorization

\[
 a_i=d_i e_i y_i,qquad
 \pi_i:=\log_T d_i,\quad
 \varepsilon_i:=\log_T e_i,\quad
 \beta_i:=\log_T y_i,
\tag{4.590}
\]

and hence the exact exponent constraint

\[
 \boxed{\pi_i+\varepsilon_i+\beta_i=\alpha}
 \qquad(i=1,2).
\tag{4.591}
\]

The cutoff conditions merely restrict

\[
 0\le\pi_i\le u\alpha,qquad
 0\le\beta_i<(1-u)\alpha,qquad
 \varepsilon_i=\alpha-\pi_i-\beta_i.
\tag{4.592}
\]

The additional Type-I/II boundary \(V=A^v\) cuts this polytope at
\(v\alpha\); it does not change (4.591).  Even under the optimistic
hypothesis that the signed \(d_i,y_i\) variables supply square-root
cancellation and that the unsigned \(e_i\) variables can be completed
with their full square-root volume saving, the two contributions are

\[
 S_{\rm sign}
   ={\pi_1+\beta_1+\pi_2+\beta_2\over2},
 \qquad
 S_{\rm unsign}
   ={\varepsilon_1+\varepsilon_2\over2}.
\tag{4.593}
\]

Therefore (4.591) gives the cutoff-independent identity

\[
 \boxed{S_{\rm sign}+S_{\rm unsign}=\alpha=1-\gamma.}
\tag{4.594}
\]

The determinant-line estimate requires saving

\[
 S_{\rm req}=\kappa-\gamma,
\tag{4.595}
\]

so the most optimistic power margin allowed by this separate-factor
ledger is exactly

\[
 \boxed{S_{\rm sign}+S_{\rm unsign}-S_{\rm req}=1-\kappa.}
\tag{4.596}
\]

On the unresolved top face \(\kappa=1\), the margin in (4.596) is zero
for every admissible rational pair \((u,v)\) and for every dyadic
factorization satisfying (4.591).  Thus changing \(U\) or \(V\) cannot
create the fixed positive power saving needed to absorb dyadic,
polylogarithmic, and \(q\)-summation losses.  This is not a lower bound
for the original Möbius sum: it is an exact no-slack statement for all
arguments whose savings are the separate square-root volumes in
(4.593).  Any successful continuation must exploit joint cancellation
before those variables are separated (or introduce a genuinely
stronger input).

For the deterministic witness used by the audit, take

\[
 (\kappa,\gamma,u,v)=\left(1,{1\over2},{2\over3},{1\over4}\right),
\quad
 (\pi_1,\beta_1)=\left({1\over3},{1\over7}\right),
\quad
 (\pi_2,\beta_2)=\left({1\over4},{1\over8}\right).
\tag{4.597}
\]

Then

\[
 (\varepsilon_1,\varepsilon_2)=\left({1\over42},{1\over8}\right),
 \quad S_{\rm sign}={143\over336},
 \quad S_{\rm unsign}={25\over336},
 \quad S_{\rm req}={1\over2},
\tag{4.598}
\]

and the margin is exactly zero.  The adapter
transition_general_cutoff_line_gate_audit checks (4.591)--(4.598) with
`Fraction`, records `cutoff_choice_creates_positive_power_slack=False`,
and keeps `cell_closed_by_registered_bounds=False`.

### 4.67 BBLR joint quadratic-divisor theorem and its exact hard-face deficit

The preceding audits treat the two determinant sides separately.  There is
a stronger published comparison point that must be tested before declaring a
new joint estimate necessary: Proposition 3.1 of
[Bettin--Bui--Li--Radziwiłł](https://arxiv.org/html/1609.02539v1)
(BBLR) treats

\[
 a m_1m_2-b n_1n_2=\pm h
\tag{4.599}
\]

with arbitrary divisor-bounded coefficients in the two outer variables and
independent smooth weights in \(h,m_1,m_2,n_1,n_2\).  This is strictly better
matched to the present problem than first applying Cauchy to one side.

Write

\[
 \alpha=1-\gamma,
 \qquad
 P=1+\alpha=2-\gamma.
\tag{4.600}
\]

Here \(T^\gamma\) is the extracted denominator gcd, \(T^\alpha\) is its
cofactor scale, and each side of the determinant equation has total product
scale \(T^P\).  Apply the exact Möbius factorization to both Möbius-bearing
variables on each side.  Convolve every signed atom on side \(i\) into one
outer variable \(u_i\asymp T^{s_i}\); the resulting coefficient
\(\lambda_i(u_i)\) is bounded by a fixed divisor function and hence by
\(u_i^\varepsilon\).  The two remaining unsigned cofactors occupy the two
inner BBLR slots.  Thus the exact dyadic equation has the form

\[
 u_1m_{1,1}m_{1,2}-u_2m_{2,1}m_{2,2}=h,
 \qquad
 s_i+\xi_{i,1}+\xi_{i,2}=P,
\tag{4.601}
\]

where \(u_i\asymp T^{s_i}\),
\(m_{i,j}\asymp T^{\xi_{i,j}}\), \(h\asymp T^\alpha\), and every exponent
in (4.601) is nonnegative.  Dyadic localization supplies precisely the
independent smooth weights allowed in Proposition 3.1; no separation of
\(m_{i,1}m_{i,2}\) into a single product weight is being assumed.

Set

\[
 S=s_1+s_2,
 \qquad
 M_\ast=\max(s_1,s_2).
\tag{4.602}
\]

The exact BBLR parameter substitution is

\[
 A=T^{s_1},\qquad B=T^{s_2},\qquad
 MN=T^{2P-S},\qquad H=T^\alpha,
\tag{4.603}
\]

or, in the symmetric parameter used by the audit,
\(X=(MN)^{1/2}=T^{P-S/2}\).  Both determinant sides have product scale
\(T^P\), so the side-balance hypothesis is automatic.  The sharp form of
BBLR Proposition 3.1 requires

\[
 H\ll(AB)^{1/2+\varepsilon};
 \quad\text{at exponent level this is exactly}\quad S\ge 2\alpha.
\tag{4.604}
\]

After (4.603), the two summands in its sharp error have exact exponents

\[
 E_{\rm AB}=\frac12+\alpha+S,
 \qquad
 E_{\rm Watt}=\frac34+\frac32\alpha+\frac12M_\ast,
\tag{4.605}
\]

up to the displayed \(T^\varepsilon\).  Indeed, the common prefactor
\((ABMNH^2)^{1/4}\) has exponent \(1/2+\alpha\); multiplication by
\(AB\), respectively by
\(H^{1/4}(A+B)^{1/2}(ABMN)^{1/8}\), gives (4.605).

Without (4.604), equation (12) of Proposition 3.1 gives

\[
 E_{\rm gen,1}
 =\frac34+\frac74\alpha+\frac14S+\frac54M_\ast,
 \qquad
 E_{\rm gen,2}=2\alpha.
\tag{4.606}
\]

These follow directly from

\[
 (ABMNH^2)^{3/8}(ABH)^{1/4}(A+B)^{5/4}+H^2.
\tag{4.607}
\]

The local target exponent is not an adjustable normalization: it is the
side-product exponent

\[
 E_{\rm target}=P=1+\alpha.
\tag{4.608}
\]

On the hard face \(\gamma=0\), hence \(\alpha=1\) and \(P=2\).  If
\(S<2\), only (4.606) is available and its first exponent is minimized at
\(S=M_\ast=0\):

\[
 \min E_{\rm gen,1}=\frac52,
 \qquad E_{\rm gen,2}=2,
 \qquad E_{\rm target}=2.
\tag{4.609}
\]

If \(S\ge2\), the sharp estimate is available, but already
\(E_{\rm AB}-E_{\rm target}=S-1/2\ge3/2\).  Therefore optimizing over
every admissible \((s_1,s_2)\) leaves the exact best power margin

\[
 E_{\rm target}-E_{\rm error}=-\frac12.
\tag{4.610}
\]

Thus BBLR misses the hard Möbius face by precisely \(T^{1/2}\), even after
all signed atoms are placed in its two arbitrary-coefficient slots.

The obstruction is genuinely localized.  For example, at

\[
 \gamma=\frac45,\quad \alpha=\frac15,\quad
 s_1=s_2=\frac15,
\tag{4.611}
\]

one has \(P=6/5\), \(S=2/5\), \(M_\ast=1/5\), \(X=T\), and (4.604)
holds.  Equations (4.605) give

\[
 E_{\rm AB}=\frac{11}{10},
 \qquad E_{\rm Watt}=\frac{23}{20},
 \qquad E_{\rm target}=\frac65,
\tag{4.612}
\]

so the error has a positive \(T^{1/20}\) margin in that cell.
Nevertheless Proposition 3.1 also returns a Poisson main term, and BBLR
Theorem 4.1 recombines the relevant orderings into four main terms.  Their
exact sum after the present Möbius decomposition has not been shown to
cancel or to be absorbed by the already registered zero mode.  Hence even
the cell (4.611) is recorded as uncovered.  Conversely, cancelling those
main terms would not fix (4.610): the hard-face error itself is already too
large.

Within the sufficient DCV/square-function route, the remaining power theorem
can now be stated more sharply.  It must be a Möbius-weighted refinement of
the joint BBLR quadratic-divisor estimate which, on \(\gamma=0\), gains at
least \(T^{1/2}\) beyond (4.607), while retaining the recombination needed to
identify its Poisson main term.  This refinement is not asserted to be a
necessary consequence of the original pre-Cauchy sum: cancellation among the
slope family can still avoid the DCV majorant.  A separate-side trilinear
estimate cannot certify the gain inside the DCV route.

### 4.68 The worst BBLR box is an exact unsigned sector, not a scale artefact

The hard-face deficit in (4.610) could still be misleading if it arose only
because Proposition 3.1 suppresses the four individual inner scales.  The
exact Möbius identity and the uncompressed proof of that proposition rule out
this possibility.

For \(n>U\), group the approved finite identity by the product of its two
signed atoms.  Define

\[
 C_U(n;u):=-
 \sum_{\substack{dey=n\\de>U,\ d\le U\\dy=u}}
 \mu(d)\mu(y).
\tag{4.613}
\]

Then finite reindexing gives

\[
 \boxed{\mu(n)=\sum_{u\ge1}C_U(n;u).}
\tag{4.614}
\]

The term \(u=1\) is unique: it forces \(d=y=1\) and \(e=n\).  Therefore

\[
 \boxed{C_U(n;1)=-1,
 \qquad \sum_{u>1}C_U(n;u)=\mu(n)+1.}
\tag{4.615}
\]

Apply (4.614) to the four Möbius-bearing entries of the balanced
quadratic-divisor box.  If those entries are \(n_1,\ldots,n_4\), then

\[
 \prod_{i=1}^4\mu(n_i)
 =\sum_{u_1,\ldots,u_4\ge1}
   \prod_{i=1}^4 C_U(n_i;u_i),
\tag{4.616}
\]

whereas the all-unsigned cell is exactly

\[
 \boxed{\prod_{i=1}^4C_U(n_i;1)=(-1)^4=1.}
\tag{4.617}
\]

Thus the BBLR cell \(s_1=s_2=0\) really has a positive unweighted outer
coefficient.  None of the original four Möbius signs survives inside that
cell.  They are restored only by summing it together with every nontrivial
outer-product scale in (4.616).  A triangle inequality between those scales
irreversibly removes the relevant cancellation.

It remains to test the scale-dependent estimate before BBLR compress it to
(4.607).  In the all-unsigned hard cell the original variable ranges force

\[
 A=B=1,\qquad
 M_1=M_2=N_1=N_2=T,\qquad H=T.
\tag{4.618}
\]

This is balanced, not an extreme unbalanced allocation.  On the Poisson gcd
layer \(d\asymp T^\eta\), equation (15) of BBLR Lemma 3.1 gives

\[
 Z_{\pm,d}(x)\ll T^{5/2-(7/2)\eta+\varepsilon}.
\tag{4.619}
\]

The \(x\)-interval in their equation (14) has exponent \(\eta\), and a
dyadic \(d\)-layer contains \(T^{\eta+o(1)}\) integers.  Hence its complete
contribution has exponent

\[
 \boxed{E_d=\frac52-\frac32\eta.}
\tag{4.620}
\]

The maximum occurs at \(d\asymp1\):

\[
 \max_{0\le\eta\le1}E_d=\frac52.
\tag{4.621}
\]

The separate approximation error in equation (14) is \(H^2T^\varepsilon\),
of exponent two, so it does not change (4.621).  The uncompressed proof
therefore reproduces exactly the half-power deficit in (4.610); no hidden
choice of \(M_i,N_i\) improves it.

The finite helpers `mobius_unsigned_sector_recombination` and
`four_mobius_unsigned_sector_recombination` verify (4.613)--(4.617) on
integer fixtures.  The adapter
`transition_bblr_hard_unsigned_cell_audit` records (4.618)--(4.621) with
`Fraction`.  This is a no-go result only for cellwise use of BBLR.  It is
not a lower bound for the original signed sum.  The two remaining logical
options are now disjoint:

1. prove a BBLR-strength joint estimate after summing all outer scales in
   (4.616), before any triangle inequality; or
2. return to the pre-Cauchy slope family (4.457), where cancellation among
   slopes need not pass through the positive DCV square function.

### 4.69 The actual delta-lattice zero mode is a Gram form

Section 4.58 left open whether the coupled kernel might annihilate the
constant microarc before any Möbius estimate is used.  The exact Jacobian in
the two-dimensional Poisson formula decides this for the square-function
route.

For an entry row \(E_i=(w_i,-s_i)\), let \(K_i(v,j)\) denote the exact
continuous pullback of its transformed kernel, so that its shift coordinate
is

\[
 \delta_i=w_iv-s_ij.
\tag{4.622}
\]

For an off-diagonal pair, put

\[
 B=\begin{pmatrix}w_1&-s_1\\w_2&-s_2\end{pmatrix},
 \qquad |\det B|=|r_1s_2-r_2s_1|=|\Delta|.
\tag{4.623}
\]

The exact function used in (4.488) is characterized by
\(F_B(Bz)=K_1(z)\overline{K_2(z)}\), with \(z=(v,j)^t\).  Therefore the
ordinary change of variables \(y=Bz\) gives

\[
 \boxed{
 \frac1{|\Delta|}\widehat F_B(0)
 =\int_{\mathbb R^2}K_1(v,j)\overline{K_2(v,j)}\,dv\,dj.}
\tag{4.624}
\]

The factor \(|\Delta|^{-1}\) from Poisson summation is cancelled exactly by
the Jacobian \(|\det B|\).  It is not a residual small density which can
force the zero mode to vanish.

More generally, restore the identity diagonal and let \(c_E\) be any finite
entry coefficient, including the original Möbius and endpoint factors.
Summing (4.624) over the entry pair gives the exact Gram identity

\[
 \boxed{
 \sum_{E_1,E_2}c_{E_1}\overline{c_{E_2}}
 \int K_{E_1}(z)\overline{K_{E_2}(z)}\,dz
 =\int_{\mathbb R^2}\left|
   \sum_Ec_EK_E(z)\right|^2dz\ge0.}
\tag{4.625}
\]

The \(\Delta\ne0\) contribution is (4.625) minus the already registered
identity diagonal.  Hence the actual zero mode is not structurally killed by
the coupled kernel.  Proving it small means proving cancellation in the
Möbius-weighted vector inside the Gram norm; it cannot be replaced by the
formal statement \(\widehat F_B(0)=0\).  The zero of \(G_t\) at \(z=1/2\)
used in Section 4.2 removes a different Mellin boundary term and does not
annihilate (4.625).

The adapter `transition_delta_lattice_poisson_audit` now records the exact
covolume/Jacobian cancellation, positivity of the full Gram form, and the
off-diagonal subtraction.  This closes the first alternative stated at the
end of Section 4.58 in the negative for the DCV route.  It still does not make
DCV necessary: the original pre-Cauchy sum (4.457) can exploit cancellation
among slopes before the positive Gram form is created.

### 4.70 Banks--Shparlinski does not supply the missing slope power

The natural published comparison for the pre-Cauchy alternative is
[Banks--Shparlinski, Theorems 2.1 and
2.4](https://arxiv.org/abs/2506.08787).  On the hard transition box, the
integer relation before Cauchy is

\[
 rv-(kv+j)s=\delta,
 \qquad r,s\asymp T,qquad
 v,j,\delta\asymp T^{1/2}.
\tag{4.626}
\]

For fixed \((v,j)\), the maps

\[
 f(r)=rv,qquad g(s)=-(kv+j)s,qquad \wp(\delta)=-\delta
\tag{4.627}
\]

are injective on the relevant intervals.  Theorem 2.1 bounds its ternary
sum

\[
 \mathsf S_\mu({\bf D};M)
 =\sum_{f(n_1)+g(n_2)+\wp(n_3)=M}
   u_{n_1}v_{n_2}\mu(n_1n_2n_3)
 \ll_{C,\varepsilon,\deg\wp}
 (A+B)N(\log N)^{-C}.
\tag{4.628}
\]

There are two exact mismatches which must not be hidden in an adapter.
First, both bilinear slopes in (4.626) must be fixed before (4.627) becomes
a pair of one-variable injective functions.  Thus the theorem does not sum
the \(T^{1/2}\)-long \(v\)- and \(j\)-families.  Second, the theorem carries
\(\mu(n_1n_2n_3)\), whereas the shift \(\delta\) in the actual sum carries
no Möbius weight.  Splitting \(\delta\) into squarefree and squarefull
divisor layers can manufacture a ternary Möbius-weighted component, but it
is only an exact structural decomposition: it neither saves a power nor
verifies the remaining coupled kernel and coprimality hypotheses.  The
coverage adapter therefore records `all_actual_kernel_hypotheses_verified`
as false.

Even granting the most favorable role assignment, the three interval
lengths are \(T,T,T^{1/2}\), and (4.628) gives a fixed-slope exponent
\(3/2\).  Direct geometric counting in (4.626) is already better: for each
\(r\), the admissible \(s\)-interval has bounded length, so its exponent is
one.  Restoring the two slope variables and the \(h\)-Poisson factor gives
the exact ledger

\[
 \underbrace{1}_{\text{fixed-slope count}}
 +\underbrace{(1/2+1/2)}_{(v,j)}
 +\underbrace{1/2}_{h\text{-Poisson}}
 =\frac52,qquad
 E_{\rm target}=2,qquad
 E_{\rm target}-E_{\rm BS}=-\frac12.
\tag{4.629}
\]

The short-interval variant does not change this conclusion.  Theorem 2.4
requires \(H\ge N^{5/8+\varepsilon}\); the short variable in (4.626) has
exponent \(1/2\), and hence

\[
 \frac12-\frac58=-\frac18.
\tag{4.630}
\]

Consequently the published multiple-Möbius theorem is a useful structural
comparison but does not close the pre-Cauchy sum.  The missing estimate must
save a fixed half power while summing the bilinear slope family jointly, or
must exploit the original two-entry Möbius weights before the Gram norm is
formed.

### 4.71 A Ramaré medium-prime split does not force multilinearity

Another way to preserve Möbius structure is to expose one prime divisor
before applying a multilinear Kloosterman estimate.  Put

\[
 A=T^\alpha,\qquad
 \mathcal P_{\lambda,\nu}(A)
 :=\{p\text{ prime}:A^\lambda<p\le2A^\nu\},
 \qquad0<\lambda\le\nu\le1,
\tag{4.631}
\]

and let

\[
 \omega_{\lambda,\nu}(n)
 :=\sum_{\substack{p\mid n\\p\in\mathcal P_{\lambda,\nu}(A)}}1.
\tag{4.632}
\]

On the squarefree support of \(\mu\), whenever
\(\omega_{\lambda,\nu}(n)>0\), the exact Ramaré identity is

\[
 \boxed{
 \mu(n)=-\frac1{\omega_{\lambda,\nu}(n)}
  \sum_{\substack{p\mid n\\p\in\mathcal P_{\lambda,\nu}(A)}}
  \mu(n/p).}
\tag{4.633}
\]

Indeed every summand on the right of (4.633) is \(-\mu(n)\).  The
normalizing denominator must be retained; the formula says nothing on the
sector \(\omega_{\lambda,\nu}(n)=0\).

There is an exact obstruction at both possible upper endpoints.  If
\(\nu<1\), then for all sufficiently large \(A\), every prime
\(A<p\le2A\) lies outside the band.  The prime number theorem gives

\[
 \#\{p:A<p\le2A\}
 =(1+o(1))\frac A{\log A}=T^{\alpha+o(1)}.
\tag{4.634}
\]

Thus the exceptional sector has the full exponent \(\alpha\); it gains
one logarithm of density and no positive power.  On the determinant-line
gate (4.500), \(\alpha=1-\gamma\) is exactly the total saving required in
(4.502), so this density estimate cannot replace that saving.

If instead \(\nu=1\), the dyadic prime sector is included, but for
\(n=p\asymp A\), (4.633) is only

\[
 \boxed{\mu(p)=-\mu(1),\qquad p=p\cdot1.}
\tag{4.635}
\]

The extracted factor has exponent \(\alpha\), its cofactor has exponent
zero, and only one factor has positive length.  Consequently a full-band
Ramaré split still cannot force the two or more positive-length variables
required by a fixed multilinear theorem.  This is not a lower bound for the
original signed sum: cancellation in the remaining moving
\(\mu(r_1)\mu(r_2)\) weights could still succeed.  It rules out only the
proposed automatic reduction of every denominator Möbius weight to a
multilinear box.

The finite helper `transition_ramare_squarefree_identity` checks (4.633)
without floating point.  The adapter
`transition_ramare_medium_prime_audit` records the proper-band prime
exception, its zero power-density saving, and the one-positive-factor
full-band endpoint.  It keeps
`forces_two_positive_length_factors=False` and
`ramare_decomposition_closes_line_gate=False`.

### 4.72 Prime-weighted Kloosterman bounds still miss the critical saving

The prime sector left by Section 4.71 has stronger published estimates than
an arbitrary coefficient sequence, so it must be checked separately.  For a
fixed prime modulus \(q\), Dunn--Zaharescu quote the unrestricted-prime bound

\[
 \sum_{p\le X}\mathrm{Kl}_2(p;q)
 \ll_\varepsilon q^{1/6+\varepsilon}X^{7/9},
 \qquad1\le X\le q,
\tag{4.636}
\]

and prove, for \((u,v)=1\) and \(v\le q^{1/100}\),

\[
 \sum_{\substack{p\le X\\p\equiv u\pmod v}}
 \mathrm{Kl}_2(p;q)
 \ll_\varepsilon q^{11/192+\varepsilon}X^{15/16}.
\tag{4.637}
\]

These are Theorems 1.1 and 1.2 of
[Dunn--Zaharescu](https://arxiv.org/abs/1801.05880).  Give the theorems
their most favorable possible insertion by taking \(X=q=T\).  Equations
(4.636)--(4.637) then have exponents

\[
 \frac16+\frac79=\frac{17}{18},
 \qquad
 \frac{11}{192}+\frac{15}{16}=\frac{191}{192},
\tag{4.638}
\]

and save respectively \(T^{1/18}\) and \(T^{1/192}\) over the trivial
prime-interval exponent one.  Even the counterfactual grant of four
independent applications gives only

\[
 4\cdot\frac1{18}=\frac29,
 \qquad
 4\cdot\frac1{192}=\frac1{48}.
\tag{4.639}
\]

Against the critical half-power requirement in (4.476), the remaining
deficits are therefore

\[
 \boxed{\frac12-\frac29=\frac5{18},
 \qquad
 \frac12-\frac1{48}=\frac{23}{48}.}
\tag{4.640}
\]

This comparison is deliberately optimistic.  The theorems have one fixed
prime modulus and one standard Kloosterman argument.  In the actual entry
gate the determinant modulus moves through composite values, the recovered
kernel has not been converted to \(\mathrm{Kl}_2(p;q)\), and the other three
entry weights do not separate.  Hence neither theorem is a direct adapter;
the positive deficits in (4.640) already reject the route before those
additional hypothesis failures are charged.

The adapter `transition_prime_kloosterman_audit` records (4.638)--(4.640),
including the progression-modulus cap \(1/100\), and keeps
`standard_single_kloosterman_argument_verified=False`,
`other_entry_weights_separate=False`, and
`published_theorem_closes_prime_sector=False`.

### 4.73 Exact exchange symmetry does not square the centered collar

There is an exact symmetry which is invisible if the two orientations are
estimated separately.  In the notation of (4.4) of the exact-reduction
note, exchange

\[
 (d,e,m_1,m_2,\delta,h)
 \longmapsto(e,d,m_2,m_1,-\delta,-h).
\tag{4.641}
\]

The swapped Poisson variable is
\(y=(xr+\delta)/s\).  Since \(dy=(r/s)dx\), and since \(W\) and
\(V_t\) are real, direct substitution gives the exact kernel identity

\[
 \boxed{
 \mathscr K_{S,R,M,K}(s,r;-\delta,-h)
 =\frac rs e\!\left(\frac{h\delta}{rs}\right)
  \overline{\mathscr K_{R,S,K,M}(r,s;\delta,h)}.}
\tag{4.642}
\]

Here the order of \(K,M\) is also exchanged.  The reality of \(V_t\)
follows directly from
\(\overline{G_t(\bar z)g_t(\bar z)}=G_t(z)g_t(z)\) in its Mellin
definition.  For \((r,s)=1\), additive reciprocity says

\[
 \frac{\bar r}{s}+\frac{\bar s}{r}
 \equiv\frac1{rs}\pmod1.
\tag{4.643}
\]

Consequently the swapped arithmetic phase and the correction in (4.642)
satisfy

\[
 e\!\left(-\frac{h\delta\bar s}{r}\right)
 e\!\left(\frac{h\delta}{rs}\right)
 =e\!\left(\frac{h\delta\bar r}{s}\right).
\tag{4.644}
\]

The Jacobian in (4.642) also changes the swapped outside factor exactly:

\[
 \frac1{\sqrt{rs}\,r}\frac rs
 =\frac1{\sqrt{rs}\,s}.
\tag{4.645}
\]

Thus (4.642)--(4.645) prove that the *full* swapped Poisson summand is
the complex conjugate of the original summand.  They do not say that the
one-sided completed coefficient \(\Lambda_{r,s}(a)\) in (15.11) is
real: the swap changes the modulus from \(s\) to \(r\), and the kernel
contains both the \(t\)-phase and the Fourier phase.

This distinction decides whether the first-order collar bound can be
squared.  For an arbitrary completed coefficient \(A=a+ib\), put
\(u=2\pi x\).  Pairing only by conjugation gives the exact identity

\[
\begin{aligned}
 &A(e(x)-1)+\overline A(e(-x)-1)\\
 &\qquad=2a(\cos u-1)-2b\sin u.
\end{aligned}
\tag{4.646}
\]

Its derivative at \(x=0\) is \(-4\pi b\).  Hence, if \(b\ne0\), no
bound of the form

\[
 |A(e(x)-1)+\overline A(e(-x)-1)|
 \le C_A x^2
\tag{4.647}
\]

can hold on a neighbourhood of zero.  The hoped-for quadratic estimate
would require the extra statement

\[
 \boxed{\Im\Lambda_{r,s}(a)=0}
\tag{4.648}
\]

after a common-modulus identification.  Neither (4.642) nor finite
Fourier inversion supplies (4.648).  Splitting the reciprocity correction
symmetrically as a midpoint phase changes the gauge but not the
\(-2b\sin u\) term in (4.646).

Therefore exchange symmetry proves the exact global reality of the
off-diagonal but does **not** unconditionally improve the first-order
near-resonance estimate to a second-order one.  The helpers
`poisson_exchange_reciprocity_identity` and
`centered_conjugate_pair_taylor_coefficients` check (4.643)--(4.646) with
exact rationals; `poisson_exchange_second_order_audit` keeps
`second_order_collar_unconditional=False`.  This rejects only the
quadratic-collar inference.  It does not rule out using the same exchange
identity inside a future nonsplit spectral argument.

### 4.74 Common-modulus completion recovers two disjoint sublattices

One possible repair of the mismatch in Section 4.73 is to lift both
Poisson orientations to the common modulus

\[
 Q=rs,qquad A=r\bar r_s,qquad (r,s)=1,
\tag{4.649}
\]

where \(\bar r_s\) is the inverse of \(r\pmod s\).  The original
fraction phase is then \(e(-Ah\delta/Q)\).  Its two-dimensional finite
Gauss kernel is

\[
 G_Q(c,v;A)
 :=\sum_{x,y\bmod Q}
 e\!\left(\frac{cx+vy-Axy}{Q}\right).
\tag{4.650}
\]

This kernel is degenerate because \((A,Q)=r\).  Summing first over
\(x\) forces

\[
 c\equiv Ay\pmod Q.
\tag{4.651}
\]

Equation (4.651) is soluble exactly when \(r\mid c\).  If
\(c=rc_0\), then \(\bar r_s y\equiv c_0\pmod s\), so

\[
 y\equiv rc_0\pmod s,
\tag{4.652}
\]

with exactly \(r\) lifts modulo \(Q\).  Summing the remaining character
over those lifts gives zero unless \(r\mid v\).  Writing \(v=rv_0\)
in the nonzero case yields the exact identity

\[
 \boxed{
 G_Q(c,v;A)
 =Qr\,\mathbf1_{r\mid c}\mathbf1_{r\mid v}
 e\!\left(\frac{r c_0v_0}{s}\right).}
\tag{4.653}
\]

Thus the common-modulus lift does not create a new nondegenerate
completion.  It embeds the original modulus-\(s\) completion in the
frequency sublattice

\[
 (c,v)\in(r\mathbb Z/Q\mathbb Z)^2.
\tag{4.654}
\]

After exchanging \(r\) and \(s\), the conjugate orientation is supported
instead on \((s\mathbb Z/Q\mathbb Z)^2\).  Coprimality gives

\[
 (r\mathbb Z/Q\mathbb Z)^2
 \cap(s\mathbb Z/Q\mathbb Z)^2
 =\{(0,0)\}.
\tag{4.655}
\]

The sole common frequency does not help: the centered multiplier at
\((0,0)\) is \(e(0)-1=0\).  Hence no nonzero completed coefficient is
placed at the same common-modulus frequency as its conjugate.

The conductor ledger says the same thing.  In the balanced hard box,

\[
 Q=T^6,qquad Q/H=Q/L=T^{7/2}.
\tag{4.656}
\]

The divisibility in (4.653) removes \(r=T^3\) from each dual variable,
leaving \(T^{1/2}\) and \(T^{1/2}\), exactly the original dual scales.
There is neither a conductor gain nor a new reality constraint.

The helper `common_modulus_degenerate_gauss_identity` checks the solution
orbit in (4.651)--(4.653) by integer congruences and finite-character
orthogonality.  The adapter `common_modulus_exchange_audit` records the
raw and reduced exponents and keeps
`common_modulus_forces_real_completed_coefficient=False` and
`second_order_collar_unconditional=False`.  Thus a common-modulus lift
with the original, ungauged modulus \(Q=rs\) does not rescue the
quadratic-collar route.  This conclusion does not apply to the distinct
midpoint gauge and doubled modulus in Section 4.75.

### 4.75 Midpoint gauge gives a nondegenerate Hermitian completion

Normalize the physical kernel in (4.642) by

\[
 B_{r,s}(\delta,h):=s^{-1}\mathscr K_{R,S,K,M}
 (r,s;\delta,h).
\]

Then (4.642) is exactly

\[
 B_{s,r}(-\delta,-h)
 =e\!\left(\frac{h\delta}{rs}\right)
  \overline{B_{r,s}(\delta,h)}.
\tag{4.657}
\]

Put

\[
 \widetilde B_{r,s}(\delta,h)
 :=e\!\left(-\frac{h\delta}{2rs}\right)B_{r,s}(\delta,h).
\]

The correction in (4.657) is now divided equally between the two
orientations, and direct conjugation gives the same-gauge identity

\[
 \boxed{
 \widetilde B_{s,r}(-\delta,-h)
 =\overline{\widetilde B_{r,s}(\delta,h)}.}
\tag{4.658}
\]

Moving the half correction from the kernel into the original arithmetic
phase replaces (4.649) by

\[
 Q:=2rs,
 \qquad
 A_{r,s}:=2r\bar r_s-1,
 \qquad
 e\!\left(-\frac{A_{r,s}h\delta}{Q}\right).
\tag{4.659}
\]

This coefficient is no longer degenerate.  Modulo \(r\), modulo \(s\),
and modulo \(2\), respectively, it is \(-1,1,1\); hence

\[
 (A_{r,s},Q)=1,
 \qquad
 A_{r,s}^{\,2}\equiv1\pmod Q.
\tag{4.660}
\]

For \(r,s>1\), set \(U=r\bar r_s\) and \(V=s\bar s_r\), using the least
positive inverses.  The integer \(U+V\) is congruent to one modulo both
\(r\) and \(s\), lies strictly between one and \(2rs\), and therefore
\(U+V=1+rs\).  It follows that

\[
 \boxed{A_{s,r}\equiv-A_{r,s}\pmod{2rs}.}
\tag{4.661}
\]

Consequently the doubled-modulus Gauss kernel is exactly nondegenerate.
Summing first over \(x\pmod Q\) forces the unique congruence
\(y\equiv A_{r,s}c\pmod Q\), since \(A_{r,s}^{-1}=A_{r,s}\), and gives

\[
 \boxed{
 \sum_{x,y\bmod Q}
 e\!\left(\frac{cx+vy-A_{r,s}xy}{Q}\right)
 =Qe\!\left(\frac{A_{r,s}cv}{Q}\right).}
\tag{4.662}
\]

By (4.661), the exchanged orientation has the complex-conjugate phase
at the *same* frequency pair \((c,v)\pmod Q\).  To fix the normalization,
let \(\widetilde\Phi_{r,s}(h,\delta)\) be the midpoint-gauged physical
smooth amplitude and put

\[
 \widetilde F_{r,s}(x,y)
 :=\sum_{\substack{h\equiv x\ (Q)\\\delta\equiv y\ (Q)}}
 \widetilde\Phi_{r,s}(h,\delta),
 \qquad
 \widetilde\Theta_{r,s}(c,v)
 :=\frac1{HL}\sum_{x,y\bmod Q}\widetilde F_{r,s}(x,y)
 e\!\left(-\frac{cx+vy}{Q}\right).
\tag{4.662a}
\]

These are finite sums.  Fourier inversion and (4.662) give the exact
centered completed operator

\[
 \mathfrak H_q[\Psi]
 :=\sum_{\substack{r\asymp T^3,\ s\asymp T^3\\
                    (r,s)=1,\ (q,rs)=1\\qr,qs\le N}}
 \mu(r)\mu(s)p_N(qr)p_N(qs)
 \frac{RS}{rs}
 \sum_{c,v\bmod Q}
 \widetilde\Theta_{r,s}(c,v)
 \left\{e\!\left(\frac{A_{r,s}cv}{2rs}\right)-1\right\}.
\tag{4.663}
\]

With this definition there is no dyadic replacement in the prefactor:

\[
 \boxed{
 \mathfrak S_q[\Psi]
 =\frac{HL}{2RS}\mathfrak H_q[\Psi].}
\tag{4.663a}
\]

Here \(q\le N/\max(R,S)\), and the displayed balanced hard box has
\(R=S=T^3\), hence \(q=1\); in general the same formula is read inside
each fixed \(q,R,S,H,L\) dyadic box.  The physical variables have
\(h\asymp H=T^{5/2}\) and \(|\delta|\asymp L=T^{5/2}\), while finite
completion modulo \(Q=2rs\asymp T^6\) and repeated finite summation by
parts give, for least absolute representatives and every fixed \(A>0\),

\[
 |\widetilde\Theta_{r,s}(c,v)|
 \ll_{A,W}
 \left(1+\frac{H|c|_Q}{Q}\right)^{-A}
 \left(1+\frac{L|v|_Q}{Q}\right)^{-A}.
\tag{4.664}
\]

Thus the effective windows are
\(|c|_Q\ll(Q/H)(\log T)^C\) and
\(|v|_Q\ll(Q/L)(\log T)^C\), with transform tails kept separately in
the logarithmic ledger; (4.663) itself remains an exact finite sum.

The multiplier in (4.663) vanishes identically on the row \(c=0\) and
the column \(v=0\).  This is exact centering, not a bound.  It does not,
however, make the modular phase small away from those axes.

The exponent ledger is critical rather than contradictory.  The ambient
cardinality of \((r,s,c,v)\) is

\[
 T^{3+3+7/2+7/2}=T^{13},
 \qquad
 \frac{HL}{Q}=T^{-1}.
\]

Thus (4.663a) makes the local target \(|\mathfrak S_q[\Psi]|\ll
T^6(\log T)^{-B}\) equivalent, after this completion, to the single
Hermitian gate

\[
 \boxed{
 |\mathfrak H_q[\Psi]|
 \ll_{B,W}T^7(\log T)^{-B}.}
\tag{4.665}
\]

Square root of the ambient cardinality is \(T^{13/2}\), so (4.665)
allows exactly \(T^{1/2}\) beyond square root.  The doubled conductor is
offset by the prefactor \(HL/Q=T^{-1}\); there is no positive-power
contradiction.  Conversely, (4.660)--(4.662) alone do not prove (4.665):
the phase is a moving composite-modulus involution phase, both long
variables carry Möbius weights, and the coefficient is joint in all four
variables.  No published theorem adapter has yet been verified for this
operator.  Accordingly the deterministic audit records
`midpoint_hermitian_published_bound=False`.  Section 4.75 supplies a new
exact alternative local gate, not an unconditional proof of it.

The helper `midpoint_common_modulus_involution_identity` verifies
(4.660)--(4.662) by finite integer arithmetic.  The adapter
`midpoint_hermitian_completion_audit` records the exponents \(6,7/2,13,
-1,7,13/2\) and the remaining half-power allowance exactly.

### 4.76 Exact Salié-phase match does not satisfy the published adapter

The phase in (4.663) has an exact relation to the Hermitian
Kloosterman-fraction sum studied by Dong--Robles--Zeindler.  The identity
\(r\bar r_s+s\bar s_r=1+rs\) from Section 4.75 gives

\[
 \boxed{
 \frac{A_{r,s}cv}{2rs}
 \equiv
 \frac{cv}{2}\left(\frac{\bar r_s}{s}
                    -\frac{\bar s_r}{r}\right)
 +\frac{cv}{2}\pmod1.}
\tag{4.666}
\]

Thus \(e(A_{r,s}cv/(2rs))\) is their antisymmetric Hermitian phase with
numerator \(a=cv\) and denominator parameter \(b=2\), multiplied by
\((-1)^{cv}\).  The parity factor depends only on the dual frequencies
and may be absorbed into \(\widetilde\Theta\).  This is an exact phase
match, but not a theorem-hypothesis match.

Indeed, Theorems 1.4 and 1.8 claimed in version 1 of
[arXiv:2601.00292](https://arxiv.org/abs/2601.00292) concern a *fixed*
integer \(a\) and coefficients of the separated form \(\alpha_r\beta_s\).
The midpoint operator instead has

\[
 |a|=|cv|\ll T^7(\log T)^{2C},
 \qquad
 \widetilde\Theta_{r,s}(c,v)
 \text{ joint in }(r,s,c,v),
\tag{4.667}
\]

and requires cancellation after summing the entire \(c,v\) family.
Even if both failures are ignored and the withdrawn displayed estimate
is inserted one frequency pair at a time, it gives no saving at the
outer dual corner.  With \(M=N=T^3\), bounded \(r,s\) coefficients and
\(a=T^7\), the two \(L^2\) norms contribute \(T^3\), while the remaining
factors in the claimed Theorem 1.4 contribute

\[
 T^{7/4}T^{1/2}T^1T^{-1/4}=T^3.
\]

The resulting \(T^6\) is exactly the trivial \(r,s\) size.  In the
smaller region \(a\le T^6\), the same formal substitution gives
\(T^{23/4}\), a saving only of \(T^{1/4}\) in the inner two variables and
no estimate for the outer \(c,v\) average.

There is also a non-negotiable proof-status issue.  The authors' version
2 comment states that equation (2.53) omitted an \(L^2\) factor, changing

\[
 L^5\longrightarrow L^7,
\tag{4.668}
\]

so the argument no longer yields the advertised improved bound.  The
paper's Hermitian claim is therefore not an unconditional input.  The
newer fixed-modulus bilinear Kloosterman-sum theorems of Pascadi,
Milićević--Qin--Wu, and Blomer--Pascadi have a different kernel: a fixed
modulus and a bilinear average of classical Kloosterman sums.  Formula
(4.663) instead has the moving composite modulus \(2rs\), an individual
involution phase, and four jointly weighted variables.  No direct
adapter follows from those statements.

The helper `midpoint_salie_phase_identity` checks (4.666), including the
otherwise easy-to-miss parity term, with exact rationals.  The adapter
`midpoint_published_hermitian_adapter_audit` records the formal inner
exponents \(6\) and \(23/4\), all three hypothesis failures, and keeps
`withdrawn_claim_closes_midpoint_gate=False`.  Therefore the correct next
problem is not to cite a Hermitian theorem, but to prove a four-variable
Möbius-weighted extension of (4.665).

### 4.77 Unitary-divisor roots collapse the two Möbius weights

The midpoint coefficient exposes a second exact reindexing.  Put

\[
 n:=rs,
 \qquad
 \mathscr A(n):=\{A\pmod{2n}:A^2\equiv1\pmod{2n}\}.
\tag{4.669}
\]

Only squarefree \(n\) contribute.  For such \(n\), the map

\[
 (r,s)\longmapsto
 A_{r,s}=2r\bar r_s-1\pmod{2n},
 \qquad rs=n,quad(r,s)=1,
\tag{4.670}
\]

is a bijection from ordered coprime factorizations of \(n\) onto
\(\mathscr A(n)\).  For odd \(p\mid n\), the inverse map places \(p\)
in \(r\) when \(A\equiv-1\pmod p\) and in \(s\) when
\(A\equiv1\pmod p\).  If \(2\mid n\), the residue modulo four resolves
the otherwise ambiguous prime two: \(A\equiv-1\pmod4\) places it in
\(r\), while \(A\equiv1\pmod4\) places it in \(s\).  Equivalently, if
\(n_{\mathrm{odd}}=n/(n,2)\), then

\[
 r_{\mathrm{odd}}=(A+1,n_{\mathrm{odd}}),
 \qquad
 s_{\mathrm{odd}}=(A-1,n_{\mathrm{odd}}),
 \qquad
 \#\mathscr A(n)=2^{\omega(n)}.
\tag{4.671}
\]

The two Möbius factors now collapse without an estimate:

\[
 \boxed{\mu(r)\mu(s)=\mu(rs)=\mu(n)}
 \qquad ((r,s)=1).
\tag{4.672}
\]

For \(A\in\mathscr A(n)\), let \(r_A,s_A\) be the factors recovered by
(4.671), including the modulo-four rule, and let
\(\mathscr A_{R,S}(n)\) impose \(r_A\asymp R\), \(s_A\asymp S\), the
endpoint conditions, and \(qr_A,qs_A\le N\).  Formula (4.663) becomes
the exact finite reindexing

\[
\begin{aligned}
 \mathfrak H_q[\Psi]
 ={}&\sum_{n}\mu(n)
 \sum_{\substack{A\in\mathscr A_{R,S}(n)\\(q,n)=1}}
 p_N(qr_A)p_N(qs_A)\frac{RS}{n}\\
 &\quad\times\sum_{c,v\bmod 2n}
 \widetilde\Theta_{r_A,s_A}(c,v)
 \left\{e\!\left(\frac{Acv}{2n}\right)-1\right\}.
\end{aligned}
\tag{4.673}
\]

Here \(RS/4\le n\le4RS\); at the balanced hard box
\(n\asymp T^6\), the physical numerator \(|h\delta|\) has exponent
five, and the completed numerator \(|cv|\) has exponent seven.  The root
multiplicity \(2^{\omega(n)}\le\tau(n)=n^{o(1)}\) has no positive-power
cost.  Thus (4.673) genuinely replaces two Möbius variables of length
\(T^3\) by one Möbius variable of length \(T^6\) and a subpower root
fiber.

This is not yet a one-dimensional Möbius exponential sum to which a
published theorem applies.  The balanced-root filter is nonmultiplicative,
and the inner coefficient retains its joint dependence on
\((n,A,c,v)\); in particular, the Chinese-remainder representative of
\(A\) couples all prime factors of \(n\).  The exact remaining root-trace
gate is

\[
 \boxed{
 \left|\sum_{n\asymp T^6}\mu(n)
       \sum_{A\in\mathscr A_{T^3,T^3}(n)}
       \mathcal G_q(n,A)\right|
 \ll_{B,W}T^7(\log T)^{-B},}
\tag{4.674}
\]

where \(\mathcal G_q(n,A)\) is exactly the weighted \(c,v\)-sum in
(4.673).  A useful next theorem would have to exploit cancellation in
\(\mu(n)\) before taking absolute values over the root fiber.  The helper
`midpoint_unitary_divisor_root_bijection` verifies (4.670)--(4.672),
including the even-prime branch, on finite integers.  The adapter
`midpoint_unitary_divisor_audit` records the exponents \(6,6,5,7\) and
keeps `unitary_root_trace_bound_verified=False`.

### 4.78 Root-Farey large sieve leaves the same deficit in both gauges

The fraction attached to a root is reduced:

\[
 \left(A,2n\right)=1,
 \qquad
 \theta_{n,A}:=\frac{A}{2n}\pmod1.
\tag{4.675}
\]

Moreover, (4.670)--(4.671) show that \(\theta_{n,A}\) uniquely recovers
the ordered factorization.  Thus the root fractions are distinct.  For
\(n_1,n_2\asymp T^6\), ordinary reduced-fraction spacing gives only

\[
 \|\theta_{n_1,A_1}-\theta_{n_2,A_2}\|
 \ge\frac1{4n_1n_2}gg T^{-12}.
\tag{4.676}
\]

This denominator growth prevents a generic additive large sieve from
using the reindexing.  On the physical side, the product coefficient
\(\nu(a)\), \(a=h\delta\), has length exponent five and the exact
product-energy estimate has exponent five, up to one logarithm.  There
are \(T^{6+o(1)}\) root points.  Cauchy over the points followed by the
large sieve therefore has exponent

\[
 \frac62+\frac{\max(5,12)+5}{2}
 =\frac{23}{2}.
\tag{4.677}
\]

The physical local target has exponent six, so the deficit is
\(23/2-6=11/2\).  On the completed side, \(a=cv\) and its product
energy both have exponent seven.  The identical calculation gives

\[
 \frac62+\frac{\max(7,12)+7}{2}
 =\frac{25}{2},
 \qquad
 \frac{25}{2}-7=\frac{11}{2}.
\tag{4.678}
\]

These are optimistic bounds: the actual smooth coefficient is joint in
the root point and the numerator variables, so the separation required
by the displayed large-sieve calculation has not been justified.  Even
after granting it, the same positive deficit remains in both gauges.
Consequently the unitary-root reindexing is useful only if \(\mu(n)\)
is kept inside a Type-II or dispersion step; taking absolute values over
the root points first is ruled out.  The helper
`midpoint_root_fraction_identity` checks reduction and exact recovery,
while `midpoint_root_farey_large_sieve_audit` records both \(11/2\)
deficits and keeps `root_farey_large_sieve_closes_gate=False`.

### 4.79 Root CRT exposes the exact Möbius Type-II kernel

Apply the approved finite identity to the single outer Möbius factor in
(4.673).  For \(n>U\),

\[
 \mu(n)=-\sum_{de=n,\ d>U}c_U(d)\mu(e),
 \qquad
 c_U(d)=\sum_{j\mid d,\ j\le U}\mu(j).
\tag{4.679}
\]

The Type-II cells have \(d>U\) and \(e>V\).  Since the contributing
\(n\) are squarefree, \((d,e)=1\).  A root modulo \(2de\) splits
uniquely into roots \(A_d\pmod{2d}\) and \(A_e\pmod{2e}\).  Put

\[
 y_d:=\frac{A_d-1}{2}\pmod d,
 \qquad
 y_e:=\frac{A_e-1}{2}\pmod e.
\]

Ordinary CRT applied to \(y=(A-1)/2\pmod{de}\) gives

\[
 y\equiv y_d\,e\bar e_d+y_e\,d\bar d_e\pmod{de},
 \qquad
 A=2y+1\pmod{2de}.
\tag{4.680}
\]

Here \(\bar e_d\) and \(\bar d_e\) are the indicated inverses.  Dividing
(4.680) by \(de\) yields the exact phase factorization, valid for every
integer \(k\),

\[
 \boxed{
 e\!\left(\frac{kA}{2de}\right)
 =e\!\left(\frac{k}{2de}\right)
  e\!\left(\frac{k y_d\bar e_d}{d}\right)
  e\!\left(\frac{k y_e\bar d_e}{e}\right).}
\tag{4.681}
\]

This handles the even prime as well: the roots are odd, so the two
congruences for \((A-1)/2\) are compatible even though the moduli
\(2d,2e\) have common factor two.

At the balanced central Type-II cell, write \(D=E=T^3\) and use the
physical numerator \(k:=-h\delta\), so \(|k|\asymp T^5\).  This sign
matches the midpoint arithmetic phase in (4.659).  After grouping equal
products into the coefficient \(\nu(k)\), the remaining sum is exactly
of the form

\[
\begin{aligned}
 \mathcal{RTII}_{q}(D,E,K)
 :={}&\sum_{|k|\asymp K}\nu(k)
 \sum_{\substack{d\asymp D,\ e\asymp E\\
                  (d,e)=1,\ de\ {\rm squarefree}}}
 c_U(d)\mu(e)\\
 &\quad\times
 \sum_{\substack{A_d^2\equiv1\ (2d)\\
                  A_e^2\equiv1\ (2e)}}
 \Omega_q(d,e,A_d,A_e,k)\\
 &\quad\times e\!\left(\frac{k}{2de}
       +\frac{k y_d\bar e_d}{d}
       +\frac{k y_e\bar d_e}{e}\right).
\end{aligned}
\tag{4.682}
\]

The weight \(\Omega_q\) is the original coupled smooth kernel together
with the balanced-root condition recovered from the combined root in
(4.680), both endpoint tapers, \((q,de)=1\), and
\(qr_A,qs_A\le N\).  No factor in it has been separated.  The root
fibers have size \((de)^{o(1)}\).  The completed version replaces the
single \(k\)-sum by \(c,v\asymp T^{7/2}\) and uses \(k=cv\); it is
exactly equivalent by (4.663a).

Consequently one sufficient central-cell theorem is

\[
 \boxed{
 |\mathcal{RTII}_{q}(T^3,T^3,T^5)|
 \ll_{B,W}T^6(\log T)^{-B}.}
\tag{4.683}
\]

Formula (4.682) is a three-scale Möbius-weighted Type-II sum with fixed
exponents \((3,3,5)\).  It retains \(c_U(d)\) on one side and \(\mu(e)\)
on the other.  The published Hermitian Kloosterman-fraction theorems do
not apply termwise: their numerator is fixed, whereas here the two
numerators \(k y_d\) and \(k y_e\) vary with the root fibers, and
\(\Omega_q\) is joint in every variable.  The subtraction of one in
the completed formula (4.673) is still exact: summing
\(\widetilde\Theta(c,v)\) over all \(c,v\) selects the physical residue
class \(h\equiv\delta\equiv0\pmod Q\), which is empty because
\(0<H,L<Q\) and both dyadic variables are nonzero.  Therefore the
completed frequency formula may use \(e(Acv/Q)-1\), while its exact
physical inverse (4.682) has \(e(-Ah\delta/Q)\) and no subtraction.
Thus (4.683) is an exact new local gate, not a proved estimate.  The helper
`midpoint_root_crt_phase_identity` checks (4.680)--(4.681) with exact
rationals, and `midpoint_root_type_ii_audit` keeps
`completed_centering_exact=True`,
`physical_zero_residue_vanishes=True`,
`physical_centered_subtraction_present=False`, and
`root_type_ii_bound_verified=False`.

### 4.80 Root fibers unfold to four classical fraction variables

Write the ordered factorization represented by \(A_d\) as
\(d=d_r d_s\), with \(A_d\equiv-1\pmod {2d_r}\) and
\(A_d\equiv1\pmod {2d_s}\), and define \(e=e_r e_s\) in the same
way.  The four factors are pairwise coprime on the squarefree support.
The idempotents \(y_d=(A_d-1)/2\) and \(y_e=(A_e-1)/2\) then satisfy

\[
 \boxed{
 y_d\equiv-d_s\overline{d_s}_{d_r}\pmod d,
 \qquad
 y_e\equiv-e_s\overline{e_s}_{e_r}\pmod e.}
\tag{4.684}
\]

Indeed the first displayed representative is \(-1\) modulo \(d_r\)
and zero modulo \(d_s\), which uniquely characterizes \(y_d\); the
second identity is identical.  Substitution into (4.681) gives the
exact four-factor phase

\[
 \boxed{
 e\!\left(\frac{kA}{2de}\right)
 =e\!\left(
    \frac{k}{2de}
   -\frac{k\,\overline{d_s e}_{d_r}}{d_r}
   -\frac{k\,\overline{e_s d}_{e_r}}{e_r}
          \right).}
\tag{4.685}
\]

A denominator equal to one contributes zero to the corresponding
fraction.  The combined root has negative sign precisely on
\(r=d_r e_r\) and positive sign precisely on \(s=d_s e_s\), so (4.685)
is the midpoint phase for the original ordered factorization
\(de=rs\), not merely a congruent surrogate.

After dyadic subdivision, (4.682) is therefore a sum of the exact form

\[
\begin{aligned}
 \mathcal F_q(D_r,D_s,E_r,E_s,K)
 :={}&\sum_{|k|\asymp K}\nu(k)
 \sum_{\substack{d_r\asymp D_r,\ d_s\asymp D_s\\
                  e_r\asymp E_r,\ e_s\asymp E_s\\
                  d_r d_s e_r e_s\ {\rm squarefree}}}
 c_U(d_r d_s)\mu(e_r)\mu(e_s)\\
 &\quad\times
 \Omega_q(d_r d_s,e_r e_s,A_{d_r,d_s},A_{e_r,e_s},k)\\
 &\quad\times e\!\left(
   \frac{k}{2d_r d_s e_r e_s}
  -\frac{k\,\overline{d_s e_r e_s}_{d_r}}{d_r}
  -\frac{k\,\overline{e_s d_r d_s}_{e_r}}{e_r}
                         \right).
\end{aligned}
\tag{4.686}
\]

The squarefree condition in (4.686) is equivalent to individual
squarefreeness plus all six cross-coprimality conditions.  The weight is
exactly the joint weight from (4.682): it still contains the original
coupled transform, the \(q\)-coprimality, both mollifier tapers, and the
four support restrictions.  In particular no tensor separation is
asserted.

On the balanced central face the complete dyadic scale list can be
parametrized by \(0\le\alpha\le3\):

\[
 D_r=T^\alpha,
 \quad D_s=T^{3-\alpha},
 \quad E_r=T^{3-\alpha},
 \quad E_s=T^\alpha,
 \quad K=T^5.
\tag{4.686a}
\]

Thus \(D_rD_s=E_rE_s=D_rE_r=D_sE_s=T^3\).  Up to powers of
\(\log T\) from the dyadic partition, the precise local inequality
sufficient on every such box is

\[
 \boxed{
 |\mathcal F_q(T^\alpha,T^{3-\alpha},
                    T^{3-\alpha},T^\alpha,T^5)|
 \ll_{B,W}T^6(\log T)^{-B}
 \quad(0\le\alpha\le3).}
\tag{4.687}
\]

The endpoint \(\alpha=3\) has
\((d_r,d_s,e_r,e_s)=(d,1,1,e)\).  Formula (4.685) becomes

\[
 e\!\left(\frac{k}{2de}-\frac{k\bar e_d}{d}\right)
 =e\!\left(\frac{k(2d\bar d_e-1)}{2de}\right),
\tag{4.688}
\]

where the equality follows from additive reciprocity.  Hence this
endpoint recovers the original hard Kloosterman fraction with weight
\(c_U(d)\mu(e)\); root unfolding does not delete the endpoint sector.
It does, however, replace the abstract root fiber by the explicit
four-variable family (4.686), so any successful Cauchy--reciprocity--
complementary-divisor--Kuznetsov argument can now be stated directly on
the variables it must average.  The exact helper
`midpoint_root_four_factor_phase_identity` verifies (4.684)--(4.685)
and recovery of \(r,s\); the ledger keeps
`completed_centering_exact=True`,
`physical_zero_residue_vanishes=True`,
`physical_centered_subtraction_present=False`, and
`four_factor_type_ii_bound_verified=False`.

### 4.81 One physical Poisson step gives the exact resonance lattice

There is a useful deterministic saving inside each fixed balanced
root point before any Möbius estimate.  Fix coprime \(r,s>1\), put

\[
 Q=2rs,
 \qquad
 A=2r\bar r_s-1,
 \qquad
 U=Q/L,
\tag{4.689}
\]

and retain the joint physical amplitude as
\(\Phi_{r,s,h}(\delta/L)\).  With the convention
\(\widehat f(\xi)=\int_{\mathbb R}f(x)e(-x\xi)\,dx\), Poisson
summation in \(\delta\) alone gives the exact identity

\[
 \sum_{\delta\in\mathbb Z}
 \Phi_{r,s,h}(\delta/L)e\!\left(-\frac{Ah\delta}{Q}\right)
 =L\sum_{v\in\mathbb Z}
 \widehat\Phi_{r,s,h}\!\left(L\left(v+\frac{Ah}{Q}\right)\right).
\tag{4.690}
\]

All other variables remain frozen in (4.690); no separation of the
joint kernel is used.  The already proved dyadic derivative bounds give,
for every fixed \(C>0\),

\[
 \left|\widehat\Phi_{r,s,h}\!\left(\frac{Lu}{Q}\right)\right|
 \ll_{C,W}\left(1+\frac{|u|}{U}\right)^{-C}.
\tag{4.690a}
\]

For a term of (4.690), define the integer \(u:=Ah+vQ\).  Since
\(A\equiv-1\pmod {2r}\) and \(A\equiv1\pmod {2s}\), there are unique
integers \(a,b\) satisfying

\[
 \boxed{
 h=ra+sb,
 \qquad
 u=ra-sb,
 \qquad
 a=\frac{h+u}{2r},
 \quad b=\frac{h-u}{2s}.}
\tag{4.691}
\]

Conversely (4.691) gives \(u\equiv Ah\pmod Q\), because it gives the
two defining congruences modulo \(2r\) and \(2s\).  Thus (4.691) is a
bijection, including the even-prime branch; it is exactly the
determinant-line resonance in root coordinates.

For \(|h|\le2H\) and \(|u|\le X\), (4.691) gives the elementary lattice
count

\[
 \#\{(h,u)\}
 \le
 \left(2+\frac{2H+X}{r}\right)
 \left(2+\frac{4H}{s}\right).
\tag{4.692}
\]

Indeed the first factor bounds the possible integers \(a\) from
\(|2ra|=|h+u|\le2H+X\); after \(a\) is fixed, the interval of possible
\(b\) cut out by \(|h|\le2H\) has length at most \(4H/s\).  Applying
(4.692) on the shells \(2^{j-1}U<|u|\le2^jU\), and then summing the
decay (4.690a), proves

\[
 \sum_{h\asymp H}\left|
  \sum_{\delta\asymp L}
   \Phi_{r,s,h}(\delta/L)e\!\left(-\frac{Ah\delta}{Q}\right)
                         \right|
 \ll_{C,W}
 L\left(1+\frac{H+U}{r}\right)
  \left(1+\frac{H}{s}\right).
\tag{4.692a}
\]

At the central box
\(r,s\asymp T^3\), \(H=L=T^{5/2}\), \(Q\asymp T^6\), and
\(U\asymp T^{7/2}\).  Hence (4.692a) is \(O_W(T^3)\), a proved
\(T^2\) saving over the raw \(HL=T^5\) physical pair.  Summing this
pointwise bound absolutely over the \(T^6\) outer root points gives
only \(T^9\).  The remaining sufficient inequality is therefore the
explicit signed outer gate

\[
 \boxed{
 \left|\sum_{\substack{r,s\asymp T^3\\(r,s)=1}}
 \mu(r)\mu(s)p_N(r)p_N(s)\,\mathcal B_{r,s}\right|
 \ll_{B,W}T^6(\log T)^{-B},
 \qquad
 |\mathcal B_{r,s}|\ll_W T^3.}
\tag{4.693}
\]

This is not a new independent square-root conjecture.  On the
cancellation sector write

\[
 g=(|a|,|b|),
 \qquad a=gv_0,
 \qquad b=-gj_0,
 \qquad h=g\delta_0,
 \qquad (j_0,v_0)=1.
\]

Then the first equation in (4.691) is exactly

\[
 \boxed{rv_0-sj_0=\delta_0,}
 \qquad
 \frac ug=rv_0+sj_0.
\tag{4.694}
\]

The first identity in (4.694) is (4.155), with precisely the scales
\(j_0,v_0\asymp T^{1/2}/g\),
\(\delta_0\asymp T^{5/2}/g\), and line length
\(T^{5/2}g\) from (4.161).  Consequently the signed outer estimate
(4.693) is the physical-Poisson realization of the already isolated
unimodular square-root family \(\mathrm{USR}_B\) in (4.168).  The
pointwise \(T^2\) physical saving proves the resonance count but does
not bypass the two-affine-form Möbius correlation.

Thus the physical oscillation supplies two of the five powers needed
from the raw \((h,\delta)\)-family, while (4.693) still requires the
full square-root saving \(T^3\) across the \(T^6\) two-Möbius outer
points.  No cited published result proves this joint square-root gate.
The helper `midpoint_involution_resonance_lattice_identity` checks
(4.691) exactly, `midpoint_physical_poisson_audit` records the exponent
ledger, and records `physical_poisson_route_is_independent=False` and
`outer_mobius_square_root_verified=False` at the same proof boundary as
(4.168).

### 4.82 Full root trace is a Salié sum but the adapter is nonuniform

The preceding root reindexing has a genuine metaplectic interpretation
when the balanced-root filter is temporarily removed.  Let \(n>1\) be
odd and squarefree, let \(\chi_n\) be the Jacobi symbol, and put

\[
 \tau_n:=\sum_{y\bmod n}\chi_n(y)e(y/n),
 \qquad
 \mathcal W_k(n):=\sum_{A^2\equiv1\ (n)}e(kA/n).
\tag{4.695}
\]

For \((k,n)=1\), set \(b\equiv k^2\bar4\pmod n\) and define

\[
 T(1,b;n):=\sum_{x\bmod n}^{*}\chi_n(x)
 e\!\left(\frac{x+b\bar x}{n}\right).
\]

The Salié evaluation is the exact identity

\[
 \boxed{T(1,k^2\bar4;n)=\tau_n\mathcal W_k(n).}
\tag{4.696}
\]

For completeness, (4.696) holds coefficientwise in the group ring of
\(\mathbb Z/n\mathbb Z\):

\[
 \sum_x^*\chi_n(x)[x+k^2\bar4\bar x]
 =\left(\sum_y\chi_n(y)[y]\right)
  \left(\sum_{A^2\equiv1\ (n)}[kA]\right).
\tag{4.696a}
\]

Thus this step uses no analytic estimate.  If \(k=2a\), the change of
variable \(x=ay\) also gives

\[
 T(1,a^2;n)=\chi_n(a)S(a,a;n),
 \qquad
 S(a,a;n):=\sum_y^*\chi_n(y)e\!\left(\frac{a(y+\bar y)}n\right),
\tag{4.697}
\]

which is precisely the diagonal Salié sum in Duke--Friedlander--Iwaniec,
[Weyl Sums for Quadratic Roots, (7.1)--(7.3)](https://www.math.ucla.edu/~wdduke/preprints/weylsums.pdf).
Their Theorem 7.1, with the auxiliary parameters suppressed in the most
favourable way, bounds a smooth fixed-\(a\) modulus sum by

\[
 x^{47/118+35/59+\varepsilon}
 =x^{117/118+\varepsilon}
 \qquad(a<x).
\]

At \(x=T^6\) and \(a\le T^5\), this is

\[
 T^{351/59+\varepsilon};
 \qquad
 6-\frac{351}{59}=\frac3{59}.
\tag{4.698}
\]

So the published theorem does give a fixed-numerator power saving for
the unrestricted odd full-root trace.  It does not prove the MWKF gate.
There are five separate failures:

1. the actual midpoint modulus is \(2n\), and reducing it to the odd
   trace requires parity splits; the complete even branch has not been
   matched to the theorem;
2. \(\mathscr A_{T^3,T^3}(n)\) is a balanced subset of the roots,
   whereas the Salié sum contains every ordered factorization;
3. the modulus carries \(\mu(n)\), which is not an allowed smooth
   coefficient in Theorem 7.1;
4. \(a\) moves through a family of exponent five and the coupled weight
   depends jointly on the modulus, root, and numerator, while the theorem
   fixes \(a\);
5. the theorem excludes its square-\(a\) exceptional term.

Even discarding all five hypothesis failures and summing (4.698)
absolutely over the \(T^5\) physical numerators gives exponent

\[
 5+\frac{351}{59}=\frac{646}{59},
 \qquad
 \frac{646}{59}-6=\frac{292}{59}>0.
\tag{4.698a}
\]

Hence fixed-numerator Salié cancellation is short by \(T^{292/59}\)
before the genuine adapter failures are charged.  A viable metaplectic
route would require a spectral large sieve simultaneous in the moving
numerator, the Möbius-weighted modulus, and the balanced root test.
The helper `odd_root_trace_salie_coefficient_identity` verifies (4.696a)
with integer coefficient tables, while `root_salie_adapter_audit` keeps
`salie_adapter_closes_root_gate=False`.

### 4.83 Joint Salié averaging is the existing BCR endpoint

Opening the Salié sum does not create a previously unused generic
numerator average.  For odd \(c\) and \((2a,c)=1\), the exact evaluation
used by Duke--Friedlander--Iwaniec is

\[
 \boxed{
 c^{-1/2}S(a,a;c)
 =\varepsilon_c\left(\frac ac\right)
  \sum_{\substack{mn=c\\(m,n)=1}}
  e\!\left(2a\left(\frac{\bar m}{n}-\frac{\bar n}{m}\right)\right).}
\tag{4.699}
\]

On the midpoint parity branch on which \(k=4a\), (4.666) identifies
the phase in (4.699), up to the already recorded parity factor, with
the full-root phase \(e(kA/(2c))\).  The balanced-root filter is exactly
\(m,n\asymp T^3\), while \(a\asymp T^5\).  Therefore simultaneous
averaging over the numerator with arbitrary coefficients is precisely
the Bettin--Chandee trilinear input at

\[
 A=T^5,
 \qquad M=N=T^3.
\]

Substitution in their two terms gives

\[
 \mathrm{BC}_1
 =\frac{17}{20}(5+3+3)+\frac34
 =\frac{101}{10},
 \qquad
 \mathrm{BC}_2
 =\frac78(3+3)+5+\frac38
 =\frac{85}{8}.
\tag{4.700}
\]

The larger exponent is \(85/8\); against the physical target six, the
exact deficit is

\[
 \boxed{\frac{85}{8}-6=\frac{37}{8}.}
\tag{4.701}
\]

This is exactly the \(\delta=3\) endpoint already present in (4.49).
Hence neither the Salié evaluation nor a generic spectral large sieve
improves the published BCR coverage.  Any improvement must keep
\(\mu(m)\mu(n)\) inside the joint estimate rather than replace those
coefficients by their \(L^2\) norms.

The square-numerator exception can also be isolated exactly.  For
positive physical variables, \(h\delta\) is a square if and only if
there are unique positive \(x,y\) and one squarefree \(g\) such that

\[
 \boxed{h=gx^2,\qquad \delta=gy^2.}
\tag{4.702}
\]

Consequently, for dyadic lengths \(H,L\),

\[
 \#\{h\asymp H,\ \delta\asymp L:h\delta\text{ is a square}\}
 \ll \sum_{g\le2\min(H,L)}
       \sqrt{\frac Hg}\sqrt{\frac Lg}
 \ll \sqrt{HL}\log(2HL).
\tag{4.702a}
\]

At \(H=L=T^{5/2}\), this square-parameter family has exponent \(5/2\).
DFI Theorem 4 does have a genuine main term for an unrestricted modulus
average with square parameter.  That main term cannot be transferred to our
balanced-root sum.  In the proof of that theorem it is produced only by
the pieces called \(S_1\) and \(\bar S_1\), where one factor is at most
\(y\).  At \(a=T^5\), \(x=T^6\), and fixed congruence modulus, their
choices (5.4) and (5.14) are exactly

\[
 y=T^{7/5},\qquad z=T^{174/59}.
\tag{4.702b}
\]

Our filter has both factors of length \(T^3\), and
\(3>174/59>7/5\).  It lies entirely in their long--long piece \(S_3\),
which is bounded by Theorem H and has no exceptional main term.  Thus
the earlier transfer of a modulus-length \(T^6\) square main term into
the balanced sector was invalid; no Möbius cancellation of such a term
is required.

For each fixed square numerator \(a=t^2\asymp T^5\), DFI Theorem H,
formula (1.5), with \(M=N=T^3\), gives the exact exponent

\[
 \|\alpha\|_2\|\beta\|_2
 (a+MN)^{3/8}(M+N)^{11/48}
 \ll T^{3+18/8+33/48+\varepsilon}
 =T^{95/16+\varepsilon}.
\tag{4.702c}
\]

The theorem accepts \(\alpha_m=\mu(m)\) and \(\beta_n=\mu(n)\), but
uses them only through their \(L^2\) norms.  Summing (4.702c) absolutely
over the \(T^{5/2}\) possible square roots gives

\[
 T^{5/2+95/16}=T^{135/16},
 \qquad \frac{135}{16}-6=\frac{39}{16}.
\tag{4.702d}
\]

Thus the square sector is smaller than the full numerator family, but
the published balanced Hermitian estimate is still short by
\(T^{39/16}\) at the MWKF target.  The exact remaining square-sector
gate is

\[
 \boxed{
 \left|\sum_{t\asymp T^{5/2}}\nu(4t^2)
  \sum_{n\asymp T^6}\mu(n)
  \sum_{A\in\mathscr A_{T^3,T^3}(n)}
  \Omega_q(n,A,4t^2)e\!\left(\frac{2t^2A}{n}\right)
       \right|
 \ll_{B,W}T^6(\log T)^{-B}.}
\tag{4.703}
\]

Formula (4.703) retains the balanced-root test and the actual joint
kernel.  The helper `square_product_common_kernel_identity` verifies
(4.702), while `root_salie_joint_average_audit` records the BCR
correspondence, the corrected \(39/16\) square-sector deficit, and
`balanced_root_filter_excludes_dfi_square_main=True`.

### 4.84 Quadratic Gauss completion linearizes the square numerator

There is one further exact transformation of (4.703), but its raw
length ledger goes in the wrong direction.  Put

\[
 G(a;c):=\sum_{x\bmod c}e\!\left(\frac{ax^2}{c}\right).
\]

For odd coprime \(r,s\) and every integer \(t\), completing the two
quadratic phases gives the finite identity

\[
\boxed{
 G(-2r;s)G(2s;r)
 e\!\left(2t^2\left(\frac{\bar r}{s}
                  -\frac{\bar s}{r}\right)\right)
 =\sum_{x\bmod s}\sum_{y\bmod r}
 e\!\left(\frac{-2rx^2+4tx}{s}
           +\frac{2sy^2+4ty}{r}\right).}
\tag{4.704}
\]

Indeed, translation by \(t\bar r\bmod s\) in the first Gauss sum and
by \(t\bar s\bmod r\) in the second gives (4.704) term by term.  The
usual odd Gauss evaluation shows that

\[
 \eta(r,s):=\frac{\sqrt{rs}}{G(-2r;s)G(2s;r)},
 \qquad |\eta(r,s)|=1,
\tag{4.705}
\]

and \(\eta(r,s)\) depends only on the residue classes of \(r,s\bmod8\).
In particular, its cross Jacobi factor is exactly

\[
 \left(\frac{-2r}{s}\right)\left(\frac{2s}{r}\right)
 =\left(\frac{-1}{s}\right)
  \left(\frac2s\right)\left(\frac2r\right)
  (-1)^{(r-1)(s-1)/4}.
\]

Thus there is no uncontrolled quadratic character joining the two
long factors.

The new phase has a useful exact factorization.  Set

\[
 z:=rx+sy,\qquad w:=sy-rx.
\]

Then

\[
 \frac{-2rx^2+4tx}{s}+\frac{2sy^2+4ty}{r}
 \equiv \frac{2z(w+2t)}{rs}\pmod 1.
\tag{4.706}
\]

Consequently the square root \(t\) is linear rather than quadratic.
However, on the hard box

\[
 r\asymp s\asymp T^3,\qquad t\asymp T^{5/2},\qquad
 x\bmod s,\quad y\bmod r,\quad (r,s)=1,\quad 2\nmid rs,
\]

the map \((x,y)\mapsto z\bmod rs\) is a bijection.  Smooth summation in
\(t\) restricts \(z\) to intervals of total length
\(rs/T^{5/2}=T^{7/2}\) around the finitely many resonant residue
classes.  Even granting rapid decay away from those intervals, the
pointwise absolute ledger is therefore

\[
 T^{-3}\cdot T^{7/2}\cdot T^{5/2}=T^3.
\]

Here \(T^{-3}\) is the Gauss normalization \((rs)^{-1/2}\).  Direct
absolute summation of the original square family costs only
\(T^{5/2}\).  Thus Gauss completion loses \(T^{1/2}\) unless the
quadratic residue variables and the two Möbius weights are estimated
jointly.

Writing \(\Omega_q(r,s,t)\) for the exact dyadic coupled weight inherited
from (4.703), the remaining transformed gate is

\[
\boxed{
 \left|\sum_{\substack{r\asymp T^3,\ s\asymp T^3\\
                       (r,s)=1,\ 2\nmid rs}}
 \frac{\mu(r)\mu(s)\eta(r,s)}{\sqrt{rs}}
 \sum_{x\bmod s}\sum_{y\bmod r}
 \sum_{t\asymp T^{5/2}}
 \nu(4t^2)\Omega_q(r,s,t)
 e\!\left(\frac{2(rx+sy)(sy-rx+2t)}{rs}\right)
 \right|
 \ll_{B,W}T^6(\log T)^{-B}.}
\tag{4.707}
\]

No published estimate located in this audit accepts the simultaneous
quadratic residue sums, the two Möbius modulus weights, and the coupled
weight in (4.707).  The helper
`square_salie_double_gauss_identity` verifies (4.704), (4.706), and the
mod-eight character formula by exact coefficient tables.  The ledger
`square_salie_gauss_completion_audit` therefore keeps
`gauss_completion_improves_square_sector=False` and does not close the
MWKF gate.

### 4.85 The sufficient Möbius fourth moment is one shifted determinant gate

The top separated fourth moment (4.562) can be reduced exactly one step
further.  This does not make the componentwise sufficient condition
necessary for the original signed kernel, but it isolates its complete
arithmetic content without a generic mean-value bound.

For fixed smooth \(U\) supported in \([1,2]\), put

\[
 P_U(t):=\sum_n\frac{\mu(n)U(n/T)}{n^{1/2+it}},
 \qquad
 C_U(m):=\sum_{ab=m}\mu(a)\mu(b)U(a/T)U(b/T).
\tag{4.708}
\]

Then the finite Dirichlet-polynomial identity

\[
 P_U(t)^2=\sum_m\frac{C_U(m)}{m^{1/2+it}}
\]

is exact.  With the Fourier convention
\(\widehat\Omega(\xi)=\int_{\mathbb R}\Omega(u)e(-u\xi)\,du\), direct
integration gives

\[
\boxed{
 \int_{\mathbb R}|P_U(t)|^4\Omega(t/T)\,dt
 =T\sum_{m,n}
 \frac{C_U(m)\overline{C_U(n)}}{\sqrt{mn}}
 \widehat\Omega\!\left(
   \frac{T}{2\pi}\log\frac mn\right).}
\tag{4.709}
\]

There is no approximate functional equation in (4.709).  All sums are
finite, and \(m,n\in[T^2,4T^2]\).

The multiplicative diagonal has only a logarithmic cost.  If
\(ab=cd\), set

\[
 g=(a,c),\qquad a=gx,\qquad c=gy,qquad(x,y)=1.
\]

Then \(xb=yd\), so there is a unique positive integer \(k\) with

\[
 \boxed{a=gx,\qquad c=gy,\qquad b=yk,\qquad d=xk.}
\tag{4.710}
\]

Conversely (4.710) always gives \(ab=cd\).  The dyadic supports force
\(x/y\) into a fixed compact subinterval of \((0,\infty)\), and for
fixed coprime \((x,y)\) both \(g\) and \(k\) have
\(O(1+T/\max(x,y))\) choices.  Therefore

\[
 \sum_m\frac{|C_U(m)|^2}{m}
 \ll_U T^{-2}
 \sum_{\substack{(x,y)=1\\x\asymp y}}
 \left(1+\frac{T}{\max(x,y)}\right)^2
 \ll_U\log(2T).
\]

Thus the diagonal in (4.709) already has the required
\(T\log T\) size.

For the off-diagonal write \(h=ab-cd\).  Since
\(ab,cd\asymp T^2\), the Fourier argument in (4.709) is comparable to
\(h/T\) whenever \(|h|=o(T^2)\).  Every fixed shell
\(|h|\ge T^{1+\eta}\), \(\eta>0\), is power-negligible after using an
arbitrarily high Schwartz seminorm of \(\widehat\Omega\).  The
polylogarithmic collar \(|h|=T^{1+o(1)}\) must remain inside the local
estimate; it is not discarded as a tail.

The exact sufficient off-diagonal gate is consequently the single sum

\[
\boxed{
 \left|
 \sum_{\substack{a,b,c,d\asymp T\\ab\ne cd}}
 \frac{\mu(a)\mu(b)\mu(c)\mu(d)
       U(a/T)U(b/T)\overline{U(c/T)U(d/T)}}
      {\sqrt{abcd}}
 \widehat\Omega\!\left(
   \frac{T}{2\pi}\log\frac{ab}{cd}\right)
 \right|
 \ll_{U,\Omega}(\log T)^{1+o(1)}.}
\tag{4.711}
\]

On the critical collar \(|h|=T^{1+o(1)}\), the unnormalised solution
family \(ab-cd=h\) has exponent three: one exponent for \(h\) and two
for a fixed determinant fiber.  The four factors in (4.711) contribute
the normalization \(T^{-2}\).  Hence (4.711) requires exactly the
fixed saving

\[
 T^3\longrightarrow T^2,
\]

with additional logarithmic cancellation for the global little-oh.
This is the same one-power determinant obstruction as (4.473), now
written as one shifted \((\mu*\mu)\) variance rather than a spectral
Gram form.  Published short-interval Möbius theorems give logarithmic
decay from the raw variance but not this diagonal-scale saving.

The helper `balanced_product_diagonal_parameterization` verifies
(4.710) on integers.  The adapter
`mobius_product_shifted_variance_audit` records the exponent ledger
\(3\to2\), retains the polylogarithmic transition collar, and keeps
`shifted_mobius_determinant_bound_proved=False`.  Finally,
(4.711) is equivalent to the separated component (4.562), but the
original signed DCV superposition does not require every such component;
no converse is asserted.

### 4.86 The smooth determinant-surface theorem does not accept the Möbius gate

Ganguly--Guria, Theorem 1.1, proves the following precise fixed-shift
statement.  If \(V\in C_c^\infty([1,2])\), \(r\ne0\), and

\[
 S_V(X,r):=
 \sum_{ad-bc=r}V(a/X)V(b/X)V(c/X)V(d/X),
\]

then

\[
 \boxed{
 S_V(X,r)=\mathcal M_V(X,r)
     +O_\varepsilon\!\left(|r|^\theta X^{1+\varepsilon}\right),
 \qquad \theta\le \frac7{64}.}
\tag{4.712}
\]

The support forces \(|r|<3X^2\), and their explicit main term has size
\(X^2\) in the range relevant here.  This is a theorem for the
unweighted count with the same smooth function in all four variables.
It does not state an estimate with four arithmetic coefficient
sequences.  Remark 1.4 says that the method can also handle
\(\alpha x_1x_2-\beta x_3x_4=r\), but it gives no dependence on
\(\alpha,\beta\).  Consequently that remark is not a uniform theorem
adapter for the divisor parameters produced by a Möbius Type I/II
identity.

At the critical collar in (4.711), put \(X=T\) and
\(1\le |r|\le T\mathscr L^A\), where \(A\) is fixed.  The published
pointwise error in (4.712) is then

\[
 |r|^{7/64}X^{1+\varepsilon}
 \le T^{71/64+\varepsilon}\mathscr L^{7A/64}.
\tag{4.713}
\]

Even under the strictly stronger, unproved assumption that (4.712)
accepted the four Möbius weights in (4.711) with the same error,
absolute summation over the \(T^{1+o(1)}\) shifts would give

\[
 \boxed{
 T^{1+o(1)}T^{71/64+\varepsilon}
   =T^{135/64+\varepsilon+o(1)},
 \qquad
 \frac{135}{64}-2=\frac7{64}.}
\tag{4.714}
\]

Thus the fixed-shift theorem still misses the unnormalised target
\(T^2\mathscr L^{1+o(1)}\) by the exact power \(T^{7/64}\).  Assuming
Ramanujan would remove this positive power, but the resulting
\(T^{2+\varepsilon}\) ledger supplies neither the required logarithmic
little-oh nor cancellation of the \(T^2\)-sized main term for each
shift.  With the theorem as actually stated, the complete implication
ledger is

\[
 \boxed{
 \text{smooth unweighted fixed shift}
 \not\Longrightarrow
 \text{four-Möbius shifted determinant},
 \quad
 \text{absolute residual deficit}=\frac7{64}.}
\tag{4.715}
\]

The only place where the factor \(r^\theta\) enters their proof is the
pointwise treatment of a Hecke coefficient at \(nr/l\).  Averaging the
shift before applying the spectral estimate is therefore the natural
next candidate for eliminating \(7/64\); it still requires a new
mechanism that transports the four Möbius weights through the initial
Poisson step.  The adapter `ganguly_guria_determinant_audit` records
these exact exponents and keeps
`ganguly_guria_route_closes_mobius_gate=False`.

### 4.87 Published short-interval variance classes exclude the restricted inverse-zeta square

There is a second exact interpretation of the exponent \(3\to2\) in
(4.711).  The product variable has size \(X=T^2\), while the Fourier
kernel restricts additive differences to the window
\(H=X/T=T\).  For a fixed smooth compactly supported additive window
\(\phi\), the diagonal-scale local variance required by a smoothed
Gallagher reduction is

\[
 \boxed{
 \int_X^{2X}
 \left|\sum_m C_U(m)\phi\!\left(\frac{m-x}{H}\right)\right|^2dx
 \ll XH(\log X)^{1+o(1)},
 \qquad X=T^2,\ H=T.}
\tag{4.716}
\]

The generic absolute ledger is \(XH^2=T^4\); (4.716) is
\(XH=T^3\).  Thus this formulation requires the same one power of
\(T\) as (4.711), now as square-root variance in intervals of length
\(X^{1/2}\).

Darbar--Das prove precise short-interval variance formulae for classes
of the form

\[
 \mathcal F_{\alpha,\beta,k}
   =\{\mathbf 1 *_k h:h\in\mathcal M_{\alpha,\beta}
                          \cup\mathcal G_{\alpha,\beta}\}.
\tag{4.717}
\]

This does not include the coefficient needed here.  Even before the
dyadic factor restriction in \(C_U\), the full convolution
\(f=\mu*\mu\) has Dirichlet series \(F(s)=\zeta(s)^{-2}\).  If it were
written in the \(k=1\) form \(f=\mathbf1*h\), then necessarily

\[
 H(s)=\zeta(s)^{-3},
 \qquad
 \sum_{j\ge0}h(p^j)z^j=(1-z)^3
   =1-3z+3z^2-z^3.
\tag{4.718}
\]

The class \(\mathcal M_{\alpha,\beta}\) is squarefree-supported in its
auxiliary variable, so it forces \(h(p^2)=0\), contrary to
\(h(p^2)=3\).  The class \(\mathcal G_{\alpha,\beta}\) is completely
multiplicative; \(h(p)=-3\) would force \(h(p^2)=9\), again contrary
to (4.718).  Finally, the actual \(C_U\) in (4.708) retains the two
separate restrictions \(a,b\asymp T\) and is not a multiplicative
arithmetic function.

Therefore neither the full inverse-zeta square nor its required
restricted divisor component is an input to the published theorem:

\[
 \boxed{
 \text{Darbar--Das variance class}
 \not\ni \mu*\mu,
 \qquad
 \text{and a fortiori it does not contain }C_U.}
\tag{4.719}
\]

The helper `mobius_triple_convolution_prime_power_coefficients`
checks the local polynomial in (4.718) coefficient by coefficient.
The adapter `darbar_das_short_variance_audit` records the exact
\(4\to3\) variance ledger and keeps
`darbar_das_route_closes_mobius_gate=False`.

### 4.88 Ratio Mellin inversion restores a multiplicative inverse-zeta family

The failure of multiplicativity of \(C_U\) is removable.  For
\(q>0\) and \(y\in\mathbb R\), define

\[
 F_q(y):=U(\sqrt q\,e^y)U(\sqrt q\,e^{-y}),
 \qquad
 \widehat F_q(\tau):=\int_{\mathbb R}F_q(y)e^{-i\tau y}\,dy.
\tag{4.720}
\]

If \(m=ab\), \(q=m/T^2\), and
\(y=\frac12\log(a/b)\), then the two arguments in (4.720) are exactly
\(a/T\) and \(b/T\).  Fourier inversion in the ratio coordinate gives

\[
\boxed{
 C_U(m)=\frac1{2\pi}\int_{\mathbb R}
 \widehat F_{m/T^2}(\tau)f_\tau(m)\,d\tau,}
\qquad
 f_\tau(m):=
 \sum_{ab=m}\mu(a)\mu(b)(a/b)^{i\tau/2}.
\tag{4.721}
\]

This is an exact finite divisor identity followed by ordinary Fourier
inversion; no truncation occurs in (4.721).  For fixed \(\tau\), the
coefficient \(f_\tau\) is multiplicative and

\[
\boxed{
 \sum_{m\ge1}\frac{f_\tau(m)}{m^s}
 =\frac1{\zeta(s-i\tau/2)\zeta(s+i\tau/2)},
 \qquad \Re s>1.}
\tag{4.722}
\]

Because \(U\) is smooth and compactly supported, \(q\) is restricted
to a fixed compact subset of \((0,\infty)\), every \(q\)-derivative of
\(\widehat F_q(\tau)\) decays faster than any fixed power of
\(1+|\tau|\), uniformly in \(q\).  Cauchy in \(\tau\) therefore shows
that a uniform one-parameter local variance estimate is sufficient:

\[
\boxed{
 \sup_{|\tau|\le(\log X)^A}
 \int_X^{2X}
 \left|\sum_m f_\tau(m)V_\tau(m/X)
 \phi\!\left(\frac{m-x}{H}\right)\right|^2dx
 \ll_{A,V,\phi}XH(\log X)^{1+o(1)},
 \quad H=X^{1/2}.}
\tag{4.723}
\]

Here \(V_\tau\) ranges over the bounded Schwartz-seminorm family
generated by \(q\mapsto\widehat F_q(\tau)\); frequencies outside the
displayed polylogarithmic range contribute an arbitrarily large
negative logarithmic power.  Estimate (4.723), with the exact
seminorm bookkeeping needed by (4.716), implies the separated
fourth-moment gate (4.711).

The \(\tau=0\) member also has a larger *formal diagonal* than the
restricted coefficient in (4.708).  Since

\[
 f_0(p)=-2,\qquad f_0(p^2)=1,\qquad f_0(p^j)=0\quad(j\geq3),
\]

one has the exact Euler factorization

\[
 \boxed{
 \sum_{n\geq1}\frac{|f_0(n)|^2}{n^s}
 =\prod_p(1+4p^{-s}+p^{-2s})
 =\zeta(s)^4G(s),}
\tag{4.723a}
\]

where

\[
 \boxed{
 G_p(s)
 =(1-p^{-s})^4(1+4p^{-s}+p^{-2s})
 =1-9p^{-2s}+16p^{-3s}-9p^{-4s}+p^{-6s}.}
\tag{4.723b}
\]

Thus \(G\) converges absolutely for \(\Re s>1/2\), and the classical
Selberg--Delange calculation gives a smooth formal diagonal of order
\(XH(\log X)^3\).  This is two logarithms larger than the requested
\(XH(\log X)^{1+o(1)}\).

This observation does **not** disprove (4.723).  Expanding its full
short-interval energy gives

\[
 \boxed{
 H\sum_{m,n}f_0(m)\overline{f_0(n)}
 V_0(m/X)\overline{V_0(n/X)}
 (\phi*\widetilde\phi)((m-n)/H).}
\tag{4.723c}
\]

Although (4.723c) is nonnegative as a whole, its off-diagonal terms are
signed, so the \(m=n\) contribution is not a lower bound for the full
energy.  A bound of the size in (4.723) would have to cancel both surplus
diagonal logarithms through those off-diagonal terms.  By contrast, the
joint ratio recombination returns the restricted \(C_U\), whose exact
diagonal has only one logarithm by (4.710).  Hence taking Cauchy in
\(\tau\) discards a genuine two-logarithm recombination, but this remains
a logarithmic issue and supplies no positive power.

At \(\tau=0\), however, \(f_0=\mu*\mu\).  Thus this reduction removes
the dyadic divisor restriction but retains the genuine inverse-zeta
variance problem:

\[
 \boxed{
 \text{restricted four-Möbius gate}
 \Longleftarrow
 \text{uniform square-root variance for }
 \frac1{\zeta(s-i\tau/2)\zeta(s+i\tau/2)},
 \quad\text{currently unproved}.}
\tag{4.724}
\]

This is exactly the \(\gamma=0\) endpoint of the variance gate (4.540).
Mangerel's Theorem 1.7, even if its hypotheses and constants are granted
uniformly for all \(|\tau|\le(\log X)^A\), controls the normalized
variance only by a quantity of logarithmic size.  This comparison also
optimistically sets the theorem's long-interval main term to zero;
retaining it adds an obligation.  Undoing its
normalization gives the power ledger

\[
 \boxed{
 XH^2=T^4
 \quad\hbox{versus}\quad
 XH=T^3,
 \qquad\text{remaining deficit }H=T.}
\tag{4.725}
\]

Thus ratio Mellin inversion identifies a clean multiplicative family,
but the published typical-short-interval theorem still saves only
logarithms from the raw scale and not the required square-root factor.
Uniform verification of its non-pretentiousness parameters in the full
polylogarithmic \(\tau\)-range is unnecessary for this rejection and is
not asserted.

The exact-rational helper `restricted_product_ratio_coordinates`
checks both factor reconstructions without numerical square roots.  The
helper `mobius_square_convolution_second_moment_local_factor` verifies
the polynomial in (4.723b) coefficient by coefficient.
The adapter `restricted_mobius_ratio_mellin_audit` records the
\(X=T^2,H=T\) ledger, the formal three-logarithm diagonal, and the fact
that this diagonal alone is not a lower bound for the full signed
variance.  It keeps
`shifted_inverse_zeta_variance_proved=False`.

### 4.89 Published additive twists of $\mu*\mu$ miss the local variance scale

[Basak--Robles--Zaharescu, arXiv:2312.17435v2](https://arxiv.org/abs/2312.17435)
prove a pointwise theorem for the exact
coefficient at the untwisted endpoint of (4.723).  Their Corollary 7.1
states that, if \((a,q)=1\) and
\(\lvert\alpha-a/q\rvert\le q^{-2}\), then

\[
 \boxed{
 \sum_{n\le X}(\mu*\mu)(n)e(n\alpha)
 \ll_\varepsilon X^{16/17+\varepsilon}
 +\left(Xq^{-1/6}+X^{7/8}q^{1/8}\right)(\log X)^3.}
\tag{4.726}
\]

Here and only in this subsection exponents are recorded relative to the
product length \(X\), rather than to \(T\).  The variance gate has
\(H=X^{1/2}\).  On the critical part of the local Fourier arc,
\(\alpha\asymp X^{-1/2}\), one may take \(q\asymp X^{1/2}\), and the
three powers in (4.726) are exactly

\[
 \frac{16}{17},\qquad
 1-\frac1{12}=\frac{11}{12},\qquad
 \frac78+\frac1{16}=\frac{15}{16}.
\tag{4.727}
\]

Thus the largest term is \(X^{16/17+\varepsilon}\).  A direct
pointwise treatment of a Fourier arc of length \(H^{-1}\), on which
the squared short-interval kernel has size at most \(H^2\), gives the
power ledger

\[
 H X^{32/17}
 =X^{1/2+32/17}
 =X^{81/34},
 \qquad
 XH=X^{3/2}=X^{51/34}.
\tag{4.728}
\]

Consequently this direct adapter misses the required variance exponent
by \(15/17\).  Equivalently, a pointwise bound used in this way would
need exponent at most \(1/2\), whereas (4.726) supplies \(16/17\), a
pointwise deficit of \(15/34\).  This is a comparison of certified
upper bounds, not a lower bound for the actual variance.

The major-arc estimate in their Lemma 6.2 does not repair the loss.
On an arc of length \(X^{-1}\) it gives
\(X\exp(-c\sqrt{\log X})\) pointwise.  After squaring and multiplying
by \(H^2=X\), its direct variance ledger is

\[
 X^{-1}\,H^2\,X^2\exp(-2c\sqrt{\log X})
 =X^2\exp(-2c\sqrt{\log X}),
\tag{4.729}
\]

which retains a positive-power deficit \(X^{1/2-o(1)}\) against
\(X^{3/2}\).  Moreover, the published result treats \(\mu*\mu\), not
the uniformly ratio-twisted family \(f_\tau\) in (4.722).

The remaining possible use of their Type I/II proof is therefore not
pointwise.  It would require a new local mean-square refinement,
uniformly for the ratio twists,

\[
 \boxed{
 \sup_{|\tau|\le(\log X)^A}
 \int_{|\alpha|\le X^{-1/2}}
 \left|\sum_{n}f_\tau(n)V_\tau(n/X)e(n\alpha)\right|^2d\alpha
 \ll_{A,V}X^{1/2}(\log X)^{1+o(1)}.}
\tag{4.730}
\]

Corollary 7.1 and the Type II Lemma 2.2 cited in its proof are
pointwise statements and do not contain (4.730).  The adapter
`basak_robles_zaharescu_mobius_convolution_audit` records the exact
three-term specialization, both variance deficits, and keeps
`brz_direct_pointwise_route_closes_variance_gate=False`.  This rejects
only direct insertion of the published theorem; a proof-level local
\(L^2\) refinement remains a separate candidate.

### 4.90 The uniform inverse-zeta variance gate would prove a new zero-free strip

The sufficient condition (4.723), and hence its Fourier form (4.730),
is substantially stronger than the original restricted four-Möbius
gate.  This can be seen without any conjectural zero-density input.
Put \(f=\mu*\mu\), choose \(\phi\) with
\(\int_{\mathbb R}\phi(u)\,du=1\), and, for fixed real \(t\), set

\[
 S_{X,t}(x):=
 \sum_n f(n)n^{-it}V(n/X)
 \phi\!\left(\frac{n-x}{H}\right),
 \qquad H=X^{1/2}.
\tag{4.731}
\]

The \(x\)-integration is exact term by term:

\[
 \int_{\mathbb R}S_{X,t}(x)\,dx
 =H\sum_n f(n)n^{-it}V(n/X).
\tag{4.732}
\]

The support in \(x\) has length \(O_V(X)\).  A finite cover by the
uniform dyadic version of (4.723), followed by Cauchy--Schwarz in
(4.732), therefore gives

\[
 \left|\sum_n f(n)n^{-it}V(n/X)\right|
 \ll H^{-1}X^{1/2}(XH)^{1/2}(\log X)^{O(1)}
 =X^{3/4}(\log X)^{O(1)}.
\tag{4.733}
\]

The same argument permits a fixed smooth factor \((n/X)^{-\sigma}\)
inside \(V\).  A smooth dyadic partition of unity then bounds the
\(X\)-block of \(\sum f(n)n^{-s}\) by
\(X^{3/4-\sigma}(\log X)^{O(1)}\), locally uniformly for fixed
\(s=\sigma+it\).  Hence the dyadic series converges normally and
defines a holomorphic continuation to \(\Re s>3/4\).  On
\(\Re s>1\) it equals its Euler product, so the identity theorem gives

\[
 \boxed{
 \sum_{n\ge1}\frac{(\mu*\mu)(n)}{n^s}
 =\frac1{\zeta(s)^2}
 \text{ holomorphic for }\Re s>\frac34,
 \quad\Longrightarrow\quad
 \zeta(s)\ne0\text{ there}.}
\tag{4.734}
\]

Thus proving the uniform single-\(\tau\) variance gate would already
prove the presently unknown zero-free half-plane
\(\Re s>3/4\).  This implication does **not** show that the original
MWKF asymptotic requires that zero-free result: (4.723) was introduced
only as a sufficient condition after Cauchy in the ratio transform.
The correct conclusion is to stop strengthening the restricted
coefficient into separate uniform \(\tau\)-bounds and instead retain
the joint ratio integral, where cancellation between ratio frequencies
is still available.  The adapter `inverse_zeta_variance_zero_free_audit`
records this logical direction and keeps
`inverse_zeta_variance_gate_available_unconditionally=False`.

### 4.91 A second Poisson step closes the BBLR all-unsigned hard box at power level

Section 4.68 used the Weil treatment in BBLR Lemma 3.1 and found the
exponent \(5/2\) in its all-unsigned \(d=1\) layer.  In the forced box

\[
 A=B=1,\qquad M_1=M_2=N_1=N_2=H=T,
\tag{4.735}
\]

the \(h\)-length has an additional exact relation to the Kloosterman
modulus.  Write \(m=m_1,n=n_1\) in BBLR equation (14), initially take
\((m,n)=1\), and let \(r=\bar m\pmod n\), \(1\le r<n\).  With the
Fourier convention of that paper, ordinary Poisson summation gives

\[
 \boxed{
 \sum_{h\in\mathbb Z}W_0(h/T)e(\mp\ell hr/n)
 =T\sum_{k\in\mathbb Z}
 \widehat W_0\!\left(T(k\pm\ell r/n)\right).}
\tag{4.736}
\]

For either consistent choice of signs, put
\(j=kn\pm\ell r\).  The map \(k\mapsto j\) is a bijection onto the
corresponding residue class modulo \(n\), and multiplication by \(m\)
removes the inverse exactly:

\[
 \boxed{
 j\equiv\pm\ell\bar m\pmod n
 \quad\Longleftrightarrow\quad
 mj\equiv\pm\ell\pmod n.}
\tag{4.737}
\]

At \(d=1\), the transform \(F\) in BBLR equation (14) has physical
\(x\)-scale one, so repeated integration by parts gives
\(F(m,n,1,\ell)\ll_B(1+|\ell|)^{-B}\).  Since \(n/T\) stays in a
fixed compact interval, the factor in (4.736) is likewise
\(O_B((1+|j|)^{-B})\).  For fixed nonzero \(j\), the congruence in
(4.737) has at most \(O((j,n))\) representatives \(m\asymp T\).
Moreover the following bound is an elementary finite divisor
reindexing:

\[
 \boxed{
 \sum_{n\asymp T}(j,n)
 \le \sum_{c\mid j}c\left(\frac{T}{c}+1\right)
 \le T\tau(|j|)+\sigma_1(|j|).}
\tag{4.738}
\]

The case \(j=0\) forces \(n\mid\ell\); because \(\ell\ne0\) in the
remainder and both transform weights are Schwartz, its total is bounded
by the same argument.  Summing (4.738) against the two Schwartz
majorants costs a constant depending only on fixed seminorms.  The
inner \((m,n,\ell,j)\)-sum is therefore \(O_W(T)\), and the outside
Poisson factor in (4.736) gives

\[
 \boxed{
 \mathcal R^{\mathrm{unsigned}}_{\pm,d=1}
 \ll_W T^2,
 \qquad
 \frac52\longrightarrow2,
 \quad\text{recovered saving }\frac12.}
\tag{4.739}
\]

The same calculation is summable over every original gcd layer.  If
\((m_1,n_1)=d\), the \(h\)-length and reduced modulus are both
\(T/d\).  The physical \(x\)-scale of \(F\) is \(d\), whence
\(F\ll_B d(1+d|\ell|)^{-B}\).  Bounded \(d\) obey (4.739) with a
uniform constant, while a dyadic layer \(d=T^\eta\), \(\eta>0\), is
arbitrarily power-negligible after choosing \(B\).  The separate
approximation term in BBLR equation (14) already has exponent two.

Thus the previously identified *all-unsigned* worst box is closed at
the positive-power level; it is not an unavoidable \(T^{1/2}\)
obstruction.  This does not yet close the signed cells with nontrivial
outer products, nor does (4.739) by itself finish the global
logarithmic little-oh bookkeeping.  The helper
`bblr_h_poisson_inverse_removal` checks (4.737) on exact residues, and
the adapter `bblr_h_poisson_unsigned_hard_box_audit` records
`all_unsigned_hard_box_power_closed=True` while keeping
`whole_signed_hard_face_covered=False`.

### 4.92 The signed hard face reduces to one outer-scale parameter

It remains to keep the two nontrivial outer factors in the BBLR
decomposition.  Let their common dyadic exponent be (s), so that
(A,B\asymp T^s), (0\le s\le1).  This loses no positive power.  Indeed,
if (F_s) denotes the corresponding component before squaring, then for
the (J=O(\log T)) nonempty dyadic scales the Hilbert-space inequality

\[
 \left\|\sum_s F_s\right\|_2^2
 \le J\sum_s\|F_s\|_2^2
\tag{4.740}
\]

reduces every asymmetric cross box to a diagonal same-(s) norm.  The
factor (J) has to be paid later in the logarithmic ledger; it cannot be
discarded at the endpoint.

Apply the first BBLR Poisson step and then the exact (h)-Poisson
transformation (4.736).  With signs fixed consistently, inverse removal
as in (4.737) gives the integer equation

\[
 \boxed{a m j-b n k=\ell}
\tag{4.741}
\]

with the complete dyadic scale table

\[
 a,b\asymp T^s,qquad
 m,n\asymp T^{1-s/2},qquad
 j,k\asymp T^{s/2},qquad
 \ell\asymp T^s.
\tag{4.742}
\]

All six variables retain smooth compactly supported weights; the
(j,k)-weights are Schwartz transforms of the original (h)-weight.
Their seminorms are uniform on a fixed dyadic cell.  Coprimality is the
one inherited from BBLR equation (14), before the same finite gcd
decomposition used in Section 4.91.  Thus the transformed two sides
(amj) and (bnk) each have exponent (1+s), while the unrestricted
solution count has exponent (1+2s).  The first Poisson normalization is
(T^{1-s}).  Consequently the transformed inner estimate must save
exactly (T^s) in the outer pair (a,b).

Now apply BBLR Proposition 3.1 to (4.741), with the transformed (a,b)
as its outer variables and (mj,nk) as its inner products.  Its sharp
range condition is met at equality because
(H'=T^s=(AB)^{1/2}).  Substitution in its two error terms gives inner
exponents

\[
 E_{AB}=\frac12+3s,qquad
 E_{\mathrm{Watt}}=\frac34+2s.
\]

After restoring (T^{1-s}), the two total errors are therefore

\[
 \boxed{
 E_1^{\rm tot}=\frac32+2s,qquad
 E_2^{\rm tot}=\frac74+s,qquad
 \min(2-E_1^{\rm tot},2-E_2^{\rm tot})=\frac14-s.}
\tag{4.743}
\]

The smooth main terms in the cited formula are at most the required
(T^{1+s}(\log T)^{O(1)}) inner scale by finite divisor reindexing, so
they introduce no positive-power deficit.  Hence the published estimate
unconditionally covers each fixed exponent cell (0\le s<1/4).  At
(s=1/4), both errors have exponent exactly two and (4.740) still costs a
logarithm; the cited theorem supplies no compensating logarithmic
little-oh.  Thus the exact current boundary is

\[
 \boxed{
 \texttt{published\_bblr\_power\_coverage\_upper}=\frac14,qquad
 \texttt{signed\_residual\_lower\_exponent}=\frac14,qquad
 s\in[1/4,1]\text{ remains}.}
\tag{4.744}
\]

This is a one-dimensional reduction of the signed hard face, not a proof
of the full mollifier asymptotic.  The adapter
`bblr_h_poisson_signed_cell_audit` records the exact rational exponent
ledger with `published_bblr_power_coverage_upper=1/4` and
`signed_residual_lower_exponent=1/4`, and deliberately sets
`boundary_logarithmic_little_o_closed=False` and
`whole_signed_hard_face_covered=False`.

### 4.93 Exact signed-atom convolution collapses only for product-compatible weights

There is one more exact cancellation hidden by the cellwise arbitrary-
coefficient treatment.  For a fixed unsigned cofactor (e), retain the
two signed atoms in (4.613) and put

\[
 \lambda_{U,e}(u):=-
 \sum_{\substack{dy=u\\d\le U<de}}\mu(d)\mu(y).
\tag{4.745}
\]

Let (j) be the unsigned dual variable created by the second
(h)-Poisson step.  If the remaining weight depends on (u,j) only
through (c=uj), finite Dirichlet convolution gives

\[
\begin{aligned}
 \sum_{uj=c}\lambda_{U,e}(u)
 &=-\sum_{dyj=c\atop d\le U<de}\mu(d)\mu(y)\\
 &=-\sum_{d\mid c\atop d\le U<de}\mu(d)
       \sum_{y\mid c/d}\mu(y)\\
 &=\boxed{-\mu(c)\mathbf 1_{c\le U<ce}}.
\end{aligned}
\tag{4.746}
\]

Thus two signed atoms and one unsigned Poisson dual collapse to one
Möbius coefficient, with the cutoff retained exactly.  No asymptotic,
sieve estimate, or extension of a finite sum is used in (4.746).  On the
top diagonal cell the two factors (u,j\asymp T^{1/2}) become one
variable (c\asymp T); at general outer exponent (s), their scales are
(T^{s/2},T^{s/2}), and (c\asymp T^s).

The cancellation is not directly applicable to the actual transform.
The factors (W(u/U_0)) and
(\widehat W(j/J_0)), as well as the (F)-kernel in BBLR equation
(14), depend separately on (u) and (j).  They are not a function of
(uj).  Mellin separation in the ratio exposes the precise deformation
of (4.746):

\[
 \sum_{yj=v}\mu(y)\left(\frac yj\right)^{i\tau}
 =v^{-i\tau}\sum_{y\mid v}\mu(y)y^{2i\tau}
 =\boxed{v^{-i\tau}\prod_{p\mid v}(1-p^{2i\tau})}.
\tag{4.747}
\]

At (	au=0), (4.747) is (mathbf1_{v=1}), recovering (4.746).
For nonzero ratio frequency it is a genuine multiplicative coefficient;
replacing the coupled ratio integral by a uniform pointwise bound would
return to the inverse-zeta variance obstruction of Section 4.90.
Therefore the remaining analytic input must retain that integral and
prove cancellation jointly in the two ratio frequencies.  In particular,

\[
 \boxed{
 \texttt{signed\_dual\_product\_collapse\_exact}=\mathrm{True},
 \qquad
 \texttt{actual\_transformed\_weight\_product\_compatible}
 =\mathrm{False}.}
\tag{4.748}
\]

The helper `truncated_signed_dual_convolution_identity` verifies
(4.746) on finite integer data.  The adapter
`signed_dual_convolution_audit` records the exact scale collapse but
records `signed_dual_product_collapse_exact=True` and
`actual_transformed_weight_product_compatible=False`, while keeping
`weighted_collapse_bound_proved=False`.  This identifies a viable
pre-Cauchy route—estimate the coupled ratio-Mellin family after the
finite collapse—but does not yet bound the residual (s\in[1/4,1]).

### 4.94 The collapsed model isolates a coupled ratio-Mellin Type-II gate

For later use, Mellin-separate a smooth (u,j)-weight in its ratio.  The
exact coefficient replacing (4.746) is

\[
 \mathcal D_{U,e,\tau}(c)
 :=-c^{-i\tau}
 \sum_{d\mid c\atop d\le U<de}\mu(d)d^{2i\tau}
 \prod_{p\mid c/d}(1-p^{2i\tau}).
\tag{4.749}
\]

This follows by inserting (u=dy, j=c/(dy)) and performing the finite
(y)-divisor sum.  In particular,
(mathcal D_{U,e,0}(c)=-\mu(c)\mathbf1_{c\le U<ce}) exactly.  Grant for
the moment that the primitive gcd allocation has been separated without
loss.  One resulting tensor has the shifted determinant model

\[
 \sum_{\substack{x,y\asymp T;\ c,d\asymp T^s\\
                  0<|\ell|\asymp T^s\\xc-yd=\ell}}
 \mu(x)\mu(y)
 \mathcal D_{U,e,\tau}(c)
 \overline{\mathcal D_{U,e',\upsilon}(d)}
 \Psi_{\tau,\upsilon}
\tag{4.750}
\]

integrated against a Schwartz function of ((\tau,\upsilon)).  The
weight (Psi_{\tau,\upsilon}) is smooth on the displayed dyadic ranges;
its seminorms grow polynomially in the two Mellin frequencies, which the
outer Schwartz transform absorbs.  The exact power ledger is

\[
 \text{raw}=1+2s,qquad
 \text{target}=1+s,qquad
 \boxed{\text{required cancellation}=s.}
\tag{4.751}
\]

Thus square-root cancellation in the two collapsed (T^s)-coefficient
variables is exactly critical, with no positive-power margin.  At the
endpoint this becomes the single explicit estimate

\[
 \boxed{
 \int_{\mathbb R^2}\Xi(\tau,\upsilon)
 \mathfrak V_{1}(\tau,\upsilon)\,d\tau d\upsilon
 \ll_{B,W}T^2(\log T)^{-B},}
\tag{4.752}
\]

uniformly in every inherited cutoff and coprimality allocation.  Here
(mathfrak V_1) denotes (4.750) at (s=1), with the nonzero-shift and
Schwartz transform retained; (4.752) is not a theorem proved below.

There is a useful but insufficient level-of-distribution observation.
Modulo (c), (4.750) has (yd\equiv-\ell\pmod c), and

\[
 \frac{\log_T c}{\log_T(yd)}=\frac{s}{1+s}\le\frac12.
\tag{4.753}
\]

Standard Bombieri--Vinogradov therefore has enough *modulus range*.
It is not an adapter for (4.750): the quotient
(x=(yd+\ell)/c) carries the second Möbius weight, and applying a
fixed-shift discrepancy estimate followed by absolute summation loses
the entire (T^s) required in (4.751).  Both the quotient Möbius weight
and the full shift average must remain inside the dispersion argument.

There is one further exactness boundary.  In the primitive BBLR layer the
condition is ((X,Y)=1) before writing (X=xu, Y=yv).  After the product
collapse this becomes a prime-allocation condition involving the hidden
divisors (u,v), not merely ((xc,yd)=1).  Consequently (4.750) is the
minimal collapsed model, but it is not yet an exact four-variable rewrite
of every gcd layer.  A successful proof must first expand those prime
allocations and prove (4.752) uniformly for the resulting finitely
divisor-weighted family.  The audit therefore records
`quotient_mobius_prevents_direct_bv=True`,
`coprimality_prime_allocation_required=True`,
`four_variable_reduction_exact=False`, and
`coupled_ratio_mellin_type_ii_bound_proved=False`.

### 4.95 Four cross-coprimality allocations make the collapsed superposition exact

The exactness defect at the end of Section 4.94 is algebraic and can be
removed.  For (X=xu) and (Y=yv),

\[
 \boxed{
 (xu,yv)=1
 \Longleftrightarrow
 (x,y)=(x,v)=(u,y)=(u,v)=1.}
\tag{4.754}
\]

Apply the finite identity
(mathbf1_{(a,b)=1}=\sum_{r\mid a,,r\mid b}\mu(r)) to the four
cross pairs.  This gives

\[
 \mathbf1_{(xu,yv)=1}
 =\sum_{\substack{r_0\mid x,y\\r_1\mid x,v\\
                   r_2\mid u,y\\r_3\mid u,v}}
   \mu(r_0)\mu(r_1)\mu(r_2)\mu(r_3).
\tag{4.755}
\]

There is no compatibility assumption among the (r_i); if a prime
occurs in several cross gcds, the product of the four finite Möbius sums
still equals the indicator in (4.754).  For fixed
((r_0,r_1,r_2,r_3)), the restrictions separate exactly:

\[
 \operatorname{lcm}(r_0,r_1)\mid x,quad
 \operatorname{lcm}(r_0,r_2)\mid y,quad
 \operatorname{lcm}(r_2,r_3)\mid u,quad
 \operatorname{lcm}(r_1,r_3)\mid v.
\tag{4.756}
\]

Consequently the (u,jmapsto c) and (v,kmapsto d) convolutions in
(4.749) may be performed independently after the allocation is fixed.
The resulting collapsed (c,d) coefficients depend on the allocation
divisors and Mellin frequencies, but not on the long variables (x,y).
Thus (4.750), summed over the four allocation divisors and integrated in
the two ratio frequencies, is an exact finite superposition for the
primitive gcd layer.  The nonprimitive BBLR layers have the same
identity after extracting their common divisor.

Each (r_i) divides two already localized variables.  Absolute divisor
reindexing therefore has power exponent zero; the audit reserves the
conservative factor ((\log T)^4), to be absorbed by choosing the (B)
in (4.752) four units larger.  The exact status is

\[
 \boxed{
 \texttt{four\_variable\_superposition\_exact}=\mathrm{True},
 \qquad
 \texttt{collapsed\_coefficients\_independent\_of\_long\_variables}
 =\mathrm{True}.}
\tag{4.757}
\]

This closes the coprimality/reindexing gap, not the analytic Type-II
estimate.  Even with separated coefficient sequences, a standard
Bombieri--Vinogradov discrepancy does not retain both the Möbius weight
on (x=(yd+\ell)/c) and the signed full (ell)-average.  The remaining
new theorem is now precisely the allocation-uniform coupled estimate
(4.752).  The helper `collapsed_cross_coprimality_identity` checks
(4.754)--(4.755) on finite data, while
`collapsed_coprimality_allocation_audit` keeps
`four_variable_superposition_exact=True` and
`collapsed_coefficients_independent_of_long_variables=True`, but keeps
`standard_bombieri_vinogradov_adapter_applies=False` and
`coupled_ratio_mellin_type_ii_bound_proved=False`.

### 4.96 The equal-product face contains an ordinary two-point Chowla correlation

There is a further boundary on how (4.752) may be estimated.  Write

\[
 c=uj,\qquad d=vk.
\]

On the equal-product face, for every fixed nonzero integer \(\kappa\),
the determinant equation has the exact specialization

\[
 \boxed{
 c=d,\quad \ell=\kappa c
 \quad\Longrightarrow\quad
 xc-yd=\ell\ \Longleftrightarrow\ x-y=\kappa.}
\tag{4.758}
\]

The primitive BBLR condition does not remove this face.  For example,

\[
 (u,v,j,k,x,y)=(5,7,7,5,12,11)
\]

gives \(c=uj=vk=d=35\), \(xc-yd=35\), and

\[
 \boxed{(xu,yv)=(60,77)=1.}
\tag{4.759}
\]

Now take the identity-allocation tensor
\(r_0=r_1=r_2=r_3=1\) in (4.755) and specialize its *pointwise*
ratio family to \(\tau=\upsilon=0\).  This tensor has no additional
divisibility restriction, and equation (4.749) gives
\(\mathcal D_{U,e,0}(c)=-\mu(c)\mathbf 1_{c\le U<ce}\)
exactly.  Hence, whenever the two cutoff indicators overlap, the
equal-product, \(\ell=\kappa c\) part of that pointwise tensor is

\[
 \boxed{
 \sum_{c\asymp T^s}\mu(c)^2
   \mathbf 1_{c\le U<ce}\mathbf 1_{c\le U'<ce'}
 \sum_{x-y=\kappa\atop x,y\asymp T}
   \mu(x)\mu(y)\Psi_{0,0}(x,y,c,c,\kappa c).}
\tag{4.760}
\]

This is an ordinary two-point Möbius correlation in the long variable.
Its raw exponent is \(1+s\), exactly the required inner exponent in
(4.751).  Thus there is no remaining positive-power deficit on this
face, but the global little-oh requires cancellation beyond the trivial
\(T^{1+s}\) bound.  A theorem uniform for arbitrary separated smooth
weights in (4.760), imposed separately on every allocation tensor,
would in particular require the ordinary Cesàro two-point Chowla
estimate, which is not currently known.

This observation does **not** disprove the actual gate (4.752): a single
point \((\tau,\upsilon)=(0,0)\) has measure zero, and the inherited
weight is reconstructed only after the two ratio frequencies are
integrated jointly.  It does rule out taking absolute values separately
in those frequencies and asking for a uniform pointwise bound.  The
correct remaining route must retain the joint ratio integral and its
cancellation:

\[
 \boxed{
 \texttt{equal_collapsed_product_face_present}=\mathrm{True},\qquad
 \texttt{uniform_ratio_frequency_triangle_gate_admissible}
 =\mathrm{False}.}
\tag{4.761}
\]

The helper `collapsed_equal_product_chowla_identity` verifies
(4.758)--(4.759) on exact integer data.  The adapter
`collapsed_chowla_face_audit` records the exponent equality, the
ordinary-Chowla boundary, and keeps the jointly integrated Type-II gate
open rather than replacing it by the stronger pointwise statement.  In
particular it records `equal_collapsed_product_face_present=True` and
`uniform_ratio_frequency_triangle_gate_admissible=False`.

### 4.97 Physical ratio recombination does not annihilate the primitive equal face

The measure-zero caveat after (4.760) leaves open whether performing the
two ratio integrals first might kill the equal-product face algebraically.
It does not.  For a physical one-side weight \(\Phi\), Mellin inversion
returns the finite coefficient

\[
 \boxed{
 A_{U,e,\Phi}(c)
 =\sum_{uj=c}\lambda_{U,e}(u)\Phi(u,j)
 =-\sum_{dyj=c\atop d\le U<de}
   \mu(d)\mu(y)\Phi(dy,j).}
\tag{4.762}
\]

Before separating the four cross-coprimalities, the coefficient on the
primitive equal face \(c=d\) is therefore

\[
 \boxed{
 \begin{aligned}
 B_{U,e,e';\Phi,\Phi'}(c;x,y)
 :=\sum_{u\mid c}\sum_{v\mid c\atop
       (u,v)=(u,y)=(v,x)=1}
 &\lambda_{U,e}(u)\lambda_{U,e'}(v)\\
 &\times\Phi(u,c/u)\overline{\Phi'(v,c/v)}.
 \end{aligned}}
\tag{4.763}
\]

Here \((x,y)=1\) already follows when \(x-y=1\).  Formula (4.763) is
the direct physical recombination of the allocation tensors, so it does
not take absolute values in the ratio frequencies.

There is no universal zero in (4.763).  Take

\[
 U=5,\qquad e=e'=10,\qquad c=35,\qquad (x,y)=(12,11),
\]

and retain the balanced factor pairs \(u,v\in\{5,7\}\).  Directly from
(4.745),

\[
 \lambda_{5,10}(5)=2,\qquad \lambda_{5,10}(7)=1.
\]

The two surviving primitive pairs are \((u,v)=(5,7),(7,5)\); all three
cross gcds in (4.763) are one.  With the physical weights equal to one
on these pairs,

\[
 \boxed{B_{5,10,10}(35;12,11)=2\cdot1+1\cdot2=4.}
\tag{4.764}
\]

This finite witness proves only a structural statement: joint Mellin
inversion and primitive gcd recombination do not by themselves annihilate
the Chowla face.  It does not isolate a uniformly smooth asymptotic box
and is not a lower bound for the original remainder.  Combined with
(4.760), however, it forbids two common enlargements of the sufficient
gate: estimating allocation tensors by a triangle inequality, or replacing
the exact inherited physical kernel by an arbitrary smooth tensor class.
Any viable dispersion estimate must keep the complete outer-scale sum and
the specific kernel coefficients together:

\[
 \boxed{
 \texttt{primitive_equal_face_coefficient_can_be_nonzero}=\mathrm{True},
 \qquad
 \texttt{arbitrary_smooth_weight_enlargement_admissible}=\mathrm{False}.}
\tag{4.765}
\]

The helper `primitive_equal_face_divisor_coefficient` evaluates (4.763)
as a finite integer sum and verifies (4.764).  The adapter
`physical_joint_ratio_recombination_audit` keeps the centered coupled
dispersion estimate and the whole signed hard face explicitly unproved;
it records `primitive_equal_face_coefficient_can_be_nonzero=True` and
`arbitrary_smooth_weight_enlargement_admissible=False`.

### 4.98 Gcd layers expose the centered coupled-dispersion scale

The equal-product face cannot be estimated separately, but extracting the
common divisor still gives an exact scale decomposition without taking an
absolute value.  Put

\[
 C=T^s,\qquad G=T^\gamma,\qquad A=\frac CG=T^{s-\gamma},
 \qquad 0\leq\gamma\leq s,
\]

and on one dyadic gcd layer write

\[
 \boxed{
 c=ga,\qquad d=gb,\qquad \ell=gh,\qquad
 g\asymp G,\quad a,b,|h|\asymp A,\quad(a,b)=1.}
\tag{4.766}
\]

The equation \(xc-yd=\ell\) is then exactly \(ax-by=h\).  For fixed
\((a,b,h)\), all solutions are
\(x=x_0+bt,\ y=y_0+at\), so the localized \(t\)-interval has length
\(O(T/A+1)\).  In the power-critical range \(A\leq T\), the complete
dyadic layer therefore has raw cardinality

\[
 G\cdot A^2\cdot A\cdot\frac TA
 =TGA^2=\frac{TC^2}{G},
 \qquad
 E_{\rm raw}=1+2s-\gamma.
\tag{4.767}
\]

This count retains the entire \(g\)-sum.  It is not a sum of separate
fixed-\(g\) majorants.

There is also an exact centered Fourier form, but the allocation tensors
must first be recombined.  Expand the new primitive condition with
\(\mathbf1_{(a,b)=1}=\sum_{\rho\mid a,b}\mu(\rho)\).  Let
\(\eta=(r_0,r_1,r_2,r_3,\rho,\tau,\upsilon)\) collect the four allocations
from (4.755), this fifth primitive-slope allocation, and the two ratio
frequencies.  Write \(d\nu(\eta)\) for the resulting finite signed divisor
sum times the two inherited Schwartz Mellin densities.  For fixed \(\eta\),
let \(p_{g,\eta}(a,x)\) and \(q_{g,\eta}(b,y)\) be the now-separated exact
cutoff, Möbius, divisibility, and physical-kernel coefficients.  Define

\[
 F_{g,\eta}(\alpha)
   =\sum_{a,x}p_{g,\eta}(a,x)e(\alpha ax),\qquad
 G_{g,\eta}(\alpha)
   =\sum_{b,y}q_{g,\eta}(b,y)e(\alpha by),
\]

Let \(w_\eta\in C_c^\infty(\mathbb R\setminus\{0\})\) be the exact
nonzero-shift weight in this tensor.  Its seminorms are controlled by the
same Schwartz density already present in \(d\nu(\eta)\).  Recombine before
taking an absolute value:

\[
 \mathcal H_{C,G}(\alpha)
 :=\int d\nu(\eta)\,\widehat w_\eta(A\alpha)
   \sum_{g\asymp G}
   F_{g,\eta}(\alpha)\overline{G_{g,\eta}(\alpha)}.
\]

With \(\widehat w_\eta(\xi)=\int w_\eta(u)e(-u\xi)\,du\), ordinary
Fourier inversion gives the identity

\[
 \boxed{
 \mathfrak V_{C,G}
 =A\int_{\mathbb R}\mathcal H_{C,G}(\alpha)\,d\alpha.}
\tag{4.768}
\]

No arbitrary-coefficient enlargement is made in (4.768).  All outer-scale
and ratio-Mellin integrations, all five coprimality allocations, and the
complete \(g\)-sum remain inside \(\mathcal H_{C,G}\).

For every \(\eta\), the shift weight vanishes in a neighbourhood of zero,
and hence

\[
 \boxed{
 A\int_{\mathbb R}\widehat w_\eta(A\alpha)\,d\alpha
 =w_\eta(0)=0.}
\tag{4.769}
\]

Thus the product diagonal \(ax=by\), equivalently the constant Fourier
mode in (4.768), is annihilated exactly.  This is the useful centering:
the remaining theorem is an off-diagonal local \(L^2\) estimate, not a
positive Gram bound containing its identity diagonal.

The global inner target is \(TC=T^{1+s}\).  Hence the exact uniform local
gate on this gcd layer is

\[
 \boxed{
 \left|
 \int_{\mathbb R}\mathcal H_{C,G}(\alpha)\,d\alpha
 \right|
 \ll_{B,W}TG(\log T)^{-B}.}
\tag{4.770}
\]

After multiplication by the outside \(A=C/G\), (4.770) gives
\(TC(\log T)^{-B}\).  Comparing (4.767) with this target shows that the
required saving is exactly

\[
 (1+2s-\gamma)-(1+s)=s-\gamma=\log_T A.
\]

At the top layer \(\gamma=s\), this power requirement becomes zero, but
the logarithmic little-oh still contains the fixed-affine Chowla subface
from Section 4.96.  It must remain inside the complete \(g\)- and physical-
kernel sum.  The averaged Chowla theorem of Matomäki--Radziwiłł--Tao treats
translations of bounded multiplicative functions after averaging the
shifts; it does not state (4.770) for the coupled divisor coefficients,
varying primitive slopes, and retained \(g\)-kernel.  No adapter is claimed.

The helper `collapsed_gcd_layer_parameterization` verifies (4.766) and
the determinant equivalence on integers.  The `Fraction`-valued adapter
`collapsed_gcd_layer_centered_kernel_audit` records (4.767)--(4.770), with
`required_saving_exponent=s-gamma` and
`fixed_affine_chowla_must_remain_inside_g_sum=True` at the top layer.  It
keeps `published_averaged_chowla_adapter_applies=False`,
`centered_coupled_dispersion_bound_proved=False`, and
`whole_signed_hard_face_covered=False`.

### 4.99 Primitive refactorization closes the top equal-product face

The warning in Section 4.97 is local in the collapsed product \(c\).  The
complete primitive sum over its hidden factors has an additional
unconditional cancellation.  On \(c=d\), (4.763) contains

\[
 (u,v)=1,\qquad uj=vk.
\]

Euclid's lemma gives the exact bijection

\[
 \boxed{
 (u,v)=1,\ uj=vk
 \quad\Longleftrightarrow\quad
 j=vq,\ k=uq\quad(q\in\mathbb N),
 \qquad c=uvq.}
\tag{4.771}
\]

At the top balanced cell, the exact half cutoff (4.505) and the scale
table in Sections 4.92--4.93 give
\(u,v,j,k,U,e,e'\asymp Z=T^{1/2}\).  Hence (4.771) restricts \(q\) to
a fixed finite set depending only on the dyadic support constants.

The signed coefficient itself has a useful exact form.  Put \(D=U/e\).
The inequalities in (4.745) are equivalent to \(D<d\leq U\), and
therefore

\[
 \boxed{
 \lambda_{U,e}
 =-\big(\mu\mathbf1_{D<\cdot\leq U}\big)*\mu
 =-(\mu*\mu)
   +(\mu\mathbf1_{\cdot\leq D})*\mu
   +(\mu\mathbf1_{\cdot>U})*\mu.}
\tag{4.772}
\]

This is a coefficientwise finite identity.  On the balanced cell,
\(D=O(1)\), \(U\asymp Z\), and the last convolution in (4.772), when
localized to \(n\asymp Z\), has a bounded complementary factor.

For completeness, the standard prime-number-theorem input needed here
can be stated uniformly.  Let \(V\) range over a fixed bounded family in
\(C_c^\infty((0,\infty))\), let \(U/Z\) and \(e/Z\) stay in fixed compact
subsets of \((0,\infty)\), and let \(r\leq T^{O(1)}\).  For every \(B>0\),

\[
 \boxed{
 \sum_{(n,r)=1}\lambda_{U,e}(n)V(n/Z)
 \ll_{B,V}Z(\log Z)^{-B}\mathcal E_{C_B}(r),
 \qquad
 \mathcal E_K(r):=\prod_{p\mid r}\left(1+\frac Kp\right).}
\tag{4.773}
\]

Indeed, for the first term on the right of (4.772), the Dirichlet series
after removing primes dividing \(r\) is exactly

\[
 \frac1{\zeta(s)^2}\prod_{p\mid r}(1-p^{-s})^{-2}.
\]

The classical zero-free region and a smooth Perron shift give arbitrary
logarithmic saving.  The second term in (4.772) is a bounded sum of
similarly restricted Möbius sums because \(D=O(1)\).  In the third term,
write \(n=dm\); the support \(n\asymp Z\) and \(d>U\asymp Z\) leave only
boundedly many \(m\), and the same restricted Möbius estimate applies to
the \(d\)-sum.  Finally
\(\mathcal E_K(r)\ll_K(\log\log(3r))^K\), so all removed Euler factors
are absorbed by increasing \(B\).  This proves (4.773) without a
zero-density or Chowla hypothesis.

Substitute (4.771) into the physical coefficient before separating the
long variables.  Uniformly for fixed \(e,e'\), the inherited support
constants, and \(x,y\asymp T\), set

\[
 \begin{aligned}
 \mathfrak E_{x,y}:={}&
 \sum_{q\asymp1}
 \sum_{\substack{u,v\asymp Z\\
       (u,v)=(u,y)=(v,x)=1}}
 \lambda_{U,e}(u)\lambda_{U,e'}(v)\\
 &\hspace{35mm}\times
 \Phi_{x,y,q}(u,vq)\overline{\Phi'_{x,y,q}(v,uq)}.
 \end{aligned}
\]

For fixed \(v\), apply (4.773) to the \(u\)-sum with coprimality modulus
\(r=vy\); the physical weights have the required uniform derivatives.
Then sum \(v\) absolutely, using
\(|\lambda_{U,e'}(v)|\leq\tau_2(v)\).  Since the \(q\)-set is finite,

\[
 \boxed{\mathfrak E_{x,y}\ll_{B,W}Z^2(\log T)^{-B}.}
\tag{4.774}
\]

The remaining fixed-affine long-variable sum now needs no Möbius
correlation theorem.  Bound it by its cardinality \(O(T)\).  As
\(Z^2=T\), (4.774) gives

\[
 \boxed{
 \sum_{x-y=\kappa\atop x,y\asymp T}
   \mu(x)\mu(y)\mathfrak E_{x,y}
 \ll_{B,W}T Z^2(\log T)^{-B}
 =T^2(\log T)^{-B}.}
\tag{4.775}
\]

This proves the required logarithmic little-oh on the top primitive
equal-product face.  It does not contradict the finite coefficient \(4\)
in (4.764): individual \(c\)-fibres need not vanish; the cancellation is
the complete outer \((u,v,q)\)-average which Section 4.97 required us to
retain.  It also does not cover the intermediate gcd layers
\(0<s-\gamma<1\) in (4.770).

The helpers `primitive_equal_product_factorization` and
`truncated_signed_atom_interval_convolution` verify (4.771)--(4.772) on
integers.  The adapter `top_equal_product_outer_pnt_audit` records the
zero power margin, the arbitrary logarithmic PNT saving, and
`top_equal_product_face_closed_unconditionally=True`, while retaining
`whole_signed_hard_face_covered=False`.

### 4.100 The same outer PNT closes every fixed polylog gcd collar

The preceding argument is not confined to \(a=b=1\).  Return to the
primitive gcd layer (4.766), and retain the hidden factorizations

\[
 ga=uj,\qquad gb=vk,qquad (a,b)=(u,v)=1.
\]

They imply \(buj=avk\).  Put

\[
 d_1=(a,u),\qquad d_2=(b,v),\qquad
 \Delta=(bu,av).
\]

The two primitive conditions imply prime by prime that
\(\Delta=d_1d_2\).  Reducing the two sides by \(\Delta\) and applying
Euclid's lemma gives the exact parameterization

\[
 \boxed{
 \begin{aligned}
 \Delta&=(bu,av)=(a,u)(b,v)=d_1d_2,\\
 j&=\frac{av}{\Delta}q,\qquad
 k=\frac{bu}{\Delta}q,\qquad
 g=\frac{uv}{\Delta}q,qquad q\in\mathbb N.
 \end{aligned}}
\tag{4.776}
\]

Conversely, (4.776) reconstructs \(uj=ga\) and \(vk=gb\) exactly.
Writing

\[
 a=d_1a_0,\quad u=d_1u_0,\quad
 b=d_2b_0,\quad v=d_2v_0
\]

turns (4.776) into

\[
 \boxed{
 j=a_0v_0q,\qquad k=b_0u_0q,qquad g=u_0v_0q.}
\tag{4.777}
\]

The exact gcd conditions are

\[
 \begin{gathered}
 (a_0,u_0)=(b_0,v_0)=1,\\
 (d_1,d_2)=(d_1,b_0)=(a_0,d_2)=(a_0,b_0)=1,\\
 (d_1,v_0)=(u_0,d_2)=(u_0,v_0)=1.
 \end{gathered}
\]

They are restrictions, not discarded density factors.

Let \(Z=C^{1/2}\), and write \(q\asymp Q\).  Since
\(a,b,h\asymp A=C/G\), \(u,v,j,k\asymp Z\), and \(g\asymp G\),
(4.777) forces the complete scale table

\[
 \boxed{
 d_1d_2=\Delta\asymp AQ,\quad 1\leq Q\ll A,\quad
 a_0\asymp\frac A{d_1},\quad b_0\asymp\frac A{d_2},\quad
 u_0\asymp\frac Z{d_1},\quad v_0\asymp\frac Z{d_2}.}
\tag{4.778}
\]

At the constant endpoint, \(Q\) ranges over a nonempty fixed compact
integer set; no growing lower bound is imposed.

The PNT estimate (4.773) is stable under the divisibilities in (4.777).
For a prescribed \(d_0\leq(\log T)^K\), deleting or forcing its finitely
many local prime powers changes the Dirichlet series of \(\mu*\mu\) by a
finite Euler polynomial.  The same zero-free-region argument therefore
gives, for every \(B\),

\[
 \boxed{
 \sum_{\substack{d_0\mid n\\(n,r)=1}}
   \lambda_{U,e}(n)V(n/Z)
 \ll_{B,K,V}Z(\log Z)^{-B}
   \tau(d_0)^{C_B}\mathcal E_{C_B}(r).}
\tag{4.779}
\]

For \(s<1\), this is even more direct.  Under the exact half cutoff,
\(U=T^{1/2}\), while \(u\asymp Z=T^{s/2}\) and the unsigned cofactor
has size \(e\asymp T^{1-s/2}\).  Thus every divisor of \(u\) satisfies
\(d\leq U<de\), and \(\lambda_{U,e}(u)=-(\mu*\mu)(u)\) throughout a
fixed strict exponent cell.  At \(s=1\), the two bounded-factor tails in
(4.772) give (4.779).

Now suppose

\[
 1\leq A=\frac CG\leq(\log T)^K
\]

for a fixed \(K\).  All variables \(a,b,h,d_1,d_2,q\) and every gcd
allocation introduced by (4.776)--(4.778) have polylogarithmic total
variation.  Fix them and the long variables, apply (4.779) to one signed
atom, and sum the other signed atom absolutely with its divisor bound.
For fixed \((a,b,h)\), the affine equation \(ax-by=h\) has
\(O(T/A+1)\) localized solutions.  Consequently all slope, shift,
allocation, and long-variable sums cost only \(T(\log T)^{O_K(1)}\) on
top of the natural outer volume \(Z^2=C\).  Choosing the \(B\) in
(4.779) after these explicit polylogarithmic losses yields

\[
 \boxed{
 \mathfrak V_{C,G}\ll_{B,K,W}TC(\log T)^{-B},
 \qquad 1\leq C/G\leq(\log T)^K.}
\tag{4.780}
\]

Thus every fixed polylogarithmic neighbourhood of the top gcd face is
unconditionally closed.  The residual centered-dispersion problem can be
restricted to \(A>(\log T)^K\) for every fixed \(K\).  This still leaves
every strict positive exponent cell \(A=T^{s-\gamma}\),
\(s-\gamma>0\); (4.780) is not a positive-power Type-II theorem.

The helper `primitive_unequal_product_factorization` verifies
(4.776)--(4.777), including a witness with nontrivial cross gcds
\((d_1,d_2)=(2,7)\).  The adapter
`polylog_gcd_collar_outer_pnt_audit` records
`polylog_gcd_collar_closed_unconditionally=True` and deliberately keeps
`strict_positive_power_gcd_layers_covered=False` and
`whole_signed_hard_face_covered=False`.

### 4.101 The strict-power residual is one exact three-block Type-II gate

It remains to state the positive-power core after (4.776) without
enlarging any coefficient class.  Write

\[
 C=T^s,\qquad A=T^\delta=\frac CG,\qquad
 G=T^\gamma,\qquad q=T^\theta,\qquad d_i=T^{r_i}.
\]

The exact relations \(C=AG\) and \(d_1d_2\asymp Aq\) give

\[
 \boxed{
 \gamma=s-\delta,\qquad r_1+r_2=\delta+\theta,
 \qquad
 0\leq\theta\leq\min(\delta,\gamma),
 \qquad
 0\leq r_i\leq\min(\delta,s/2).}
\tag{4.781}
\]

The reduced variables in (4.777) have the complete scale table

\[
 \boxed{
 \begin{array}{c|ccccc}
 \text{variable}&a_0&b_0&u_0&v_0&q\\ \hline
 \log_T(\text{length})
 &\delta-r_1&\delta-r_2&s/2-r_1&s/2-r_2&\theta.
 \end{array}}
\tag{4.782}
\]

All entries in (4.782) are nonnegative precisely on the polytope
(4.781).  The reconstruction identities are

\[
 \begin{aligned}
 a&=d_1a_0,& b&=d_2b_0,&
 u&=d_1u_0,& v&=d_2v_0,\\
 j&=a_0v_0q,& k&=b_0u_0q,&
 g&=u_0v_0q,& d_1d_2&\asymp Aq.
 \end{aligned}
\]

For one dyadic cell, let \(d\nu(\eta)\) retain the four original
cross-coprimality allocations, the primitive allocations, both ratio
integrals, and the exact physical kernel.  The strict-power residual is
the following single three-block sum:

\[
 \boxed{
 \begin{aligned}
 \mathfrak C_{s,\delta,\theta,r_1}[\Psi]
 :=\int d\nu(\eta)
 \sum_{\substack{
 d_1,d_2,a_0,b_0,u_0,v_0,q,h,x,y\\
 d_1a_0x-d_2b_0y=h}}
 &\lambda_{U,e}(d_1u_0)
 \overline{\lambda_{U,e'}(d_2v_0)}\\[-2mm]
 &\times\mu(x)\mu(y)\,\Psi_\eta,
 \end{aligned}}
\tag{4.783}
\]

where every variable has the range in (4.781)--(4.782),
\(h\asymp T^\delta\), \(x,y\asymp T\), and all gcd conditions displayed
after (4.777) are imposed.  The nonzero-shift centering from (4.768)--
(4.769) is part of \(\Psi_\eta\); no positive identity diagonal is added.

There are exactly three dynamic blocks in (4.783):

\[
 \begin{array}{c|c|c}
 \text{block}&\text{variables}&\text{total exponent}\\ \hline
 \text{signed--gcd}&(d_1,u_0;d_2,v_0)&
   (\delta+\theta)+(\gamma-\theta)=s\\
 \text{reduced unsigned}&(a_0,b_0,q)&
   (\delta-r_1)+(\delta-r_2)+\theta=\delta\\
 \text{long determinant}&(x,y,h;\ d_1a_0x-d_2b_0y=h)&1.
 \end{array}
\]

Consequently

\[
 \boxed{
 E_{\rm raw}=1+s+\delta,\qquad
 E_{\rm target}=1+s,\qquad
 E_{\rm raw}-E_{\rm target}
 =\delta
 =E_{(a_0,b_0,q)}.}
\tag{4.784}
\]

Thus the whole positive-power task on this route is the one local
inequality

\[
 \boxed{
 \mathfrak C_{s,\delta,\theta,r_1}[\Psi]
 \ll_{B,W}T^{1+s}(\log T)^{-B}}
\tag{4.785}
\]

uniformly on the rational polytope (4.781), after excluding the already
proved polylog collar.  Formula (4.785) must save the complete reduced
unsigned block by coupling it to both Möbius-bearing blocks; estimating
that block by cardinality leaves exactly \(T^\delta\).

Neither direct role assignment in BBLR Proposition 3.1 is legal.  If
\(\mu(x),\mu(y)\) occupy its two arbitrary outer-coefficient slots, then
the two \(\lambda(d_i u_i)\) sequences remain arithmetic weights in inner
slots; reversing the assignment leaves the two long Möbius weights there.
There is, however, a legal *convolved* assignment, described in Section
4.102 below.  Its hypotheses hold, but its two published error terms both
miss the target by a positive power.  Thus the obstruction is an exponent
failure after the necessary convolution, not an absolute absence of a
BBLR adapter.

The adapter `strict_power_gcd_core_audit` implements (4.781)--(4.784)
with `Fraction` and records
`unsigned_reduced_block_exponent=delta`,
`bblr_arbitrary_outer_coefficient_adapter_applies=True`, and
`centered_three_block_type_ii_proved=False`.  Hence (4.785), not the
fixed-shift Chowla face, is now the unique strict-power local theorem
left by the collapsed route.

### 4.102 Convolution makes BBLR legal, but Cauchy recreates the raw-scale grouped diagonal

Fix the variables \(u_0,v_0,q\), the finite coprimality allocations, and
the ratio-Mellin parameters.  On the left define the exact dyadic
coefficient

\[
 \alpha_{u_0}(r)
 :=\sum_{d_1x=r}
   \lambda_{U,e}(d_1u_0)\mu(x)\Phi_{u_0}(d_1,x),
 \qquad
 \beta_{v_0}(t)
 :=\sum_{d_2y=t}
   \overline{\lambda_{U,e'}(d_2v_0)}\mu(y)
   \Phi'_{v_0}(d_2,y).
\tag{4.786}
\]

The Mellin variables already retained in \(d\nu(\eta)\) separate every
remaining product cutoff.  Hence (4.786) is an identity, not an arbitrary
coefficient enlargement.  Divisor bounds give
\(|\alpha_{u_0}(r)|+|\beta_{v_0}(t)|\ll\tau_K(rt)\) for a fixed \(K\).
The determinant in (4.783) becomes

\[
 \boxed{ra_0-tb_0=h.}
\tag{4.787}
\]

Put \(r_*=\max(r_1,r_2)\).  The complete exponent table for this
assignment is

\[
 \boxed{
 \begin{array}{c|ccccc}
 \text{variable}&r&t&a_0&b_0&h\\ \hline
 \log_T(\text{length})
 &1+r_1&1+r_2&\delta-r_1&\delta-r_2&\delta.
 \end{array}}
\tag{4.788}
\]

Both products \(ra_0,tb_0\) have exponent \(1+\delta\).  The variables
\((u_0,v_0,q)\) left outside (4.787) have total exponent

\[
 (s/2-r_1)+(s/2-r_2)+\theta=s-\delta=\gamma.
\]

Thus BBLR Proposition 3.1 now accepts (4.787): the two convolved sequences
are its arbitrary outer coefficients, and \(a_0,b_0\) are its smooth inner
variables (with a dummy factor of length one on each side).  Literal
substitution gives the two inner error exponents

\[
 \boxed{
 E_{\rm AB}=\frac52+2\delta+\theta,
 \qquad
 E_{\rm Watt}=\frac54+\frac32\delta+\frac12r_* .}
\tag{4.789}
\]

The inner target is \(1+\delta\), so the respective deficits are

\[
 \boxed{
 E_{\rm AB}-(1+\delta)=\frac32+\delta+\theta,
 \qquad
 E_{\rm Watt}-(1+\delta)=
 \frac14+\frac12\delta+\frac12r_* .}
\tag{4.790}
\]

In particular the legal BBLR convolution route covers no strict-power
cell.

One can instead Poisson-sum \(a_0\) modulo \(t\).  With
\(M_0=T^{\delta-r_1}\), ordinary Poisson summation gives, for the exact
smooth two-variable weight \(\mathcal W\),

\[
 \sum_{a_0\equiv h\bar r\ (\bmod t)}\mathcal W(a_0)
 =\frac{M_0}{t}\sum_{k\in\mathbb Z}
 e\!\left(\frac{kh\bar r}{t}\right)
 \widehat{\mathcal W}_{r,t,h}\!\left(\frac{kM_0}{t}\right).
\tag{4.791}
\]

The nonzero dual length is
\(k=T^{1+\theta}\), the combined numerator \(c=kh\) has exponent
\(1+\delta+\theta\), and the Poisson normalization is
\(T^{-1-\theta}\).  Combining \((k,h)\) into one divisor-bounded
coefficient makes Bettin--Chandee Theorem 1 applicable.  After also
restoring the outside exponent \(\gamma\), its two total exponents are

\[
 \boxed{
 \begin{aligned}
 E_{\rm BC,1}
 &=\frac95+s+\frac7{10}(\delta+\theta)+\frac14r_*,\\
 E_{\rm BC,2}
 &=\frac{15}{8}+s+\frac78(\delta+\theta)+\frac18r_*.
 \end{aligned}}
\tag{4.792}
\]

Relative to \(1+s\), their deficits are respectively

\[
 \boxed{
 \frac45+\frac7{10}(\delta+\theta)+\frac14r_*,
 \qquad
 \frac78+\frac78(\delta+\theta)+\frac18r_* .}
\tag{4.793}
\]

Thus the one-Poisson Bettin--Chandee route also covers no cell.

Finally, (4.769) removes the *cross* frequency diagonal in the original
bilinear form.  It does not remove the positive self-diagonal created
after applying Cauchy to either factor.  Restoring the outside factor
\(A=T^\delta\) from Fourier inversion, identical tuples in the two
short-arc norms have exponent

\[
 \boxed{
 E_{\rm tuple}=1+\frac{s+3\delta+\theta}{2}.}
\tag{4.794}
\]

This is not the full Cauchy diagonal.  The variables \(u_0,v_0\) do not
enter the additive frequencies \(d_1a_0x,d_2b_0y\).  They therefore
square coherently inside the grouped Fourier coefficients.  Bounding
those fibres by their complete lengths adds a total exponent
\((\gamma-\theta)/2\) beyond (4.794) and gives

\[
 \boxed{
 E_{\rm grouped}=1+s+\delta=E_{\rm raw},
 \qquad E_{\rm grouped}-(1+s)=\delta.}
\tag{4.794a}
\]

PNT cancellation in one invisible signed fibre can add logarithmic
decay, but it cannot supply the missing positive power \(T^\delta\).
Thus Cauchy returns the complete original deficit on every strict-power
cell.  At the top vertex
\((s,\delta,\theta,r_1,r_2)=(1,1,0,1/2,1/2)\), one has
\(u_0=v_0=q=1\) and \(\lambda=-(\mu*\mu)\).  If the ratio weight is
temporarily made product-compatible, the complete side convolution is

\[
 (\mu*\mu)*\mathbf1*\mu=\mu*\mu,
\tag{4.795}
\]

because \(\mathbf1*\mu\) is the convolution identity.  Hence this
vertex is exactly the inverse-zeta-square short-window variance at
ambient scale \(X=T^2\) and window \(H=T\) from Section 4.87.  The actual
ratio kernel deforms (4.795) and must remain jointly integrated; it does
not remove the positive grouped Cauchy diagonal.  Therefore a valid
continuation must estimate the centered cross spectral form before taking a positive
square.  The adapter `strict_power_convolution_kloosterman_audit` records
(4.786)--(4.795), with both published routes false and
`near_frequency_type_ii_proved=False`.

### 4.103 The inherited ratio-Mellin kernel has zero power bandwidth

It remains to check whether the ratio variables retained in
\(d\nu(\eta)\) can make the invisible \(u_0,v_0\) fibres in (4.794a)
orthogonal before Cauchy.  The exact height phase does not supply such a
coordinate.  Put

\[
 z=\frac{\Delta}{m_2r},\qquad
 \Theta(t;m_2,r,\Delta)=t\log(1+z).
\]

On the core (5.4), (5.5), and (5.8), \(t\in[T,2T]\) and

\[
 |z|\leq\frac{32\mathscr L^B}{T},\qquad
 \partial_{\log r}\Theta
 =-\frac{tz}{1+z}.
\tag{4.796}
\]

For \(T\) large enough that \(|z|\leq1/2\), repeated application of
\(z\partial_z\) gives, for every fixed \(j\geq1\),

\[
 \boxed{
  \left|\partial_{\log r}^{\,j}\Theta\right|
  +\left|\partial_{\log m_2}^{\,j}\Theta\right|
  \leq C_j\mathscr L^B.}
\tag{4.797}
\]

The other ratio-dependent factors are fixed-support dyadic cutoffs and
the Schwartz transforms created by the two exact Poisson steps.  Hence,
for each resulting one-dimensional ratio kernel \(F_T(y)\), its inherited
seminorms satisfy

\[
 \|F_T^{(j)}\|_{L^1(\mathbb R)}
 \leq C_{j,W}\mathscr L^{C_{j,W}},
\]

and integration by parts in \(y\) gives

\[
 \boxed{
 |\widehat F_T(\tau)|
 \leq C_{J,W}\mathscr L^{C_{J,W}}(1+|\tau|)^{-J}.}
\tag{4.798}
\]

In particular, for every fixed \(\eta>0,A\geq0,D>0\), choosing \(J\)
after \((\eta,A,D,W)\) yields

\[
 \boxed{
 \int_{|\tau|>T^\eta}(1+|\tau|)^A
       |\widehat F_T(\tau)|\,d\tau
 \ll_{\eta,A,D,W}T^{-D}.}
\tag{4.799}
\]

Thus the ratio-Mellin frequency has exact power exponent zero.  This is
also the reason that the \(T\tau\) occurring in the separately scaled
transverse inversion (4.560) cannot be counted as a second bandwidth:
there \(\tau\) is dual to \(T(\log x-\log y)\), and that scaling already
reconstructs the determinant window.  It is not the unscaled divisor-ratio
frequency in (4.747)--(4.749).

On the strict-power cell (4.781), the two hidden fibres have lengths

\[
 U_0=T^{s/2-r_1},\qquad V_0=T^{s/2-r_2}.
\]

Changing one integer in the first fibre changes its logarithm by
\(T^{-(s/2-r_1)}\) up to a fixed factor.  A Mellin character needs
\(|\tau|=T^{s/2-r_1}\) to resolve that spacing, and similarly needs
\(|\upsilon|=T^{s/2-r_2}\) on the second fibre.  Formula (4.799) removes
both ranges whenever the corresponding exponent is positive.  Their
total unresolved exponent is

\[
 \left(\frac s2-r_1\right)+\left(\frac s2-r_2\right)
 =s-\delta-\theta=\gamma-\theta.
\tag{4.800}
\]

At the hard vertex this total is zero, so there is no hidden fibre to
resolve, but (4.794a) still has the independent deficit \(\delta=1\).
Therefore ratio bandwidth neither repairs the grouped Cauchy diagonal on
the interior nor supplies the missing saving at the vertex.  The only
remaining admissible interface is still a pre-Cauchy estimate for the
joint physical kernel.  The adapter
`strict_power_ratio_mellin_bandwidth_audit` records power bandwidth zero,
the two exact fibre exponents, and
`ratio_mellin_supplies_required_delta_saving=False`.

### 4.104 Double Poisson exposes a resonance but absolute summation enlarges the deficit

The first actual second coordinate comes from Poisson summation in both
reduced slopes, not from ratio Mellin inversion.  Fix \(r,t\) in (4.787),
put

\[
 A_0=T^{\delta-r_1},\qquad B_0=T^{\delta-r_2},
 \qquad H=T^\delta,
\]

and use the Fourier convention in (4.558).  For fixed smooth weights
\(U,V,w\), ordinary Poisson summation gives the exact identity

\[
 \boxed{
 \begin{aligned}
 &\sum_{a_0,b_0}U(a_0/A_0)V(b_0/B_0)
   w\!\left(\frac{ra_0-tb_0}{H}\right)\\
 &\quad=A_0B_0\sum_{k,l\in\mathbb Z}
   \int_{\mathbb R}\widehat w(\eta)
   \widehat U\!\left(A_0\left(k-\frac{\eta r}{H}\right)\right)
   \widehat V\!\left(B_0\left(-l+\frac{\eta t}{H}\right)\right)
   \,d\eta .
 \end{aligned}}
\tag{4.801}
\]

The signs in (4.801) use the relabeling \(l\mapsto-l\) in the second
Poisson sum.  Since

\[
 rA_0\asymp tB_0\asymp T^{1+\delta},
\]

the two transform bumps have a common \(\eta\)-width \(T^{-1}\), up to
the already budgeted Schwartz tails.  Their central frequencies and the
integer resonance have scales

\[
 \boxed{
 \begin{array}{c|ccc}
  \text{variable}&k&l&n:=kt-lr\\ \hline
  \log_T(\text{length})
  &1+r_1-\delta&1+r_2-\delta&1+\theta.
 \end{array}}
\tag{4.802}
\]

Indeed, overlap in (4.801) implies

\[
 \left|\frac{kH}{r}-\frac{lH}{t}\right|
 \ll_W T^{-1}\mathscr L^{O_W(1)},
\]

and clearing denominators gives

\[
 \boxed{|kt-lr|\ll_W T^{1+\theta}\mathscr L^{O_W(1)}.}
\tag{4.803}
\]

The variable \(n=kt-lr\) is always an exact integer; (4.803) is only its
Schwartz-effective range.  Dyadic subdivision in \(n\), together with the
rapid transform tails, therefore gives an exact signed resonance family.

This transform is not useful after absolute summation.  Including the
\((d_1,d_2)\)-volume, the tuple count on the transformed side has exponent

\[
 (\delta+\theta)+2+(2-\delta+\theta)-1=3+2\theta.
\]

The Poisson amplitude \(A_0B_0\) has exponent \(\delta-\theta\), and the
common \(\eta\)-overlap has exponent \(-1\).  Hence the transformed inner
absolute exponent is

\[
 \boxed{
 E_{\rm 2P,abs}=2+\delta+\theta,qquad
 E_{\rm inner,raw}=1+2\delta,qquad
 E_{\rm 2P,abs}-E_{\rm inner,raw}=1-\delta+\theta.}
\tag{4.804}
\]

Restoring \((u_0,v_0,q)\), whose total exponent is \(\gamma\), gives

\[
 \boxed{
 E_{\rm 2P,global}=2+s+\theta,qquad
 E_{\rm target}=1+s,qquad
 E_{\rm 2P,global}-E_{\rm target}=1+\theta.}
\tag{4.805}
\]

There is a legal BBLR comparison on the transformed side.  Use \(r,t\)
as its arbitrary outer-coefficient variables, \(l,k\) as the two
nontrivial inner variables, and \(n\) as its shift.  The outer sum,
largest outer scale, side-product scale, and shift scale are

\[
 S'=2+\delta+\theta,\qquad
 M'_\ast=1+r_\ast,\qquad
 P'=2+\theta,\qquad
 \alpha'=1+\theta.
\]

The sharp-range condition (4.604) becomes

\[
 \boxed{S'\geq2\alpha'
 \quad\Longleftrightarrow\quad \delta\geq\theta,}
\tag{4.806}
\]

which holds everywhere on (4.781).  Equations (4.605) give, before
restoring the transform normalization,

\[
 \boxed{
 E'_{\rm AB}=\frac72+\delta+2\theta,\qquad
 E'_{\rm Watt}=\frac{11}{4}+\frac32\theta+\frac12r_\ast.}
\tag{4.807}
\]

The product of the Poisson amplitude and the common overlap width has
exponent

\[
 (\delta-\theta)-1=\delta-\theta-1.
\]

Adding this factor and the outside exponent \(\gamma=s-\delta\), then
subtracting the target \(1+s\), gives the exact transformed BBLR
deficits

\[
 \boxed{
 D'_{\rm AB}=\frac32+\delta+\theta,\qquad
 D'_{\rm Watt}=\frac34+\frac12\theta+\frac12r_\ast.}
\tag{4.808}
\]

The first expression is identical to the original deficit in (4.790).
For the second expression,

\[
 \boxed{
 D'_{\rm Watt}-D_{\rm Watt}
 =\frac{1+\theta-\delta}{2}\geq0.}
\tag{4.809}
\]

Equality in (4.809) is possible only at
\((s,\delta,\theta)=(1,1,0)\).  Therefore simultaneous slope Poisson
summation never improves the published BBLR estimate: its first error is
invariant and its Watt error is weakly worse, becoming equal only on the
hard vertex.

Thus an absolute treatment of the resonance needs \(T^{1+\theta}\),
whereas the original core needs \(T^\delta\).  The extra loss is exactly
\(T^{1-\delta+\theta}\).  At the hard vertex this extra loss is zero, but
the original \(T^1\) deficit remains.  Consequently the double-Poisson
coordinate is retained only as a possible *signed pre-Cauchy* spectral
interface; it supplies no unconditional box by itself.  The adapter
`strict_power_double_poisson_resonance_audit` records (4.801)--(4.805) and
the comparison (4.806)--(4.809).  It keeps
`absolute_double_poisson_route_covered=False` and
`double_poisson_improves_bblr=False`.

### 4.105 A signed MRTT adapter leaves the exact shift-power deficit

The positive local variance (4.730) is stronger than the original
centered problem.  A closer published comparison is an averaged
nonzero-shift correlation.  The coefficient decomposition begins with
an exact finite identity.  Put

\[
 a_U(n)=\mu(n)\mathbf 1_{n\leq U}.
\]

For integers \(K,U\geq1\), the convolution
\((\mu-a_U)^{*K}(n)\) vanishes when \(n\leq U^K\).  Expanding it and
convolving by \(\mathbf 1^{*(K-1)}\), using
\(\mu*\mathbf1=\varepsilon\), gives

\[
 \boxed{
 \mu(n)=\sum_{j=1}^{K}(-1)^{j+1}\binom Kj
 \big(a_U^{*j}*\mathbf1^{*(j-1)}\big)(n),
 \qquad n\leq U^K.}
\tag{4.810}
\]

There is no analytic truncation error in (4.810).  Taking
\(U=(2Y)^{1/K}\), then choosing \(K>K_0(A,\vartheta)\), makes every
Möbius factor in the dyadic expansion \(Y^\varepsilon\)-short.  The
combinatorial decomposition then has the same scale alternatives as in
Matomäki--Radziwiłł--Tao I:

\[
 \boxed{
 \begin{array}{ll}
 \text{Type II:}&Y^\varepsilon\ll N\ll H_0,\quad NM\asymp Y,\\
 \text{Type }d_j:&N\ll Y^\varepsilon,\quad
  H_0\ll M_1\ll\cdots\ll M_j.
 \end{array}}
\tag{4.811}
\]

The long factors in the second line are the \(\mathbf1\)-factors from
(4.810).  Thus the Type-II input keeps divisor-bounded short
coefficients, while the Type-\(d_j\) input sees only the permitted long
unit factors.

For the ratio-twisted product define

\[
 \mu_z(n)=\mu(n)n^{iz},\qquad
 f_\tau=\mu_{\tau/2}*\mu_{-\tau/2}.
\tag{4.812}
\]

Multiplication by \(n^{iz}\) commutes with Dirichlet convolution.
Uniformly for \(|\tau|\leq(\log Y)^C\),

\[
 \boxed{
 |f_\tau(n)|\leq d_2(n),\qquad
 f_\tau(pm)=-
 \big(p^{i\tau/2}+p^{-i\tau/2}\big)f_\tau(m)
 \quad(p\nmid m).}
\tag{4.813}
\]

These are the exact candidate substitutions for a typical-prime-factor
argument.  The first gives a \(d_2\) majorant for the mean-value and
large-values steps.  In the Ramaré identity the constant prime
coefficient is replaced by the parenthesis in (4.813), whose modulus is
at most \(2\); its two summands translate the height of the same prime
Dirichlet polynomial.  The extracted prime bands are squarefree, so
\(p\nmid m\) holds exactly where the second identity is invoked.

The major arcs have arbitrary logarithmic decay.  The hyperbola identity
and Davenport's uniform Möbius exponential-sum estimate, followed by
partial summation for the polylogarithmic Archimedean twists, give

\[
 \boxed{
 \sup_{\substack{\alpha\in\mathbb R\\
                  |\tau|\leq(\log Y)^C}}
 \left|\sum_n f_\tau(n)V(n/Y)e(n\alpha)\right|
 \ll_{A,C,V}Y(\log Y)^{-A}.}
\tag{4.814}
\]

Splitting the convolution at \(d\leq\sqrt{2Y}\) leaves an inner Möbius
sum of length at least a constant multiple of \(\sqrt Y\); Davenport
saves an arbitrary logarithmic power, the harmonic \(d\)-sum costs one
logarithm, and the square boundary is \(O(Y^{1/2+o(1)})\).

The published MRTT long-shift theorem has the following normalization.
For bounded smooth \(V,V',w\), \(H=Y^\vartheta\), and polylogarithmic
\(\tau,\upsilon\), it gives

\[
 \boxed{
 \sum_h w(h/H)\sum_n
 f_\tau(n)V(n/Y)
 \overline{f_\upsilon(n+h)V'((n+h)/Y)}
 \ll_{A,C,V,V',w}YH(\log Y)^{-A}.}
\tag{4.815}
\]

This is an averaged-Chowla estimate: it saves arbitrary logarithms
relative to the \(YH\) count, but it does not save the number \(H\) of
shifts.  On a strict core cell,

\[
 Y=T^{1+\delta},\qquad H=T^\delta,\qquad
 \vartheta=\frac{\delta}{1+\delta}.
\tag{4.816}
\]

MRTT I's published threshold \(\vartheta\geq8/33\) is therefore

\[
 \boxed{
 \frac{\delta}{1+\delta}\geq\frac8{33}
 \quad\Longleftrightarrow\quad
 \delta\geq\frac8{25}.}
\tag{4.817}
\]

Below (4.817), (4.813) and (4.814) identify a plausible signed
typical-factor adaptation of MRTT II, but they do not by themselves
reconstruct every exceptional-set and minor-arc estimate in that proof.
The coverage adapter therefore does not mark the sub-threshold extension
as verified.  This distinction is immaterial at the hard vertex
\(\delta=1\), which lies in the published range.

The decisive comparison is between the exponent supplied by (4.815)
and the exponent required by the MWKF core:

\[
 \boxed{
 E_{\mathrm{MRTT}}=(1+\delta)+\delta=1+2\delta,\qquad
 E_{\mathrm{MWKF}}=1+\delta,\qquad
 E_{\mathrm{MRTT}}-E_{\mathrm{MWKF}}=\delta.}
\tag{4.818}
\]

Restoring the shared gcd exponent \(\gamma=s-\delta\) gives the same
deficit:

\[
 \boxed{
 E_{\mathrm{MRTT,global}}=1+s+\delta,\qquad
 E_{\mathrm{target}}=1+s,\qquad
 E_{\mathrm{MRTT,global}}-E_{\mathrm{target}}=\delta.}
\tag{4.819}
\]

Consequently even the product-compatible model is not closed.  What is
actually sufficient is the strictly stronger signed estimate

\[
 \boxed{
 \sum_h w(h/H)\sum_n
 f_\tau(n)V(n/Y)
 \overline{f_\upsilon(n+h)V'((n+h)/Y)}
 \ll_{A,C,V,V',w}Y(\log Y)^{-A}.}
\tag{4.820}
\]

Estimate (4.820) gains the full power \(H=T^\delta\) beyond the MRTT
scale and is not a consequence of either MRTT theorem.  It is weaker
than the positive uniform variance (4.730), because the physical kernel
is centered and signed, but it remains a genuinely new pre-Cauchy
spectral/dispersion estimate.  The physical gcd layers and the full
ratio-twisted coefficient family would still have to be restored after
proving it.

The exact-rational adapter
`mrtt_signed_mobius_power_shift_audit` records (4.816)--(4.819), and
`truncated_heath_brown_mobius_identity` checks (4.810)
coefficientwise through \(n=U^K\).  Its status fields deliberately keep
`mrtt_scale_closes_mwkf_model=False`,
`full_ratio_twisted_multiplicative_family_covered=False`,
`product_compatible_hard_vertex_covered=False`,
`physical_gcd_layer_adapter_verified=False`, and
`whole_strict_power_core_covered=False`.

### 4.106 The hard vertex is a unimodular four-Möbius determinant shell

The missing factor in (4.820) can be seen without a circle-method
normalization.  First freeze the product-compatible coefficient
\(f=\mu*\mu\).  For smooth \(V,V'\) and a nonzero-shift weight \(w\),
finite reindexing gives the exact identity

\[
 \boxed{
 \begin{aligned}
 \mathcal A(Y,H)
 &:=
 \sum_h w(h/H)\sum_n
 f(n)V(n/Y)f(n+h)V'((n+h)/Y)\\
 &=\sum_{a,b,c,d\geq1}
 \mu(a)\mu(b)\mu(c)\mu(d)
 w\!\left(\frac{cd-ab}{H}\right)
 V(ab/Y)V'(cd/Y).
 \end{aligned}}
\tag{4.821}
\]

At the hard vertex \(Y=T^2\), \(H=T\), the balanced factor box has
\(a,b,c,d\asymp T\) and \(|cd-ab|\asymp T\).  For fixed \(a,b,c\), the
allowed \(d\)-interval has length
\(O(H/c+1)=O(1)\).  Its raw cardinality therefore has exponent \(3\),
whereas the required correlation scale in (4.820) is \(Y=T^2\).

Now dyadically extract

\[
 g=(a,c)\asymp G=T^\kappa,\qquad
 a=ga_0,\quad c=gc_0,\quad(a_0,c_0)=1,
 \qquad 0\leq\kappa\leq1.
\tag{4.822}
\]

The shift is divisible by \(g\).  Writing \(cd-ab=gk\) gives

\[
 c_0d-a_0b=k.
\tag{4.823}
\]

Choose any Bézout pair \(p,q\) satisfying
\(c_0p-a_0q=1\).  Every integral solution of (4.823), with no omission
or multiplicity, is

\[
 \boxed{
 d=pk+a_0t,\qquad b=qk+c_0t,\qquad t\in\mathbb Z.}
\tag{4.824}
\]

Indeed the coordinate matrix is unimodular:

\[
 \det
 \begin{pmatrix}
 q&c_0\\ p&a_0
 \end{pmatrix}
 =qa_0-c_0p=-1.
\tag{4.825}
\]

Changing the Bézout pair only translates \(t\), so the finite sum is
independent of this choice.  The exact dyadic scales are

\[
 \boxed{
 \begin{array}{c|ccccc}
 \text{variable}&g&a_0&c_0&k&t\\ \hline
 \log_T(\text{length})
 &\kappa&1-\kappa&1-\kappa&1-\kappa&\kappa .
 \end{array}}
\tag{4.826}
\]

The \(t\)-range is the intersection of the two intervals imposed by
\(b,d\asymp T\), hence has length \(O(G+1)\).  Consequently one gcd
layer has raw exponent

\[
 E_{\mathrm{raw}}(\kappa)
 =\kappa+2(1-\kappa)+(1-\kappa)+\kappa
 =3-\kappa.
\]

A precise model gate is therefore

\[
 \boxed{
 \begin{aligned}
 \mathcal S_\kappa[\Psi]
 :=\sum_{g\asymp T^\kappa}
 \sum_{\substack{a_0,c_0\asymp T^{1-\kappa}\\(a_0,c_0)=1}}
 \sum_{k\asymp T^{1-\kappa}}\sum_t
 &\mu(ga_0)\mu(gc_0)\\
 {}\times&
 \mu(qk+c_0t)\mu(pk+a_0t)\Psi
 \ll_{B,\Psi}T^2(\log T)^{-B}.
 \end{aligned}}
\tag{4.827}
\]

Here \(\Psi\) imposes (4.824), positivity, all four balanced dyadic
ranges, and the chosen signed shift box.  The required power saving is

\[
 (3-\kappa)-2=1-\kappa.
\]

This is exactly square-root cancellation in the pair
\((a_0,c_0)\), whose joint exponent is \(2(1-\kappa)\); equivalently it
is complete cancellation in the \(k\)-block.  Even where an
averaged-Chowla input can be adapted, its logarithmic saving relative
to the raw layer does not provide this power.

The endpoint \(\kappa=1\) requires a separate warning.  Its positive
power deficit vanishes, but taking \(a_0=c_0=1\), \(p=1\), and \(q=0\)
leaves the subfamily

\[
 \sum_{g\asymp T}\mu(g)^2
 \sum_{t\asymp T}\mu(t)\mu(t+k)\Psi(g,t,k),
 \qquad k\asymp1.
\]

Arbitrary logarithmic saving here contains the ordinary Cesàro
fixed-shift two-point Chowla problem and is not known.  The closed
polylogarithmic gcd collar for the actual physical coefficients in
Section 4.100 uses an additional outer Möbius cancellation; it cannot be
transferred after freezing the coefficient to \(f=\mu*\mu\).
Thus every strict \(\kappa<1\) layer needs a new centered
outer-Möbius spectral estimate, while the top model face still needs a
new logarithmic cancellation.

The helper
`hard_vertex_four_mobius_determinant_line_identity` verifies
(4.822)--(4.825) on exact integers.  The exponent adapter
`hard_vertex_four_mobius_determinant_audit` records (4.826)
and the critical saving in (4.827).  This is a product-compatible
hard-vertex model: the actual ratio-Mellin deformation and physical gcd
allocations have not yet been restored.  Accordingly both the model
estimate and the full MWKF core remain unproved.


### 4.107 Periodic arithmetic-weight Kuznetsov cannot encode the modulus Möbius gain

[Blomer--Milićević's arithmetic-weight Kuznetsov theorem](https://arxiv.org/abs/1410.4538)
permits a
periodic weight on the Kloosterman modulus, so it is a natural possible
replacement for the inadmissible entry-weighted trace formula of
Section 4.64.  Their normalization is

\[
 \boxed{
 \widehat f(\chi)
 =\frac1{\varphi(q)^{1/2}}
   \sum_{a\bmod q}^{*}\overline{\chi(a)}f(a),\qquad
 \|\widehat f\|_1=\sum_{\chi\bmod q}|\widehat f(\chi)|.}
\tag{4.828}
\]

For \(f:(\mathbb Z/q\mathbb Z)^\times\to\mathbb C\), fixed smooth
\(f_\infty\), and \(mn\leq X^2\), their Theorem 1 states

\[
 \boxed{
 \sum_{\substack{c\geq1\\(c,q)=1}}
 \frac{S(m,n;c)}{c^{1/2}}f(c)f_\infty(c/X)
 \ll_{f_\infty,\varepsilon}
 X^{1/2+2\vartheta}\|\widehat f\|_1(mnq)^\varepsilon,}
\tag{4.829}
\]

where \(\vartheta=7/64\) is currently admissible.

Give this theorem its most favorable direct interpretation for a Möbius
modulus weight.  Choose a prime \(q>2X\), so reduction modulo \(q\) is
injective on \([X,2X]\), and define \(f(c\bmod q)=\mu(c)\) on that
interval and zero on the other reduced residues.  Multiplicative
Parseval and the squarefree density give

\[
 \boxed{
 \|\widehat f\|_1\geq\|\widehat f\|_2
 =\left(\sum_{a\bmod q}^{*}|f(a)|^2\right)^{1/2}
 =X^{1/2+o(1)}.}
\tag{4.830}
\]

Consequently the smallest right side compatible with Parseval already
has exponent

\[
 \boxed{
 E_{\mathrm{BM}}
 =\left(\frac12+2\vartheta\right)+\frac12
 =1+2\vartheta.}
\tag{4.831}
\]

The normalized modulus sum has the direct Weil-bound exponent \(1\).
Thus the published theorem loses \(X^{2\vartheta}\).  The paper's
Selberg-conjecture remark does **not** set every occurrence of
\(\vartheta\) to zero: it replaces \(X^{2\vartheta}\) by
\((mn)^\vartheta\), retaining the finite-prime Ramanujan exponent.
Only the full Ramanujan conjecture, including Selberg at infinity,
sets \(\vartheta=0\) and merely ties the trivial exponent.

On the balanced QCT box \(X=S=T^3\), the combined physical numerator has
scale \(h\delta=T^5\), so the favorable Linnik-range check
\(T^5\leq X^2=T^6\) succeeds.  Nevertheless,

\[
 \boxed{
 E_{\mathrm{BM}}=\frac{117}{32},\qquad
 E_{\mathrm{triv}}=3,\qquad
 E_{\mathrm{BM}}-E_{\mathrm{triv}}=\frac{21}{32}}
\tag{4.832}
\]

in \(T\)-exponents.  This deficit occurs before charging the fact that
the QCT kernel is an incomplete, coupled orbit rather than the complete
Kloosterman family in (4.829).

Under Selberg alone, the direct periodic encoding instead has

\[
 \boxed{
 E_{\mathrm{BM,Sel}}=3+5\left(\frac7{64}\right)
 =\frac{227}{64},\qquad
 E_{\mathrm{BM,Sel}}-3=\frac{35}{64}.}
\tag{4.832a}
\]

Full Ramanujan lowers (4.832a) to \(3\), still with zero power-saving
margin.

This audit rejects the direct collision-free periodic encoding.  It
does not assert that no specially chosen smaller period can agree with
a finite Möbius interval, and it does not reject a Type-I/II expansion
followed by separate level formulas.  Such a hybrid must still retain
the two Möbius cofactors and is exactly the unresolved centered
dispersion problem, not an application of (4.829) alone.  The coverage
adapter records the Parseval lower bound, the \(21/32\) hard-box deficit,
the Selberg-only \(35/64\) deficit, the zero full-Ramanujan margin, and
leaves the whole Möbius gate unproved.


### 4.108 Type-I level extraction still needs exceptional-spectrum cancellation

The periodic encoding is deliberately wasteful: it asks one finite
period to remember every value of \(\mu(c)\).  The exact Möbius
factorization gives a different use of the same trace formula.  For
\(c>U\), put

\[
 \boxed{
 c_U(a)=\sum_{\substack{d\mid a\\d\leq U}}\mu(d),\qquad
 \mu(c)=-\sum_{\substack{ab=c\\a>U}}c_U(a)\mu(b).}
\tag{4.833}
\]

Split the last sum at \(b\leq V\).  In the Type-I part write \(a=d\ell\)
inside \(c_U(a)\).  After an exact dyadic partition \(b\asymp B\),
\(d\asymp D\), a model modulus block is

\[
 \boxed{
 \begin{aligned}
 \mathcal K_{B,D}(m,n;X)
 =-&\sum_{\substack{b\asymp B\\b\leq V}}\mu(b)
 \sum_{\substack{d\asymp D\\d\leq U}}\mu(d)
 \sum_{\substack{\ell\geq1\\bd\ell\asymp X\\d\ell>U}}
 \frac{S(m,n;bd\ell)}{(bd\ell)^{1/2}}\\
 &\hspace{35mm}\times
 F_{b,d}\!\left(\frac{bd\ell}{X}\right).
 \end{aligned}}
\tag{4.834}
\]

The inequalities in (4.834) are retained, not absorbed into asymptotic
notation.  Partial summation treats their two endpoints, while the
fixed dyadic functions \(F_{b,d}\) have the inherited uniform smooth
seminorms.  This is still only the product-compatible modulus model;
the other Möbius entry, ratio integrals, and physical QCT kernel have
not been restored.

Estimate (211) in the proof of
[Blomer--Milićević, Theorem 1](https://arxiv.org/abs/1410.4538) gives,
uniformly for \(mn\leq X^2\) and every fixed divisibility level \(L\),

\[
 \boxed{
 \sum_{L\mid c}\frac{S(m,n;c)}{c^{1/2}}
 F_\infty(c/X)
 \ll_{F_\infty,\varepsilon}
 X^{1/2+2\vartheta}(mnL)^\varepsilon.}
\tag{4.835}
\]

Thus (4.835) applies separately to \(L=bd\).  Put

\[
 X=T^3,\qquad mn=T^5,\qquad
 B=T^\beta,\quad D=T^\eta,\quad
 \lambda=\beta+\eta.
\tag{4.836}
\]

The Linnik hypothesis is satisfied because \(5\leq2\cdot3\).  Absolute
summation over \((b,d)\) and, even more favorably, an unproved ideal
Cauchy aggregation over the \(T^\lambda\) level pairs give respectively

\[
 \boxed{
 E_{\mathrm{I,abs}}=\frac{69}{32}+\lambda,\qquad
 E_{\mathrm{level\text{-}Cauchy}}=\frac{69}{32}+\frac\lambda2.}
\tag{4.837}
\]

The hard determinant model requires exponent \(2\).  Consequently the
two conditions in (4.837) would be

\[
 \boxed{
 \lambda<-\frac5{32},\qquad
 \lambda<-\frac5{16}.}
\tag{4.838}
\]

Neither contains a nonnegative level box: the uniform Kim--Sarnak
exceptional-spectrum factor already loses \(T^{5/32}\) when \(B=D=1\).

Selberg alone replaces the fixed-level exponent \(69/32\) by

\[
 \frac32+5\left(\frac7{64}\right)=\frac{131}{64}.
\]

It therefore still requires \(\lambda<-3/64\) after absolute summation
or \(\lambda<-3/32\) after the ideal Cauchy step.  Under full Ramanujan
the two bounds become

\[
 \boxed{
 E_{\mathrm{I,abs}}^{\mathrm{Ram}}=\frac32+\lambda,\qquad
 E_{\mathrm{level\text{-}Cauchy}}^{\mathrm{Ram}}
 =\frac32+\frac\lambda2.}
\tag{4.839}
\]

Hence even that conjectural ledger covers only \(\lambda<1/2\) by
absolute summation and \(\lambda<1\) by ideal level Cauchy.  At the
critical level face \(\lambda=1\), (4.839) is exactly \(T^2\) and
supplies none of the logarithmic decay needed for \(o(T)\).

The sharp new local input suggested by this route is therefore a
Möbius-weighted level-family estimate of the form

\[
 \boxed{
 \sum_{\substack{b\asymp B\\d\asymp D}}
 \alpha_{b,d}
 \sum_{bd\mid c}\frac{S(m,n;c)}{c^{1/2}}
 \mathscr F_{b,d}\!\left(\frac c{T^3}\right)
 \ll_{A,\mathscr F}
 T^{3/2+\lambda/2}(\log T)^{-A},
 \qquad 0\leq\lambda\leq1.}
\tag{4.840}
\]

Here \(\alpha_{b,d}=\mu(b)\mu(d)\) times the retained Type-I and
allocation coefficients, while \(\mathscr F_{b,d}\) must still contain
the second Möbius cofactor and the coupled physical kernel.  In
particular (4.840) must cancel the exceptional spectrum in the level
family; it is not the ordinary positive spectral large sieve.  No
published theorem audited here proves (4.840), and the Type-II sector
\(b>V\), including level boxes \(\lambda>1\), still requires the
centered four-variable dispersion estimate.  The adapter
`blomer_milicevic_type_i_level_audit` records (4.836)--(4.839) and keeps
both the level-Cauchy and physical-kernel proof flags false.


### 4.109 Coupled-conductor density removes the archimedean exceptional loss but leaves the finite-prime Hecke loss

The factor \(X^{2\vartheta}\) in (4.835) combines an exceptional
archimedean transform loss with a finite-prime Hecke loss.  These must
be separated before testing the strongest published level-density
saving.
[Humphries, Theorem 1.2](https://arxiv.org/abs/1609.06740), specialized
to \(\Gamma_0(q)\), trivial character, and no finite-prime condition,
states that for \(0<\alpha<1/2\),

\[
 \boxed{
 N_q(\alpha):=
 \#\{f\in\mathcal B_0(q):it_f\in(\alpha,1/2)\}
 \ll_\varepsilon
 \operatorname{vol}(\Gamma_0(q)\backslash\mathbb H)^{1-4\alpha+\varepsilon}.}
\tag{4.841}
\]

For \(q\asymp Q=T^\lambda\), the volume is
\(q^{1+o(1)}\).  The earlier audit at this point used \(X^{2\nu}\)
for the exceptional Bessel-transform loss.  That drops the numerator
conductor and is not the specialization of the published proof.
Blomer--Milićević define

\[
 \Xi=\frac{\sqrt{mn}}X.
\]

If \(X=T^\sigma\) and \(mn=T^\tau\), their exact small-parameter
transform bound is \(\Xi^{-2\nu}\), while their separate pointwise
finite-prime Hecke estimate costs \((mn)^\vartheta\).  Thus the
pre-density spectral loss is

\[
 \boxed{
 (mn)^\vartheta\Xi^{-2\nu}
 =T^{\tau\vartheta+(2\sigma-\tau)\nu}.}
\tag{4.842}
\]

Give (4.841) its most favorable volume-normalized use.  The exceptional
count at height \(\nu\) gains \(Q^{-4\nu}\), so the exact exponent
ledger becomes

\[
 \boxed{
 \tau\vartheta+
 \sup_{0\leq\nu\leq\vartheta}
 (2\sigma-\tau-4\lambda)\nu
 =
 \tau\vartheta+
 \vartheta\max(2\sigma-\tau-4\lambda,0).}
\tag{4.843}
\]

This still grants more than Humphries literally supplies for the joint
QCT coefficients: (4.841) is a positive counting theorem, not a
weighted spectral large sieve.  It is an exact conductor test of that
optimistic grant.

At the critical Type-I face

\[
 \sigma=3,\qquad \tau=5,\qquad \lambda=1,\qquad
 \vartheta=\frac7{64},
\]

the archimedean exceptional residual in (4.843) is zero, but the
finite-prime Hecke loss is

\[
 \boxed{
 5\vartheta=\frac{35}{64}.}
\tag{4.844}
\]

The full-Ramanujan ideal level-Cauchy base in (4.839) is exactly
\(T^2\).  Restoring the pointwise finite-prime loss gives

\[
 \boxed{
 E_{\mathrm{density}}
 =2+\frac{35}{64}=\frac{163}{64},
 \qquad
 E_{\mathrm{density}}-2=\frac{35}{64}.}
\tag{4.844a}
\]

The level thresholds are now compatible.  The target bound for the
ideal Cauchy base requires \(\lambda\leq1\), while neutralizing only
the archimedean exceptional growth requires

\[
 \boxed{
 \lambda\geq\frac{2\sigma-\tau}{4}=\frac14.}
\tag{4.845}
\]

Therefore exceptional eigenvalues are not the numerical obstruction
on the critical level face once the coupled numerator conductor is
retained.  The remaining power is exactly the use of the individual
Kim--Sarnak bound at the finite primes.  A successful continuation
must average the Hecke entries together with the retained Möbius
variables and physical kernel, avoiding that pointwise
\((mn)^\vartheta\) charge.  Humphries alone does not do this and does
not justify the ideal level Cauchy step.  The adapter
humphries_exceptional_level_density_audit records the ratio exponent
\(2\sigma-\tau=1\), the neutral level \(1/4\), the surviving
\(35/64\), and keeps the QCT spectral-weight and whole-gate flags
false.


### 4.109a The corrected local gate is a pre-Cauchy finite-prime Hecke average

Section 4.109 changes the interpretation of (4.840).  Write the two
Hecke-index scales as \(T^a,T^b\), so \(a+b=\tau\).  At level
\(T^\lambda\), the ideal full-Ramanujan level-Cauchy base is

\[
 E_{\rm Ram}=\frac{\sigma}{2}+\frac{\lambda}{2}.
\]

The pointwise finite-prime estimate used in the proof of the
Blomer--Milićević bound adds \((a+b)\vartheta=\tau\vartheta\).
Consequently the critical ledger is

\[
 \boxed{
 E_{\rm pointwise}
 =\frac{\sigma}{2}+\frac{\lambda}{2}+\tau\vartheta
 =2+\frac{35}{64}=\frac{163}{64}.}
\tag{4.845a}
\]

Applying the ordinary spectral large sieve after both Hecke indices
have been frozen is not a remedy.  Its delta-sequence normalization
costs

\[
 \boxed{
 D_{\rm fixed\text{-}LS}
 =\frac12\big((a-\lambda)_++(b-\lambda)_+\big).}
\tag{4.845b}
\]

At the balanced physical index scales
\(a=b=5/2,\lambda=1\), this is \(3/2\), and hence

\[
 \boxed{
 E_{\rm fixed\text{-}LS}=2+\frac32=\frac72.}
\tag{4.845c}
\]

This is worse than the pointwise Kim--Sarnak charge \(35/64\).  Thus
Cauchy followed by a fixed-index large sieve cannot be the missing
argument.

[Pascadi's exceptional large sieve](https://arxiv.org/abs/2404.04239)
is directly relevant to the corrected conductor.  Its proved theorems
handle the archimedean exceptional spectrum for exponential phases and
dispersion coefficients with concentrated Fourier transform, including
critical sequence length comparable with level.  The paper separately
describes a finite-place analogue as a prospective extension; that
extension is not one of its theorems.  It therefore supports the
archimedean conclusion of Section 4.109 but does not remove
\((mn)^\vartheta\).

The weakest sufficient critical inequality is now (4.840) with its
finite-prime role made explicit:

\[
 \boxed{
 \mathfrak H_{\rm entry}[\Psi]
 \ll_{A,W}
 T^{\,\sigma/2+\lambda/2}(\log T)^{-A}
 =T^2(\log T)^{-A}.}
\tag{4.845d}
\]

Here \(\mathfrak H_{\rm entry}\) is the signed level/newform sum before
positive Cauchy, with both Möbius matrix-entry weights, both level
coefficients, every ratio and gcd allocation, and the physical coupled
kernel retained.  Relative to (4.845a), (4.845d) must save exactly
\(T^{35/64}\), then supply logarithmic decay at the zero-margin
endpoint.  Section 4.16 already proves that classical Kuznetsov puts
the Hecke operator on the shift, not on either Möbius entry.  Therefore
deriving \(\mathfrak H_{\rm entry}\) itself requires a new
entry-weighted relative trace formula or an equivalent pre-Cauchy
dispersion identity.

The adapter finite_prime_hecke_average_audit records (4.845a)--(4.845c),
the required \(35/64\), Pascadi's proved archimedean scope, and the
unproved finite-place and entry-adapter flags.  It does not mark
(4.845d) as proved.


### 4.109b Fourier separation of the original Farey family cannot precede positive Cauchy

There is a tempting way to attack (4.845d) before passing to a
fixed-index spectral sum.  It must first be normalized correctly.  For
one product-separated component of the signed Farey kernel, let
\(X=T^x\), \(L=T^\ell\), \(V_1=T^{\nu_1}\),
\(V_2=T^{\nu_2}\), and put

\[
 \begin{aligned}
 P(\alpha)&=\sum_{v\asymp V_1}\sum_{r\asymp X}
   a_{r,v}\mu(r)e(\alpha rv),\\
 Q(\alpha)&=\sum_{j\asymp V_2}\sum_{s\asymp X}
   b_{s,j}\mu(s)e(-\alpha js).
 \end{aligned}
\]

With the Fourier convention
\(\widehat U(\xi)=\int_{\mathbb R}U(y)e(-\xi y)\,dy\), Fourier
inversion gives the exact identity

\[
 \boxed{
 \sum_{r,s,v,j}a_{r,v}b_{s,j}\mu(r)\mu(s)
 U\!\left(\frac{rv-js}{L}\right)
 =L\int_{\mathbb R}\widehat U(L\alpha)
 P(\alpha)Q(\alpha)\,d\alpha.}
\tag{4.845e}
\]

The integral in (4.845e) is over the whole real line; the effective
arc \(|\alpha|\ll L^{-1}(\log T)^C\) follows from the rapid decay of
\(\widehat U\), with the complementary tail bounded by an arbitrary
negative power after retaining the original smooth seminorms.  The
coprimality conditions can be inserted into the coefficients by the
same finite gcd decomposition used before (10.5).  Equation (4.845e)
does **not** assert that the physical coupled kernel has already been
separated: it is the most favorable separated component on which an
ordinary Fourier--Cauchy argument would have to succeed.

For fixed nonzero \(v\asymp T^\nu\), the local mean-value theorem is

\[
 \boxed{
 \int_{|\alpha-\alpha_0|\ll L^{-1}}
 \left|\sum_{r\asymp X}a_r\mu(r)e(\alpha vr)\right|^2d\alpha
 \ll
 \left(\frac XL+\frac1{|v|}\right)
 \sum_{r\asymp X}|a_r\mu(r)|^2.}
\tag{4.845f}
\]

The coefficient energy on the right of (4.845f) has exponent \(x\).
It may not be deleted.  In the hard cell

\[
 (x,\ell,\nu_1,\nu_2)=
 \left(3,\frac52,\frac12,\frac12\right),
\]

the bandwidth factor in parentheses has exponent \(1/2\), while the
complete one-dilate mean square has exponent

\[
 \boxed{x+\max(x-\ell,-\nu_i)=\frac72.}
\tag{4.845g}
\]

Applying Cauchy to the \(V_i\)-family before using any signed
interaction gives, with the normalized Fourier measure
\(L|\widehat U(L\alpha)|d\alpha\),

\[
 \boxed{
 E_{i,\mathrm{Cauchy}}
 =\ell+2\nu_i+x+\max(x-\ell,-\nu_i)=7.}
\tag{4.845h}
\]

Thus Cauchy in (4.845e) yields exponent \(7\), the complete
four-variable ambient bound.  It has discarded the signed Farey
window rather than recovered a half power.

The normalization error is easy to diagnose from the self-diagonal.
In the expansion of either positive short-arc majorant, the literal
terms \((v_1,r_1)=(v_2,r_2)\) have coefficient energy

\[
 \boxed{E_{i,\mathrm{self}}=x+\nu_i=\frac72.}
\tag{4.845i}
\]

If a new joint Möbius--dilate theorem suppressed every other term down
to this natural scale without loss, Cauchy on the two sides would give
only

\[
 \boxed{
 E_{\mathrm{ideal}}
 =\frac12\big((x+\nu_1)+(x+\nu_2)\big)
 =\frac72.}
\tag{4.845j}
\]

This is the zero-slack endpoint and still misses
FTF\(_{\epsilon,1/1000}\) by \(T^{1/1000}\).  The fact that the
original signed support excludes \(rv-js=0\), and the exact completed
identity (12.10) removes its zero character, does not remove the
positive equal-copy terms in (4.845i) created only after squaring.
Therefore a successful argument must retain the signed pairing in
(4.845e) through the new arithmetic estimate, or prove cancellation
between the diagonal-scale and off-diagonal pieces strong enough to
supply a power or logarithmic saving.  Ordinary positive Cauchy cannot
be the missing step.

The adapter farey_dilate_pre_cauchy_audit records (4.845f)--(4.845j),
including the coefficient-energy factor, the ambient exponent (7),
the ideal endpoint (7/2), and the remaining (1/1000).  Its physical
kernel, published joint-dilate estimate, and whole-gate flags remain
false.


### 4.109c Grouping the dilates and Poisson summing them are exact loops, not savings

The signed form in (4.845e) still has two algebraic options which do not
square it.  First group the products.  For product-compatible
coefficients define

\[
 \boxed{
 c_{X,V}(n)=
 \sum_{\substack{v\mid n\\v\asymp V,\ n/v\asymp X}}
 b_v a_{n/v}\mu(n/v).}
\tag{4.845k}
\]

Then (4.845e) is equivalently

\[
 \boxed{
 \sum_{n,m}c_{X,V_1}(n)d_{X,V_2}(m)
 U\!\left(\frac{n-m}{L}\right).}
\tag{4.845l}
\]

Because the signed shift support has \(U(0)=0\), the equal-product
terms \(n=m\) in (4.845l) vanish exactly.  This is the original
centering; replacing the multiplier by an absolute short-arc norm
reintroduces the energy of \(c_{X,V}\).

The identity \(\mu*\mathbf1=\varepsilon\) applies only to the complete
divisor sum

\[
 \boxed{
 \sum_{v\mid n}\mu(n/v)=\mathbf1_{n=1}.}
\tag{4.845m}
\]

It does not collapse (4.845k).  To see the obstruction without an
upper-bound heuristic, choose disjoint interior subintervals and primes
\(p\asymp V\), \(q\asymp X\), with \(X>4V\).  For \(n=pq\), the only
divisor in the selected \(V\)-window is \(p\), so for unit interior
weights

\[
 \boxed{c_{X,V}(pq)=\mu(q)=-1.}
\tag{4.845n}
\]

The prime number theorem supplies

\[
 \boxed{
 \#\{pq:p\asymp V,\ q\asymp X\}
 \asymp\frac{XV}{\log X\log V}=T^{x+\nu-o(1)}.}
\tag{4.845o}
\]

Thus the grouped coefficient has energy of exponent \(x+\nu=7/2\)
on an explicit subfamily.  The complete convolution may still act only
after different divisor windows and boundary pieces are recombined; it
does not give a fixed power inside the hard dyadic cell.

Second, apply Poisson directly to a smooth dilate weight.  With the same
Fourier convention as (4.845e),

\[
 \boxed{
 \sum_{v\in\mathbb Z}B(v/V)e(\alpha rv)
 =V\sum_{k\in\mathbb Z}\widehat B\big(V(k-\alpha r)\big).}
\tag{4.845p}
\]

On the effective arc \(|\alpha|\ll L^{-1}(\log T)^C\), the relevant
numerators have size \(k\ll X/L\), and a packet around \(k/r\) has
width \((VX)^{-1}\).  After the analogous Poisson step in \(j\), two
packets can overlap only if

\[
 \left|\frac kr-\frac ls\right|\ll\frac1{VX}.
\]

Multiplying by \(rs\asymp X^2\) gives

\[
 \boxed{|ks-lr|\ll X/V.}
\tag{4.845q}
\]

At the hard scales \(X=T^3\), \(V=T^{1/2}\), \(L=T^{5/2}\), one has

\[
 \boxed{
 X/L=T^{1/2},\qquad (VX)^{-1}=T^{-7/2},
 \qquad X/V=L=T^{5/2}.}
\tag{4.845r}
\]

Therefore double dilate Poisson reconstructs the same critical
determinant window as (10.3), with the two Fourier transforms exchanged.
It is an exact coordinate loop, not an additional source of
cancellation.  The only potentially useful continuation of (4.845l)
is consequently a *signed* shifted-correlation theorem for the truncated
convolution coefficients, with all dyadic windows and the physical
coupled kernel recombined before estimating.

The adapter farey_dilate_convolution_poisson_audit records
(4.845k)--(4.845r): grouped length \(7/2\), the semiprime energy
witness \(7/2\), numerator length \(1/2\), packet width \(-7/2\), and
the recovered determinant window \(5/2\).  It keeps the dyadic
convolution-saving, physical-kernel, and whole-gate flags false.


### 4.109d A smooth product-index average removes the finite-prime Ramanujan loss for newforms

The \(35/64\) in (4.845a) was obtained only after freezing the combined
Hecke index.  The original physical variables provide a different
ordering.  This is consistent with the Ramanujan-independent
shifted-convolution refinement in
[Milićević--Qin--Wu](https://arxiv.org/abs/2511.07550), especially their
equations (3.11') and (3.13), but the product-index lemma needed here
can be proved directly.

Let \(f\) be a primitive cusp form of trivial nebentypus, level \(Q_f\),
and analytic conductor \(\mathcal C_f\).  Let
\(W_1,W_2\in C_c^\infty((1/2,2))\), and put

\[
 \mathcal J_f(H_1,H_2)
 :=\sum_{h,\delta\ge1}\lambda_f(h\delta)
 W_1(h/H_1)W_2(\delta/H_2).
\]

At \(p\nmid Q_f\), the degree-two Hecke recurrence gives ordinary
Möbius inversion.  At \(p\mid Q_f\), the primitive local standard
factor has degree at most one, so its coefficients are completely
multiplicative.  Prime-by-prime comparison therefore gives the exact
all-index identity

\[
 \boxed{
 \lambda_f(h\delta)
 =\sum_{\substack{d\mid(h,\delta)\\(d,Q_f)=1}}\mu(d)
   \lambda_f(h/d)\lambda_f(\delta/d).}
\tag{4.845s}
\]

Consequently

\[
 \boxed{
 \mathcal J_f(H_1,H_2)
 =\sum_{\substack{d\ge1\\(d,Q_f)=1}}\mu(d)
 A_f(H_1/d;W_1)A_f(H_2/d;W_2),}
\tag{4.845t}
\]

where

\[
 A_f(Y;W):=\sum_{n\ge1}\lambda_f(n)W(n/Y).
\]

For a product of normalized smooth weights, (4.845t) is an identity of
finite sums.  A general two-variable smooth weight is an exact Mellin
superposition of these products; the physical QCT kernel still has to
be shown to possess the required uniform nuclear norm, so that passage
is not assumed below.

Let \(H_0=\min(H_1,H_2)\), \(H_*=\max(H_1,H_2)\), and, with a fixed
large \(B\), split at

\[
 \boxed{D_0=\frac{H_0}{\mathcal C_f(\log T)^B}.}
\tag{4.845u}
\]

Since \(L(s,f)\) is entire, Mellin inversion and the functional equation
give, for every fixed \(J\), uniformly when
\(Y\ge\mathcal C_f(\log T)^B\),

\[
 \boxed{
 A_f(Y;W)
 \ll_{J,W}\mathcal C_f^{1/2}
 \left(\frac{\mathcal C_f}{Y}\right)^J
 (\mathcal C_fY)^{o(1)}.}
\tag{4.845v}
\]

Taking \(J\) after \(B\) therefore gives

\[
 \boxed{
 \sum_{\substack{d\le D_0\\(d,Q_f)=1}}\mu(d)
 A_f(H_1/d;W_1)A_f(H_2/d;W_2)
 \ll_{A,W_1,W_2}H_0(\log T)^{-A}.}
\tag{4.845w}
\]

For \(d>D_0\), interchange the finite sums in (4.845t):

\[
 \boxed{
 \sum_{a,b}\lambda_f(a)\lambda_f(b)
 \sum_{\substack{d>D_0\\(d,Q_f)=1}}\mu(d)
 W_1(da/H_1)W_2(db/H_2).}
\tag{4.845x}
\]

On a compatible dyadic pair \(a\asymp A,b\asymp B_1\), the inner
variable has scale
\(D\asymp H_1/A\asymp H_2/B_1\ge D_0\).  The zeta zero-free region and
partial summation give, for every fixed \(A_0\),

\[
 \boxed{
 \sum_{\substack{d\\(d,Q_f)=1}}
 \mu(d)W_1(da/H_1)W_2(db/H_2)
 \ll_{A_0,W_1,W_2}D(\log T)^{-A_0}.}
\tag{4.845y}
\]

The same bound holds with \((d,Q)=1\) for polynomial \(Q\), after the
finite Euler factors are retained; their zero-free-contour cost is
smaller than the Vinogradov--Korobov decay and is absorbed by choosing
\(A_0\) larger.  Rankin--Selberg and Cauchy give

\[
 \sum_{a\asymp A}|\lambda_f(a)|\ll A(\mathcal C_fA)^{o(1)}
\]

and similarly for \(b\).  Hence one compatible block in (4.845x) is

\[
 AB_1D(\log T)^{-A_0}
 \asymp H_2A(\log T)^{-A_0}.
\]

Since \(A\le H_1/D_0\), summing the logarithmically many blocks gives

\[
 \boxed{
 \sum_{\substack{d>D_0\\(d,Q_f)=1}}\mu(d)
 A_f(H_1/d;W_1)A_f(H_2/d;W_2)
 \ll_{A,W_1,W_2}
 H_*\mathcal C_f(\log T)^{-A}.}
\tag{4.845z}
\]

At the critical scales

\[
 H_1=H_2=T^{5/2},\qquad \mathcal C_f=T^{1+o(1)},
\]

(4.845u), (4.845w), and (4.845z) become

\[
 \boxed{
 D_0=T^{3/2}(\log T)^{-B},\qquad
 \mathcal J_{f,\mathrm{small}}\ll T^{5/2}(\log T)^{-A},\qquad
 \mathcal J_{f,\mathrm{large}}\ll T^{7/2}(\log T)^{-A}.}
\tag{4.845aa}
\]

Thus the smooth product-index newform component, including its ramified
local factors, avoids the pointwise
\((H_1H_2)^{7/64}=T^{35/64}\) charge and supplies the logarithmic decay
required at the zero-margin endpoint.  This is a proved local lemma,
not yet the full finite-prime gate.  Three interfaces remain:

1. the oldclass coefficients must be inserted into (4.845s) without
   losing (4.845z);
2. the physical five-variable QCT transform must be decomposed with a
   polylogarithmic, not positive-power, product nuclear norm; and
3. the other two Möbius entry weights and Type-I level family must remain
   inside the spectral sum until (4.840) is recovered.

The adapter smooth_hecke_product_mobius_audit records the critical split
\(3/2\), the small-\(d\) exponent \(5/2\), the large-\(d\) endpoint
\(7/2\), its arbitrary logarithmic decay, and removal of the \(35/64\)
pointwise loss for the product-smooth newform component.  It records
the primitive ramified factors as restored, while leaving the oldclass,
physical-kernel, finite-prime-gate, and whole-gate flags false.


### 4.109e Blomer--Milićević oldclasses preserve the product-smooth endpoint

The first missing interface in Section 4.109d can be restored without
paying a new power of \(T\).  Let \(f\) be a primitive cusp form of level
\(Q_f\), let \(b\mid Q/Q_f\), and put

\[
 \mathcal N_f(b)=
 \left\{
 b\prod_{p\mid b}
 \left(1-\frac{p|\lambda_f(p)|^2}
 {(p+\chi_0(p))^2}\right)^{-1}
 \right\}^{1/2}.
\]

The exact Blomer--Milićević orthonormal oldclass basis satisfies

\[
 \boxed{
 \sqrt n\,\rho_{f_{(b)}}(n)
 =\mathcal N_f(b)\rho_f(1)
 \sum_{c\ell=b}
 \frac{\mu(c)\overline{\lambda_f(c)}}{\nu(c)}
 \lambda_f\!\left(\frac n\ell\right),}
 \qquad
 \nu(c)=c\prod_{p\mid c}\left(1+\frac{\chi_0(p)}p\right),
\tag{4.845ab}
\]

with \(\lambda_f(x)=0\) when \(x\notin\mathbb N\).  In the
Blomer--Milićević Kuznetsov reduction the first Fourier index \(m'\)
satisfies

\[
 (m',Q)=1.
\tag{4.845ac}
\]

Since \(\ell\mid b\mid Q/Q_f\), only \(\ell=1,c=b\) survives in
(4.845ab) at \(m'\).  At the second Fourier index retain a term
\(c\ell=b\), and allocate
\(\ell=\ell_1\ell_2\) to the two smooth Hecke variables.  Write

\[
 H_1=H_2=T^{u},\quad
 Q=T^{\lambda+o(1)},\quad
 Q_f=T^{\rho+o(1)},\quad
 b=T^{\beta+o(1)},\quad
 c=T^{\gamma+o(1)},\quad
 \ell_i=T^{e_i+o(1)}.
\]

The exact constraints are

\[
 \rho+\beta=\lambda,\qquad
 0\leq\gamma\leq\beta,\qquad
 e_1+e_2=\beta-\gamma,\qquad e_1,e_2\geq0.
\tag{4.845ad}
\]

The product of the two oldclass normalizations in (4.845ab), including
the Hecke bounds only on \(b\) and \(c\), has exponent

\[
 \mathcal N_f(b)^2
 \frac{|\lambda_f(b)\lambda_f(c)|}{\nu(b)\nu(c)}
 \ll T^{\theta\beta-(1-\theta)\gamma+o(1)}.
\tag{4.845ae}
\]

Apply the product-index Möbius identity (4.845s) to the shortened
lengths \(T^{u-e_1}\) and \(T^{u-e_2}\), with primitive conductor
\(T^\rho\).  Its common-divisor split remains uniformly long:

\[
 \begin{aligned}
 \min(u-e_1,u-e_2)-\rho
 &=u-\max(e_1,e_2)-\rho\\
 &\geq u-\beta-\rho
 =u-\lambda.
 \end{aligned}
\tag{4.845af}
\]

Consequently the Möbius variable still has length at least
\(T^{u-\lambda}\) in every oldclass cell, so the zero-free-region PNT
used in (4.845y) retains arbitrary logarithmic decay.  The
large-common-divisor endpoint, after (4.845ae), is

\[
 \begin{aligned}
 E(\rho,\beta,\gamma,e_1,e_2)
 &=u-\min(e_1,e_2)+\rho
   +\theta\beta-(1-\theta)\gamma\\
 &\leq u+\rho+\theta\beta\\
 &=u+\lambda-(1-\theta)\beta
 \leq u+\lambda.
 \end{aligned}
\tag{4.845ag}
\]

All sums over \(c,\ell,\ell_1,\ell_2\) are divisor sums and hence cost
only \(T^{o(1)}\).  At the critical point
\[
 u=\frac52,\qquad \lambda=1,\qquad \theta=\frac7{64},
\]
(4.845af) is at least \(3/2\), while (4.845ag) is at most \(7/2\).
The worst endpoint is attained only at \(\beta=0\), the primitive
newform cell; every genuine oldclass shift \(\beta>0\) gains
\((57/64)\beta\).  Thus oldclasses preserve the \(7/2\) endpoint and
its arbitrary logarithmic decay in the product-smooth spectral model.
This also remains compatible with the ramified primitive identity from
Section 4.109d, because the latter already restricts its common Möbius
divisor away from \(Q_f\).

The adapter smooth_hecke_oldclass_product_audit records the minimum
split \(3/2\), the newform and worst oldclass endpoint \(7/2\), and the
oldclass saving slope \(57/64\).  It leaves the physical coupled-kernel,
finite-prime-gate, and whole-gate flags false: the exact
Blomer--Milićević formula closes the oldclass normalization only after
one has reached the product-smooth spectral model.


### 4.109f The physical QCT--Bessel kernel has zero-power product bandwidth

The second interface listed after (4.845aa) separates into an elementary
QCT tensorization and an exact Bessel--Mellin identity.  This subsection
closes that smooth-kernel interface, but not the geometric passage from
the entry-weighted QCT orbit to a standard Kuznetsov formula.

For one retained box, the exact kernel
\(\Psi(u,v,\alpha,\beta)\) in (5.13b) of the off-diagonal audit is
compactly supported in four fixed normalized intervals and satisfies

\[
 \|\partial^{\mathbf j}\Psi\|_\infty
 \ll_{\mathbf j,W}(\log T)^{C_{\mathbf j}}.
\]

With
\[
 \widehat\Psi(\boldsymbol\xi)
 =\int_{\mathbb R^4}\Psi(\mathbf x)
   e(-\boldsymbol\xi\cdot\mathbf x)\,d\mathbf x,
\]
Fourier inversion is the exact identity

\[
 \boxed{
 \Psi(\mathbf x)
 =\int_{\mathbb R^4}\widehat\Psi(\boldsymbol\xi)
 e(\xi_1u)e(\xi_2v)e(\xi_3\alpha)e(\xi_4\beta)
 \,d\boldsymbol\xi.}
\tag{4.845ah}
\]

For every fixed seminorm degree \(J\), applying
\(\prod_{j=1}^4(1-(2\pi)^{-2}\partial_{x_j}^2)^{J+1}\) before inversion
gives

\[
 \boxed{
 \int_{\mathbb R^4}
 \prod_{j=1}^4(1+|\xi_j|)^J
 |\widehat\Psi(\boldsymbol\xi)|\,d\boldsymbol\xi
 \ll_{J,W}(\log T)^{C_J}.}
\tag{4.845ai}
\]

Only derivatives of total order at most \(8(J+1)\) occur.  Thus the
additive twists in \(h/H\) and \(\delta/L\), together with the two
entry twists, have an exact weighted nuclear norm of polylogarithmic
size.

There is one more coupling after a standard Kuznetsov formula is
available.  Put \(n=|h\delta|\), and in the notation of
Blomer--Milićević define

\[
 G_n(x)
 :=\left(\frac{4\pi q_1\sqrt n}{x}\right)^{1/2}
 f_\infty\!\left(\frac{4\pi\sqrt n}{xX}\right).
\]

Direct substitution gives its exact Mellin transform

\[
 \boxed{
 \widehat G_n(z)
 =(q_1X)^{1/2}
 \left(\frac{4\pi\sqrt n}{X}\right)^z
 \widehat f_\infty(1/2-z).}
\tag{4.845aj}
\]

For the same-sign Kuznetsov kernel, Mellin Parseval and
\[
 \int_0^\infty J_\nu(x)x^{w-1}\,dx
 =2^{w-1}
 \frac{\Gamma((\nu+w)/2)}
 {\Gamma((\nu-w+2)/2)}
\]
give, on the fixed line \(\Re z=-1/2\),

\[
 \boxed{
 \int_0^\infty J_\nu(x)G_n(x)\frac{dx}{x}
 =\frac1{2\pi i}\int_{(-1/2)}
 \widehat G_n(z)\,2^{-z-1}
 \frac{\Gamma((\nu-z)/2)}
 {\Gamma((\nu+z+2)/2)}\,dz.}
\tag{4.845ak}
\]

For the opposite-sign kernel, the identity
\[
 \int_0^\infty K_\nu(x)x^{w-1}\,dx
 =2^{w-2}\Gamma((w+\nu)/2)\Gamma((w-\nu)/2)
\]
similarly gives

\[
 \boxed{
 \int_0^\infty K_\nu(x)G_n(x)\frac{dx}{x}
 =\frac1{2\pi i}\int_{(-1/2)}
 \widehat G_n(z)\,2^{-z-2}
 \Gamma\!\left(\frac{-z+\nu}{2}\right)
 \Gamma\!\left(\frac{-z-\nu}{2}\right)\,dz.}
\tag{4.845al}
\]

These formulas are first justified with compact truncations in \(x\)
and \(z\), where Fubini is absolute, and then by the Schwartz decay of
\(\widehat f_\infty\) and Stirling's formula.  They hold for the two
fixed sign boxes separately.  If \(t=i\eta\) is exceptional with
\(|\eta|\leq7/64\), every Bessel order in (4.845ak)--(4.845al) has
absolute real part at most

\[
 2|\eta|\leq\frac7{32}<\frac12=-\Re z;
\]
hence the common contour has the fixed margin

\[
 \boxed{\frac12-\frac7{32}=\frac9{32}.}
\tag{4.845am}
\]

The only \(n\)-dependence in (4.845aj) is

\[
 n^{z/2}=|h|^{z/2}|\delta|^{z/2}.
\]

It therefore multiplies the two one-variable factors supplied by
(4.845ah), rather than coupling them.  On \(\Re z=-1/2\), the fixed
real powers are absorbed into the dyadic normalizations, while
\(\Im z\) is a Mellin twist.  Equations (4.845ai) and
(4.845aj)--(4.845al), followed by repeated integration by parts and
Stirling, give arbitrary logarithmic decay outside
\[
 |\boldsymbol\xi|+|\Im z|+|t_f|+k
 \leq(\log T)^{C}.
\]
Inside this range the analytic conductor is
\[
 Q_f(1+|t_f|+|\Im z|+k)^2=T^{\lambda+o(1)}
\]
when \(Q_f\leq T^\lambda\).  Thus the critical level
\(\lambda=1\) used in Sections 4.109d--4.109e is unchanged, and every
separated component is covered by the product-smooth Hecke lemma and
its exact oldclass restoration.  Any polynomial dependence of those
lemmas on the one-variable seminorms is absorbed by taking \(J\) larger
in (4.845ai) and the Möbius-PNT logarithmic exponent larger in
(4.845y).

The adapter physical_qct_hecke_kernel_audit records the four normalized
QCT variables, the fifth Bessel-product variable, derivative-order
slope \(8\), contour \(-1/2\), exceptional margin \(9/32\), and zero
power Mellin bandwidth.  It marks the physical smooth kernel restored
*inside each standard Kuznetsov product component*.  It deliberately
keeps three distinct statements false:

1. no identity has yet transformed the two entry-weighted QCT orbit
   into the required standard Kuznetsov family;
2. the other Möbius entry weights have not yet been retained through
   that transformation; and
3. the signed Type-I level family has not been aggregated.

Accordingly the finite-prime Hecke gate and the whole Möbius gate remain
unproved.


### 4.109g Type-I completion leaves an inverse-scaled Kloosterman index

Apply the finite Möbius identity (4.833) to the
two entry weights.  In one fixed factor box write

\[
 r=Ae,\qquad A=db,\qquad
 s=B\ell,\qquad B=d'b',
\tag{4.845an}
\]

where \(e,\ell\) are the unweighted quotients and the exact inequalities
\(d\leq U,de>U,b\leq V\), together with their right-hand analogues, are
retained in the smooth endpoint weights.  The determinant condition
\((r,s)=1\) implies

\[
 (A,B)=1,\qquad (A,s)=1.
\]

The additional \(q\)-coprimality is a finite one-variable divisor layer
and does not alter the identity below; on the balanced critical face
\(q=T^{o(1)}\) (indeed, only bounded \(q\) occur in each fixed endpoint
box).

Put \(n=h\delta\), let \(E\) be the \(e\)-length, and use
\(\widehat U(\xi)=\int U(x)e(-x\xi)\,dx\).  Poisson summation in the
unweighted quotient is exact:

\[
 \boxed{
 \begin{aligned}
 &\sum_{\substack{e\in\mathbb Z\\(e,s)=1}}
 U(e/E)e\!\left(-\frac{n\overline{Ae}}s\right)\\
 &\qquad=\frac Es\sum_{m\in\mathbb Z}
 \widehat U(mE/s)\,
 S(\overline A m,-n;s).
 \end{aligned}}
\tag{4.845ao}
\]

Indeed finite residue-class Poisson first gives
\[
 \sum_{x\bmod s}^{*}
 e\!\left(\frac{mx-n\overline A\bar x}{s}\right).
\]
The permutation \(y=Ax\bmod s\) changes this residue sum into
\[
 \sum_{y\bmod s}^{*}
 e\!\left(\frac{\overline A m\,y-n\bar y}{s}\right),
\]
which is the Kloosterman sum in (4.845ao).  No estimate and no
completion of a Möbius-weighted variable occurs here: the quotient is
unweighted because the full finite Type-I identity is retained.

At this point the previously claimed geometric adapter fails.  Use
[Kiral--Young, Proposition 2.6](https://arxiv.org/abs/1710.00914).  In
their notation take
\[
 N=BA,\qquad r=B,\qquad s_{\mathrm{KY}}=A.
\]
The allowed moduli for the cusp pair
\((\infty,1/B)\) are exactly
\[
 B\mid s,\qquad(s,A)=1,
\]
Their explicit formula is

\[
 \boxed{
 S_{\infty,1/B}^{(AB)}
   (m,-n;s\sqrt A)
 =S(A m,-n;s),}
\tag{4.845ap}
\]

whereas the exact Poisson residue sum in (4.845ao) is

\[
 \boxed{S(\overline A m,-n;s).}
\tag{4.845ap'}
\]

The two first indices are not interchangeable.  For example, with
\(A=2,s=5,m=n=1\), one has \(\overline A=3\pmod5\) and

\[
 \boxed{
 S(3,-1;5)=-(1+\sqrt5),\qquad
 S(2,-1;5)=\sqrt5-1.}
\tag{4.845ap''}
\]

Thus the allowed-modulus condition matches, but the physical Poisson
sum is not the Kiral--Young cusp Kloosterman orbit.  The former audit
checked only the permutation \(e\mapsto Ae\pmod s\) and then hard-coded
the last equality; (4.845ap'') is a finite counterexample to that step.
The inverse-scaled family is nevertheless reducible by a different
exact identity.  CRT multiplicativity gives

\[
 \boxed{
 S(m,-An;As)
 =c_A(m)S(\overline A m,-n;s),}
\tag{4.845ap_1}
\]

because its local factor modulo \(A\) is
\(S(m\bar s,0;A)=c_A(m\bar s)=c_A(m)\).  On the exact Möbius support,
\(A\mid r\) is squarefree.  If \(g=(A,m)\), then

\[
 \boxed{
 c_A(m)=\mu(A/g)\frac{\varphi(A)}{\varphi(A/g)}\ne0,
 \qquad |c_A(m)|^{-1}\leq1.}
\tag{4.845ap_2}
\]

Therefore the inverse-scaled family

\[
 \sum_{\substack{B\mid s\\(s,A)=1}}
 \frac1s S(\overline A m,-n;s)F_{A,B,m,n}(s/S)
\tag{ISK}_{A,B}
\]

has the exact standard-orbit expansion

\[
 \boxed{
 \mathrm{ISK}_{A,B}
 =\frac{A}{c_A(m)}
 \sum_{j\mid A}\mu(j)
 \sum_{ABj\mid c}\frac1c
 S(m,-An;c)F_{A,B,m,n}(c/(AS)).}
\tag{4.845ap_3}
\]

Indeed \(c=As\) and
\(\mathbf1_{(s,A)=1}=\sum_{j\mid A,\ j\mid s}\mu(j)\).  Thus each
inner sum in (4.845ap_3) is an infinity--infinity Kuznetsov orbit at
level \(ABj\); no division by a possibly zero local factor occurs.
This is the correct geometric repair of (4.845ap), but it introduces
the non-squarefree level family \(ABj\) with \(j\mid A\), whose exponent
can be as large as \(2\alpha+\beta\).

The repaired orbit has an exact scale cancellation.  At the balanced
QCT box let
\[
 R=S=T^3,\qquad |h\delta|=T^5,\qquad
 A=T^\alpha,\qquad B=T^\beta.
\]
Then

\[
 \boxed{
 \begin{array}{c|c}
 \text{quantity}&\log_T(\text{scale})\\ \hline
 E=R/A&3-\alpha\\
 m\text{ after Poisson}=S/E&\alpha\\
 ABj\text{ (spectral level), }j=T^\gamma&\alpha+\beta+\gamma\\
 As\text{ (standard modulus)}&3+\alpha\\
 |mA h\delta|\text{ (Bessel numerator product)}&5+2\alpha\\
 EA\text{ (outer Poisson--lift factor)}&3.
 \end{array}}
\tag{4.845aq}
\]

In particular the exceptional Bessel exponent is
\[
 2(3+\alpha)-(5+2\alpha)=1.
\]
More generally it is \(\rho+\sigma-(h+\ell)\), independent of
\(\alpha\).  Also \(E=R/A\) makes \(EA=R\) exactly.  The inverse
Ramanujan factor has absolute value at most one.

For a fixed finite Type-I allocation, let
\(\Omega_{A,B,q}(c,m,h,\delta)\) denote the retained smooth weight after
the literal substitutions

\[
 s=c/A,\qquad E=R/A,\qquad
 \widehat U(mE/s)=\widehat U(mR/c).
\]

It includes the original endpoint inequalities, mollifier tapers,
ratio/gcd cutoffs, and the four-variable kernel; no variable has been
estimated.  Equations (4.845ao) and (4.845ap_3) give the exact nonzero
mode component

\[
 \boxed{
 \mathfrak S^{\mathrm{lift}}_{q,A,B}
 =R\sum_{j\mid A}\mu(j)
 \sum_{\substack{m\ne0\\h,\delta\ne0}}
 \frac1{c_A(m)}
 \sum_{ABj\mid c}\frac{S(m,-Ah\delta;c)}c
 \Omega_{A,B,q}(c,m,h,\delta).}
\tag{4.845aq_1}
\]

Thus the original coupled-kernel target is now one signed family of
standard Kloosterman sums; on the complete Type allocation it is enough
to prove

\[
 \boxed{
 \left|\sum_{A,B}\frac{\mathfrak S^{\mathrm{lift}}_{q,A,B}}R\right|
 \ll_{C,W}S(\log T)^{-C},\qquad C>7.}
\tag{LISK}_{q}
\]

This is equivalent to the required
\(|\mathfrak S_q[\Psi]|\ll RS(\log T)^{-C}\) for that allocation;
the zero Poisson mode remains in the separately audited main-term
calculation.

The exact new local loss is visible before any conjectural estimate.
Write \(j=T^\gamma\), \(0\leq\gamma\leq\alpha\), and let a residual
Hecke polynomial have physical length \(Y\).  The second Fourier
sequence is supported on indices \(Ay\), so the ordinary spectral large
sieve contains

\[
 \frac{AY}{ABj}=\frac{Y}{Bj}
\]

instead of the base-level factor \(Y/(AB)\).  The excess in the squared
estimate and the required amplitude saving are exactly

\[
 \boxed{
 x_{\mathrm{EVP}}(\alpha,\gamma)=\alpha-\gamma,
 \qquad s_{\mathrm{EVP}}(\alpha,\gamma)
 =\frac{\alpha-\gamma}{2}.}
\tag{4.845aq_2}
\]

The worst cell \(j=1\) requires \(A^{-1/2}\) in amplitude; the endpoint
\(j=A\) requires no extra saving.  This factor is already visible in
the geometric identity (4.845ap_1): after division by \(c_A(m)\), the
Weil scale is \(s^{1/2}\), not \((As)^{1/2}\).  Since the cancellation
is between levels, the accepted local gate must retain the full divisor
sum and the cross pairing between the dense Poisson index and the
sparse product index.  With identical Bessel test at every level, the
required bilinear statement is

\[
 \boxed{
 \begin{aligned}
 &\left|\sum_{j\mid A}\mu(j)
 \int_{\mathscr S_{ABj}(\mathcal T)}
 \left(\sum_{m\asymp M}\frac{b_m}{c_A(m)}\sqrt m\,
 \overline{\rho_\pi(m)}\right)
 \left(\sum_{y\asymp Y}a_y\sqrt{Ay}\,
 \rho_{\pi}(Ay)\right)d\pi\right|\\
 &\qquad\ll_\varepsilon
 (ABMYT)^\varepsilon
 \left(\mathcal T^2+\frac{M}{AB}\right)^{1/2}
 \left(\mathcal T^2+\frac{Y}{AB}\right)^{1/2}
 \left(\sum_m|b_m|^2\sum_y|a_y|^2\right)^{1/2}.
 \end{aligned}}
\tag{EVP}_{A,B}
\]

The measure includes Maaß, holomorphic, and continuous spectra with the
standard Kuznetsov normalizations.  No published theorem has yet been
matched to this signed exact-valuation projector, so
the arbitrary-coefficient \(\mathrm{EVP}_{A,B}\) is not a proved lemma.
It is a sufficient diagnostic, not the accepted physical gate below.
The adapter lifted_kuznetsov_level_cell_audit records (4.845aq_2) with
exact rational arithmetic.

One generic cuspidal local cell can be closed exactly.  Let \(p\mid A\),
let \(f\) be primitive and unramified at \(p\), and assume
\(p\nmid my\).  Put \(\lambda=\lambda_f(p)\) and

\[
 D_p=1-\frac{p|\lambda|^2}{(p+1)^2}.
\]

The Blomer--Milićević orthonormal oldclass formula gives squared
normalization \(p/D_p\) for the \(b=p\) vector.  Adding its cross term
to the \(b=1\) term at indices \(m,py\) gives the exact algebraic
simplification

\[
 \boxed{
 \lambda+\frac p{D_p}
 \left(-\frac{\lambda}{p+1}\right)
 \left(1-\frac{|\lambda|^2}{p+1}\right)
 =\frac{\lambda}{(p+1)D_p}.}
\tag{4.845aq_3}
\]

Since \(|\lambda_f(p)|\leq2p^{7/64}\), the right side is
\(O(p^{-57/64})\), strictly stronger than the required
\(p^{-1/2}\).  At ambient level \(p^2\), the additional \(b=p^2\)
oldvector does **not** have zero coefficient at the first index.  Its
cross term is the negative of (4.845aq_3), so the complete
\(b=1,p,p^2\) oldclass vanishes in this coprime/ramified cell.  The
exact prime-power calculation is recorded below in (4.845aq_8).

The primitive conductor-\(p\) oldspace cancels even more sharply after
raising to ambient level \(p^2\).  Here \(\nu(p)=p\).  With
\(D'_p=1-|\lambda_f(p)|^2/p\), the two oldvectors give

\[
 \boxed{
 \lambda_f(p)+\frac p{D'_p}
 \left(-\frac{\lambda_f(p)}p\right)
 \left(1-\frac{|\lambda_f(p)|^2}p\right)=0.}
\tag{4.845aq_4}
\]

At level \(p\) itself the Steinberg identity
\(|\lambda_f(p)|=p^{-1/2}\) supplies exactly the required local
amplitude saving.  A primitive trivial-central representation of
conductor exponent two has degree-zero local \(L\)-factor, hence its
coefficient at \(py\), \(p\nmid y\), is zero.  The same alternatives
cover the continuous spectrum: the level-one Eisenstein oldspace uses
(4.845aq_3), there is no trivial-nebentypus conductor-\(p\) Eisenstein
newform, and a conductor-\(p^2\) character pair has zero \(p\)-Euler
coefficient.

The two exact identities are checked independently by
unramified_prime_oldspace_cross_factor_identity and
conductor_p_raised_oldspace_cross_identity.  They close the generic
\(p\nmid my\) local cell for all three spectra.  They do not yet prove
\(\mathrm{EVP}_{A,B}\): the cells with \(p\mid my\) must be averaged
with the Ramanujan denominator and multiplied consistently over
\(p\mid A\).

The arbitrary-sequence form \(\mathrm{EVP}_{A,B}\) is stronger than the
physical problem.  Here the sparse coefficient is the fixed
divisor-convolution

\[
 a_y^{H,L}
 =\sum_{h\delta=y}U(h/H)V(\delta/L),
\]

with the exact coupled smooth factors retained by Fourier--Mellin
superposition.  Let \(D=(A,h\delta)\).  Since \(A\) is squarefree, every
condition \(D\mid h\delta\) has the disjoint prime allocation
\(D=D_1D_2\), \((D_1,D_2)=1\), with \(D_1\mid h,D_2\mid\delta\).  Hence
the boundary-aware count is

\[
 \boxed{
 \sum_{h\asymp H}\sum_{\delta\asymp L}
 \mathbf1_{D\mid h\delta}
 \leq
 \sum_{\substack{D_1D_2=D\\(D_1,D_2)=1}}
 \left(\frac{2H}{D_1}+1\right)
 \left(\frac{2L}{D_2}+1\right).}
\tag{4.845aq_5}
\]

Terms with \(D_1>2H\) or \(D_2>2L\) vanish.  On every remaining
allocation the right side is
\(\ll HL D^{-1}4^{\omega(D)}\).  Thus if
\(A=T^\alpha,D=T^d\), the bad-prime density supplies square saving
\(d\), while (4.845aq_3)--(4.845aq_4) supply generic-prime amplitude
saving \((\alpha-d)/2\).  The exact power balance is

\[
 \boxed{
 \frac{\alpha-d}{2}+\frac d2=\frac\alpha2.}
\tag{4.845aq_6}
\]

This recovers the entire power required in (4.845aq_2), including the
short-interval boundary cells.  It remains to verify that no ramified
oldclass matrix consumes that saving.  This follows by the same finite
basis formula.  Put \(a=v_p(m)\),
\(k=v_p(y)\), and let \(\lambda_j=\lambda_f(p^j)\) for an unramified
primitive form.  When \(a=0\), the \(b=1,p\) cross factor at the second
index \(p^{k+1}y\) is exactly

\[
 \boxed{
 \lambda_{k+1}+\frac p{D_p}
 \left(-\frac{\lambda_1}{p+1}\right)
 \left(\lambda_k-\frac{\lambda_1\lambda_{k+1}}{p+1}\right)
 =\frac{\lambda_1\lambda_k/(p+1)-\lambda_{k-1}}{D_p},}
\tag{4.845aq_7}
\]

with \(\lambda_{-1}=0\).  This is just
\(\lambda_{j+1}=\lambda_1\lambda_j-\lambda_{j-1}\).  For \(k=0\)
it is (4.845aq_3); for \(k\geq1\), Kim--Sarnak and the exact
\(p^{-k/2}\) amplitude density give

\[
 p^{(k-1)7/64}p^{-k/2}
 =p^{-1/2}p^{-(k-1)25/64}.
\]

The squarefull oldvector is supplied by the general
[Blomer--Milićević basis, Lemma 2](https://arxiv.org/abs/1404.7845),
not by the squarefree specialization used in
(4.845aq_3).  Put
\(C_{p^2}^2=(D_p(1-p^{-2}))^{-1}\).  In normalized Fourier
coefficients its local polynomial is
\[
 u_{p^2}(a)
 =C_{p^2}\left(p^{-1}\lambda_a-lambda_1\lambda_{a-1}
                    +p\lambda_{a-2}\right),
 \qquad \lambda_{-1}=\lambda_{-2}=0.
\]
Consequently, at the unit first index and the second index of
valuation \(k+1\),

\[
 \boxed{
 u_{p^2}(0)u_{p^2}(k+1)
 =-\frac{\lambda_1\lambda_k/(p+1)-\lambda_{k-1}}{D_p},
 \qquad
 \sum_{b=1,p,p^2}u_b(0)u_b(k+1)=0.}
\tag{4.845aq_8}
\]

Thus (4.845aq_7) is exactly the level-\(p\) remainder, while the full
ambient-level-\(p^2\) oldclass cancels.  The checker
`unramified_level_p_squared_cross_identity` evaluates both sides for
every requested \(k\); it replaces the incorrect claim that the
\(p^2\) vector vanished separately.

If \(a\geq1\), then
\(|c_p(m)|^{-1}=(p-1)^{-1}\).  In the \(b=p\) vector its normalization
\(p/D_p\) cancels this denominator and leaves the leading product
\(\lambda_{a-1}\lambda_k\).  The two valuation densities give

\[
 p^{(a+k-1)7/64}p^{-(a+k)/2}
 =p^{-1/2}p^{-(a+k-1)25/64}.
\]

For the \(b=p^2\) vector, (4.845aq_8) gives the exact three-term
coefficient.  Its potentially largest product is
\(p^2\lambda_{a-2}\lambda_{k-1}\); it occurs only for
\(a\geq2,k\geq1\).  Division by \(|c_p(m)|=p-1\), followed by the
two amplitude densities \(p^{-a/2}p^{-k/2}\), bounds this term by
\[
 p^{1+(a+k-3)7/64-(a+k)/2}
 \leq p^{-1/2}p^{-(a+k-3)25/64}.
\]
For completeness, after the Ramanujan denominator and the two density
factors, the nine exponents (rows in the order
\(p^{-1}\lambda_a,-\lambda_1\lambda_{a-1},p\lambda_{a-2}\),
columns in the analogous order at \(k+1\)) are

\[
\begin{pmatrix}
-3+(a+k+1)\theta-(a+k)/2&
-2+(a+k+1)\theta-(a+k)/2&
-1+(a+k-1)\theta-(a+k)/2\\
-2+(a+k+1)\theta-(a+k)/2&
-1+(a+k+1)\theta-(a+k)/2&
(a+k-1)\theta-(a+k)/2\\
-1+(a+k-1)\theta-(a+k)/2&
(a+k-1)\theta-(a+k)/2&
1+(a+k-3)\theta-(a+k)/2
\end{pmatrix}.
\]

The third row requires \(a\geq2\), and the third column requires
\(k\geq1\).  With \(0\leq\theta<1/2\), every entry is at most
\(-1/2\); equality can occur only in the bottom-right entry at
\((a,k)=(2,1)\).  This supplies the promised exact local inequality,
including all nine squarefull cross products.  The conductor-\(p\) and
conductor-\(p^2\) cases
use (4.845aq_4) and the degree-zero local factor, respectively.  For
Eisenstein oldvectors the unramified coefficients satisfy
\(|\lambda_j|\leq j+1\), and the ramified character-pair coefficient at
positive p-valuation is zero, so the same bounds hold with
\(7/64=0\).

The local alternatives multiply over squarefree \(A\), and they prove
the required power exponent \(A^{-1/2+o(1)}\).  That statement is not
yet strong enough for the logarithmic endpoint.  Indeed, on a fixed
bad-gcd cell the square-density estimate contributes
\(D^{-1}4^{\omega(D)}\), while the generic primes contribute the
square saving \((A/D)^{-1}\).  Summing the present positive majorants
over \(D\mid A\) gives exactly

\[
 \boxed{
 \sum_{D\mid A}
  \frac{4^{\omega(D)}}D\frac D A
  =\frac{5^{\omega(A)}}A.}
\tag{4.845cy}
\]

The amplitude residual \(5^{\omega(A)/2}\) is \(A^{o(1)}\), but it is
not bounded by a fixed power of \(\log T\) uniformly for \(A\leq T^3\).
For the primorial \(A_y=\prod_{p\leq y}p\), the prime number theorem
gives
\[
 \log 5^{\omega(A_y)/2}\sim\frac{\log5}{2}\frac y{\log y},
 \qquad
 \log(\log A_y)^C\sim C\log y,
\]
so the former exceeds the latter for every fixed \(C\).

Therefore the physical divisor-convolution exact-valuation projector is
covered only at the power-exponent level.  A proof still has to retain
orthogonality or Möbius cancellation across the \(D\)-cells and replace
(4.845cy) by a polylogarithmic square bound.  The arbitrary-sequence
statement \(\mathrm{EVP}_{A,B}\) remains unproved as well.  The adapters
unramified_oldspace_cross_prime_power_identity and
physical_exact_valuation_projector_audit record (4.845aq_7) and this
case split; the latter now distinguishes power-exponent coverage from
the unproved polylogarithmic tensor gate.  The adapter
lifted_projector_gcd_partition_audit separately records the power
identity (4.845aq_6).

Before spectral transformation, the raw Poisson normalization and its
dual length still cancel:

\[
 \boxed{
 \frac ES\sum_{m\ne0}
 |\lambda_f(|m|)\widehat U(mE/S)|
 \ll (Q_fS)^{o(1)},\qquad
 \frac ES\cdot\frac SE=1.}
\tag{4.845ar}
\]

For \(m\ne0\), (4.845ar) uses only
\(\sum_{m\asymp M}|\lambda_f(m)|\ll M(Q_fM)^{o(1)}\); it never invokes
the pointwise \(m^\vartheta\) bound.  This raw identity alone does not
normalize the spectral side of (4.845ap_3): the Bessel transform, the
Fourier-coefficient normalization at level \(ABj\), and the sum over
\(j\mid A\) must be retained together.  In particular the former
\(\mathrm{SLF}_{\alpha,\beta}\) target, derived under the false
level-\(AB\) cusp adapter, is no longer an accepted physical gate.  The
power-exponent exact-valuation calculation is now available.  The
remaining gate in this sector is the polylogarithmic tensor inequality
PEVP\(_{A,B}\), followed by the outer \(\mathrm{LISK}_q\) aggregation
with all ratio/gcd and \(q\)-layers restored.

The adapter type_i_atkin_lehner_cusp_audit records both the rejected
Kiral--Young match and the exact CRT product-modulus repair.  It marks
the physical Type-I/Type-I reduction to a finite standard Kuznetsov
level family true, but keeps the old cusp-pair identity false.  The
local calculation above restores the base-level large-sieve *power
exponent* uniformly for \(ABj\) and the ramified second index \(An\);
Section 4.109v combines it with the orientation inequalities.  The
polylogarithmic tensor bound, outer factor
\(R/c_A(m)\), ratio/gcd layers, and \(q\)-aggregation remain separate.


### 4.109h The inverse-zeta zero does not by itself prove level reciprocity

The two retained shift variables do give more structure than an
arbitrary spectral sequence.  At every unramified prime, write

\[
 \lambda_f(p^{j+1})
 =\lambda_f(p)\lambda_f(p^j)-\lambda_f(p^{j-1}).
\]

Then, coefficient by coefficient,

\[
 \lambda_f(p^{a+b})
 =\lambda_f(p^a)\lambda_f(p^b)
  -\mathbf 1_{a,b\geq1}\lambda_f(p^{a-1})\lambda_f(p^{b-1}),
\]

and hence, initially for \(\Re u,\Re v>1\),

\[
 \boxed{
 \sum_{h,\delta\geq1}
 \frac{\lambda_f(h\delta)}{h^u\delta^v}
 =\frac{L(u,f)L(v,f)}{\zeta^{(Q_f)}(u+v)}.}
\tag{4.845as}
\]

Here \(\zeta^{(Q_f)}\) omits the Euler factors at primes dividing the
primitive conductor.  The finite checker
hecke_double_dirichlet_local_identity verifies the displayed Hecke
coefficient identity on every requested rectangle; it is a regression
witness for the algebra, not a substitute for Euler-product
continuation.

It is tempting to set \(u=v=1/2\) and declare that the pole of
\(\zeta(u+v)\) kills the spectral family.  This is invalid for the
continuous spectrum.  For the unramified Eisenstein eigenvalues
\(\lambda_t(n)\), the corresponding factor is

\[
 \boxed{
 D_t(u,v)=
 \frac{\zeta(u+it)\zeta(u-it)
       \zeta(v+it)\zeta(v-it)}{\zeta(u+v)}.}
\tag{4.845at}
\]

When the \(t\)-contour crosses the pole
\(t=-i(1-u)\), its residue contains
\[
 \frac{\zeta(1+v-u)}{\zeta(u+v)}.
\]
Writing \(u=1/2+a\), \(v=1/2+b\), its normal-crossing leading model is

\[
 \boxed{
 \frac{\zeta(1+b-a)}{\zeta(1+a+b)}
 =\frac{a+b}{b-a}\bigl(1+O(|a|+|b|)\bigr).}
\tag{4.845au}
\]

Thus the inverse-zeta zero and the transverse Eisenstein pole have the
same order, and their quotient has no path-independent value at
\((a,b)=(0,0)\).  Only the *completed sum* of both contour residues,
the zero frequencies, and the ramified local factors can be continued
to the central point.  A coefficientwise cancellation claim is false.

Three published reciprocity formulae were compared term by term.

1. [Andersen--Kiral](https://arxiv.org/abs/1801.06089) averages the
   square of a degree-four Rankin--Selberg \(L(s,g\times f)\), with a
   fixed cuspidal \(g\), and in its stated level-reciprocity theorem
   exchanges distinct prime parameters.  Replacing \(g\) by Eisenstein
   data introduces polar terms absent from their theorem.
2. [Blomer--Khan](https://arxiv.org/abs/1706.01245) proves reciprocity
   for \(L(s,f\times F)L(w,f)\).  With the minimal \(GL(3)\)
   Eisenstein series this is the degree-eight fourth moment
   \(L(1/2,f)^4\), not the degree-four product in (4.845as); its theorem
   includes a completed main term assembled from GL(3) residues and
   Eisenstein-contour residues.
3. [Khan](https://arxiv.org/abs/2401.01057) directly transforms a zeta
   twisted second moment, but the stated theorem assumes distinct odd
   prime twists and a Gaussian archimedean weight, and the dual family
   is a Dirichlet-character second moment.  It is not a composite-level
   Atkin--Lehner spectral-family estimate.

Consequently none of these is a literal adapter for
SLF\(_{\alpha,\beta}\).  On a factor box
\(A=T^\alpha,B=T^\beta\), the exact missing estimate remains

\[
 \boxed{
 \text{completed signed level family}
 \ \ll_{C,W}\
 T^{3/2+(\alpha+\beta)/2}(\log T)^{-C},
 \qquad \alpha+\beta\leq1.}
\tag{4.845av}
\]

The completed expression must include the paired Eisenstein residues
from (4.845at), all ramified factors at \(AB\), and the oldclass cusp
coefficients.  The right side requires a half-level saving
\((\alpha+\beta)/2\) over absolute aggregation and arbitrary
logarithmic decay on \(\alpha+\beta=1\).  Deriving such a composite
smooth second-moment reciprocity identity is a viable new route; it has
not yet been proved.  The adapter
eisenstein_second_moment_reciprocity_audit therefore keeps the signed
level-family, Type-II, and whole Möbius gates false.


### 4.109i Product-Hecke large sieve closes the cuspidal Type-I/Type-I gate

The level-reciprocity gate in Sections 4.109g--4.109h is unnecessary
once the product-index identity (4.845s) is combined with the ordinary
spectral large sieve *before* the common-divisor variable is estimated.
This ordering was not covered by the fixed-index calculation (4.845b):
there the two indices still had length \(T^{5/2}\), whereas here their
residual lengths are at most the ambient level.

Fix \(A=T^\alpha\), \(B=T^\beta\), put \(Q=AB\), and use reciprocity to
complete the quotient on the side with the smaller Type-I divisor.  If

\[
 \eta=\min(\alpha,\beta),\qquad
 m\ll T^\eta(\log T)^C,
\]

then the Atkin--Lehner cusp identity (4.845ao)--(4.845ap) is unchanged,
with \(A,B\) interchanged when \(\beta<\alpha\).  Let \(H=T^{5/2}\)
denote either product-variable length.  In (4.845t), split the common
divisor \(c\) at \(H/Q\).  The small-\(c\) portion has the arbitrary
logarithmic decay of (4.845w).  In the remaining portion,

\[
 c\asymp C\geq H/Q,\qquad Y=H/C\leq Q.
\]

For the full Maaß, holomorphic, and Eisenstein spectrum at level \(Q\),
the spectral large sieve, in the Fourier-coefficient normalization used
by Kuznetsov, is

\[
 \boxed{
 \int_{\mathscr S_Q(\mathcal T)}
 \left|\sum_{n\asymp Y}a_n\sqrt n\,\rho_{\pi,\infty}(n)\right|^2
 d\pi
 \ll_\varepsilon
 (QY\mathcal T)^\varepsilon
 \left(\mathcal T^2+\frac YQ\right)
 \sum_n|a_n|^2.}
\tag{4.845aw}
\]

This is the Deshouillers--Iwaniec inequality in the form stated as the
spectral-large-sieve lemma in
[Blomer--Milićević](https://arxiv.org/abs/1404.7845).  The physical
Bessel--Mellin tensorization from Section 4.109f restricts
\(\mathcal T\) to a power of \(\log T\), so the parenthesis in
(4.845aw) has power exponent \(\max(0,\log_T(Y/Q))=0\).

Multiplication by the Poisson Hecke index does not introduce a
pointwise Ramanujan factor on a primitive cuspidal coefficient list.
At unramified primes,

\[
 \lambda_\pi(m)\lambda_\pi(n)
 =\sum_{r\mid(m,n)}\lambda_\pi(mn/r^2).
\]

If \(b_k\) is the resulting coefficient sequence, then for each fixed
\(r\mid m\) the map \(n\mapsto mn/r^2\) is injective.  Cauchy over
\(r\mid m\) gives

\[
 \sum_k|b_k|^2\leq\tau(m)^2\sum_n|a_n|^2,\qquad
 \operatorname{supp}b\subset[1,4mY].
\]

The degree-one ramified local factors only delete terms from this
divisor expansion.  After the finite oldclass shifts from Section
4.109e, the same estimate holds with a divisor-power loss, hence with
subpower cost.  Applying (4.845aw) to the multiplied first factor and
the unmultiplied second factor, then applying Cauchy in the complete
spectral measure, gives for each fixed common divisor \(c\)

\[
 \boxed{
 \int_{\mathscr S_Q(\mathcal T)}
 |\rho_\pi(1)|^2
 |\lambda_\pi(m)A_{\pi,1}(H/c)A_{\pi,2}(H/c)|\,d\pi
 \ll
 T^{o(1)}Y\left(1+\frac{mY}{Q}\right)^{1/2}.}
\tag{4.845ax}
\]

For cusp forms there is no positivity loss from the second cusp.  By
[Kiral--Young, Lemma 2.5](https://arxiv.org/abs/1710.00914), the full
oldclass Fourier-coefficient lists at an Atkin--Lehner cusp are a
signed permutation of their lists at infinity.  For the continuous
spectrum the Atkin--Lehner operator is unitary, so changing the
orthonormal Eisenstein basis preserves the squared norm in (4.845aw).
This basis change alone does not factor a ramified Eisenstein
level-oldvector coefficient at index \(mn\); that separate issue is
audited in Section 4.109k.
The total variation of the physical nuclear measure is polylogarithmic
by (4.845ai).

The small-common-divisor range uses a different ledger.  The individual
functional-equation estimate (4.845v) and
\(c\leq H/(Q(\log T)^B)\) give arbitrary logarithmic decay after the
\(c\)-sum.  Estimating the remaining \(\lambda_\pi(m)\) there by
Kim--Sarnak costs at most \(M^{7/64}\).  Relative to the SLF target its
power margin is

\[
 \frac{\alpha+\beta}{2}
 -\frac{7}{64}\min(\alpha,\beta)>0
\]

whenever the level has a nonzero power exponent.  If
\(\alpha=\beta=0\), then \(M=T^{o(1)}\) and arbitrary logarithmic decay
absorbs the subpower local factors.  Thus this complementary range is
also covered; no logarithm is used to absorb a fixed positive power.

Now sum (4.845ax) over \(c\asymp C\).  Since \(CY=H\) and \(Y\leq Q\),

\[
 \boxed{
 \sum_{c\asymp C}\int_{\mathscr S_Q}
 |\rho_\pi(1)|^2
 |\lambda_\pi(m)A_{\pi,1}(H/c)A_{\pi,2}(H/c)|\,d\pi
 \ll T^{o(1)}H\sqrt{1+m}.}
\tag{4.845ay}
\]

The Poisson normalization is \(M^{-1}\) for \(m\ll M=T^\eta\), so
averaging (4.845ay) over \(m\) has the same worst power \(HM^{1/2}\).
The previous pointwise product bound was \(HQ\).  Thus the fixed-level
saving is \(Q/M^{1/2}=T^{\alpha+\beta-\eta/2}\).  Subtracting it from
the absolute level aggregation in
\(\mathrm{SLF}_{\alpha,\beta}\) gives

\[
 \boxed{
 \begin{aligned}
 E_{\rm new}&=\frac32+\frac12\min(\alpha,\beta),\\
 E_{\rm SLF}&=\frac32+\frac{\alpha+\beta}{2},\\
 E_{\rm SLF}-E_{\rm new}
 &=\frac12\max(\alpha,\beta).
 \end{aligned}}
\tag{4.845az}
\]

Every nontrivial power-scale cuspidal Type-I/Type-I box therefore has a
fixed power margin.  At \(\alpha=\beta=0\), the arbitrary logarithmic
decay from (4.845w)--(4.845z) supplies the endpoint decay.  The interface
product_hecke_spectral_large_sieve_audit records the threshold
\(H/Q\), multiplied support \(mY\), saving \(Q/\sqrt m\), and the
margin in (4.845az).

This closes the Maaß and holomorphic Type-I/Type-I contribution, not
the full sector: ramified Eisenstein oldvectors remain open.  The
Type-II sectors additionally contain two genuinely bilinear Möbius
factors after Cauchy and require the audit below.


### 4.109j The Type-II residual is a closed level square

The same ordering applies to most Type-II boxes.  Expanding the
truncated divisor coefficient is the finite identity

\[
 c_U(a)\mu(b)
 =\sum_{\substack{d\mid a\\d\leq U}}\mu(d)\mu(b).
\]

For a fixed divisor-allocation box write

\[
 r=(db)e=Ae,\qquad s=(d'b')\ell=B\ell.
\tag{4.845ba}
\]

The variables \(e,\ell\) are unweighted.  Therefore Poisson summation,
the Kloosterman identity (4.845ao), and the Atkin--Lehner cusp formula
(4.845ap) apply after the displayed finite allocation.  The distinction
from Type I is the level range: because \(b,b'>V=T\) and
\(d,d'\leq U=T\), the Type-II factor polytopes have

\[
 A=T^\alpha,\qquad B=T^\beta,\qquad
 1\leq\alpha,\beta\leq3.
\]

Put \(Q=AB=T^{\alpha+\beta}\), \(H=T^{5/2}\), and complete the quotient
on the side with \(\eta=\min(\alpha,\beta)\).  The Poisson index has
length \(M=T^\eta\).  In the common-divisor decomposition (4.845t), the
largest residual Hecke-polynomial length is

\[
 \boxed{Y\leq\min(H,Q)
 =T^{\min(5/2,\alpha+\beta)}.}
\tag{4.845bb}
\]

Applying (4.845aw)--(4.845ay), the only remaining positive-power
large-sieve factor is the square root of \(1+MY/Q\).  Define

\[
 x(\alpha,\beta)
 :=\left(\min(\alpha,\beta)
 +\min(5/2,\alpha+\beta)-\alpha-\beta\right)_+.
\]

Replacing the former \(HQ\) product bound by the fixed-level bound and
restoring the absolute \(A,B\)-box count gives

\[
 \boxed{
 E_{\rm PHLS}(\alpha,\beta)
 =\frac32+\frac{x(\alpha,\beta)}2.}
\tag{4.845bc}
\]

The normalized QCT target is exponent \(2\).  Eliminating the two
minima gives, on \(1\leq\alpha,\beta\leq3\),

\[
 \boxed{
 x(\alpha,\beta)\geq1
 \quad\Longleftrightarrow\quad
 1\leq\alpha\leq\frac32,\qquad
 1\leq\beta\leq\frac32.}
\tag{4.845bd}
\]

Outside this closed square, (4.845bc) has a fixed power saving.  On the
boundary \(x=1\), no logarithmic saving has yet been retained.  In the
interior the deficit is \((x-1)/2\), maximized at

\[
 (\alpha,\beta)=(5/4,5/4),\qquad
 x=5/4,\qquad E_{\rm PHLS}-2=1/8.
\]

The interface high_level_product_hecke_spectral_audit implements the
affine branches with Fraction arithmetic.  This is a primal-only
ledger: it isolates the exact square left by that estimate and does not
declare the Type-II or whole Möbius gate closed.


### 4.109k Functional-equation duality removes the cuspidal Type-II square

The \(1/8\) residual in Section 4.109j is an artifact of always feeding
the primal Hecke polynomial to the large sieve for the *cuspidal*
spectrum.  The completed standard \(\mathrm{GL}(2)\) functional
equation provides a reciprocal-length polynomial there.

Let \(f\) be a primitive Maaß or holomorphic cusp form of conductor
\(q_0\mid Q\), and let

\[
 A_f(Y;W)=\sum_{n\geq1}\lambda_f(n)W(n/Y).
\]

Mellin inversion on \(\Re s>1\), the exact completed functional
equation, the change of variable \(w=1-s\), and inverse Mellin
inversion give

\[
 \boxed{
 A_f(Y;W)
 =\varepsilon_f\frac{Y}{\sqrt{q_0}}
 \sum_{n\geq1}\overline{\lambda_f(n)}
 \widetilde W_{t_f}\!\left(\frac{nY}{q_0}\right).}
\tag{4.845be}
\]

The contour shift crosses no pole because \(L(s,f)\) is entire.  The
transform is defined by the exact gamma quotient.  Repeated Stirling,
together with the spectral truncation in Section 4.109f, gives rapid
decay outside \(n\ll(q_0/Y)(\log T)^C\).  Its coefficient energy is

\[
 \left(\frac{Y}{\sqrt{q_0}}\right)^2\frac{q_0}{Y}=Y,
\]

the same as the primal polynomial.  For fixed Mellin frequency, the
\(t_f\)-dependent gamma quotient remains in the spectral test weight;
the Mellin integral has polylogarithmic weighted total variation.

Let \(m\ll M\) be the Poisson Hecke index and retain the ambient-level
normalization \(Q=AB\).  Applying (4.845aw) after the Hecke relation to
the primal and dual forms of one polynomial gives respectively

\[
 \boxed{
 1+\frac{mY}{Q},
 \qquad
 1+\frac{mq_0}{YQ}.}
\tag{4.845bf}
\]

Use the primal form for \(Y\leq\sqrt{q_0}\) and (4.845be) for
\(Y>\sqrt{q_0}\).  Uniformly in every common-divisor block,

\[
 \boxed{
 \min\!\left(\frac{mY}{Q},\frac{mq_0}{YQ}\right)
 \leq\frac{m\sqrt{q_0}}Q.}
\tag{4.845bg}
\]

Completion was chosen on the shorter level-factor side, so

\[
 m\leq T^{\min(\alpha,\beta)+o(1)},\qquad
 q_0\leq Q=T^{\alpha+\beta},
\]

and therefore

\[
 \log_T\frac{m\sqrt{q_0}}Q
 \leq\min(\alpha,\beta)-\frac{\alpha+\beta}{2}\leq0.
\]

The cuspidal and holomorphic versions of (4.845ax) have no
positive-power large-sieve excess.  Summing over the common divisor
gives \(HT^{o(1)}\), and the level-box ledger is

\[
 \boxed{
 E_{\rm cusp/holo}=\frac32,\qquad
 E_{\rm target}=2,\qquad
 E_{\rm target}-E_{\rm cusp/holo}=\frac12.}
\tag{4.845bh}
\]

Oldclasses do not alter this cuspidal inequality.  Split by the
underlying primitive conductor \(q_0\mid Q\), apply (4.845be) to each
primitive coefficient list, and insert the finite
Blomer--Milićević shifts.  The conductor and shift allocations cost
\(Q^{o(1)}\); their coefficient energies have the divisor-square bound
used after (4.845aw); and Kiral--Young's signed permutation moves the
second-cusp norm back to infinity.

The same conclusion does **not** follow for the continuous spectrum.
Squarefree \(Q\) forces the inducing character in the adelic
Eisenstein parametrization to be trivial, but level-oldvectors remain.
The exact coefficient formula in
[Blomer--Khan, Section 2.2](https://arxiv.org/abs/1706.01245) exposes
the obstruction.  Specialize it to \(Q=M=p\) prime and suppress factors
common to all indices.  The remaining local coefficient is

\[
 F_{p,t}(n)
 =p^{-1/2}n^{it}
 \sum_{\delta\mid(p,n)}\delta\mu(p/\delta)
 \sum_{cf=n/\delta}c^{-2it}.
\]

Consequently

\[
 \boxed{
 F_{p,t}(1)=-p^{-1/2},\qquad
 F_{p,t}(p)=p^{-1/2}p^{it}(p-1-p^{-2it}),\qquad
 \left|\frac{F_{p,t_p}(p)}{F_{p,t_p}(1)}\right|=p-2,
 \quad t_p=\frac{\pi}{\log p}.}
\tag{4.845bi}
\]

Thus the ramified oldvector ratio is not \(\tau(p)\)-bounded; it grows
linearly in \(p\).  The absolute estimate
\(\rho_{\chi,M,Q}(n,t)\ll_\varepsilon
((1+|t|)Qn)^\varepsilon(M_1M_2)^{1/2}Q^{-1/2}\)
from the same source does not repair this step, because it is not a
bound for the ratio to the first Fourier coefficient and cannot be
pulled outside the spectral polynomial.  Applying the large sieve
directly retains support \(mY\), hence retains the square (4.845bd) in
this part of the spectrum.

The interface primal_dual_product_hecke_spectral_audit therefore
records the fixed \(1/2\) margin only for Maaß and holomorphic cusp
forms.  It records the exact prime-oldvector witness \(p=5\), ratio
\(3\), and keeps the continuous-spectrum, all-sector, finite-prime,
transform-tail, and whole-Möbius gates false.  The next local theorem
must prove a ramified Eisenstein dispersion/reciprocity estimate giving
arbitrary logarithmic decay on the boundary of (4.845bd) and at most
\(T^{1/8}\) saving at its center.  The complete ratio/gcd allocations,
dyadic and \(q\)-sums, and all AFE and transform tails also remain to be
restored before any global asymptotic can be asserted.


### 4.109l The same-cusp Eisenstein projector localizes the loss

The individual oldvector witness (4.845bi) does not by itself show that
a same-cusp Eisenstein kernel is large.  If both Fourier coefficient
lists are evaluated at infinity, the oldvector label can be summed
before taking absolute values, and at squarefree level this diagonal
oldspace projector factorizes prime by prime.

Continue with \(Q=p\) prime and put \(X=p^{-2it}\).  In the notation of
the exact Blomer--Khan coefficient formula, the two local oldvector
coefficient polynomials, after removing the scattering and phase
factors common to both oldvectors, are \(1\) and

\[
 \boxed{
 B_{p,k}(X)
 :=p\sum_{0\leq j<k}X^j-\sum_{0\leq j\leq k}X^j
 =(p-1)\sum_{0\leq j<k}X^j-X^k,}
\tag{4.845bj}
\]

where \(k=v_p(n)\); the first sum is empty for \(k=0\), so
\(B_{p,0}=-1\).  The squarefree normalization
\(\widetilde{\mathfrak n}(M)\) is independent of whether \(M=1\) or
\(M=p\).  Hence the sum of the two normalized oldvector products at
valuations \(k,\ell\) is exactly the Laurent polynomial

\[
 \boxed{
 \mathcal P_{p,t}(k,\ell)
 =\frac1p+\frac1{p^2}
 B_{p,k}(X)B_{p,\ell}(X^{-1}).}
\tag{4.845bk}
\]

For the first three valuation pairs this gives

\[
 \boxed{
 \begin{aligned}
 \mathcal P_{p,t}(0,0)
   &=\frac{p+1}{p^2},\\
 \mathcal P_{p,t}(0,1)
   &=\frac{1+X^{-1}}{p^2},\\
 \mathcal P_{p,t}(1,1)
   &=\frac{p^2-p+2-(p-1)(X+X^{-1})}{p^2}.
 \end{aligned}}
\tag{4.845bl}
\]

Thus the \(p-2\) growth of one shifted vector cancels after the
oldspace sum whenever exactly one Fourier index is divisible by \(p\):
the projector then gains a full factor \(p^{-1}\) over its natural
\(p^{-1}\) scale.  A positive local loss can survive only when both
indices are ramified.

For arbitrary \(k,\ell\), (4.845bj) and \(|X|=1\) give
\[
 |B_{p,k}(X)|\leq (p-1)k+1.
\]
If \(\min(k,\ell)=0\), substitution into (4.845bk) is
\(O((k+\ell+2)/p)\); if \(k,\ell\geq1\), it is
\(O((k+1)(\ell+1))\).  Multiplying the local bounds for squarefree
\(Q\), and absorbing the valuation divisor factors and the common
inverse-\(L\) normalization into \(T^\varepsilon\), yields

\[
 \boxed{
 \left|\mathcal P_{Q,t}(m,n)\right|
 \ll_\varepsilon
 (Qmn(1+|t|))^\varepsilon
 \frac{(m,n,Q)}{Q}.}
\tag{4.845bm}
\]

This is the correct same-cusp replacement for the false attempt to
bound every ramified oldvector ratio separately.  It is **not** yet the
physical Kuznetsov projector in (4.845ap): that formula pairs infinity
with the Atkin--Lehner cusp \(1/B\).  The physical kernel contains the
Atkin--Lehner matrix between the two coefficient lists.  Unitarity
preserves their separate squared norms but does not identify this
cross-cusp matrix coefficient with (4.845bk).

The interface eisenstein_oldspace_projector_audit evaluates
(4.845bk) as an exact Laurent polynomial.  At \(p=5\) it records the
individual ratio \(3\), the mixed projector
\((1+X^{-1})/25\), and the common-ramification projector.  It marks the
prime-by-prime same-cusp factorization and its gcd-over-level majorant
proved, while leaving the Atkin--Lehner cross-cusp projector, physical
gcd aggregation, continuous-spectrum gate, and whole Möbius gate false.


### 4.109m The Poisson average absorbs common ramification in the same-cusp model

The gcd in the same-cusp majorant (4.845bm) costs no positive power
after the normalized nonzero Poisson-frequency average.  Put
\(g=(n,Q)\).  The elementary
divisor identity

\[
 \boxed{
 (m,g)=\sum_{d\mid(m,g)}\varphi(d)}
\tag{4.845bn}
\]

is exact.  Therefore, for every integer \(M\geq1\),

\[
 \begin{aligned}
 \sum_{M<m\leq2M}(m,g)
 &=\sum_{d\mid g}\varphi(d)
   \#\{M<m\leq2M:d\mid m\}\\
 &\leq
 \sum_{\substack{d\mid g\\d\leq2M}}
 \varphi(d)\left(\frac Md+1\right)\\
 &\leq 3M\tau(g).
 \end{aligned}
\]

In the last line, \(\varphi(d)\leq d\) and \(d\leq2M\) are applied to
each nonempty divisor class.  Hence

\[
 \boxed{
 \frac1M\sum_{M<m\leq2M}
 \frac{(m,n,Q)}Q
 \leq\frac{3\tau((n,Q))}{Q}
 \ll_\varepsilon \frac{(nQ)^\varepsilon}{Q}.}
\tag{4.845bo}
\]

The same conclusion holds for every fixed smooth dyadic Poisson weight,
with its sup norm multiplying the right side.  Thus the same-cusp
projector's common-ramification factor has zero power cost.  This does
not apply (4.845bo) to the physical cross-cusp projector; its local
Atkin--Lehner matrix has not yet been inserted.

What remains in the continuous spectrum is archimedean rather than
finite-prime: Mellin inversion of
\(\zeta(s+it)\zeta(s-it)\) crosses the two poles
\(s=1\pm it\).  The resulting residues must be combined with the
Poisson zero mode and the paired residues already isolated in
(4.845at)--(4.845au).  Only after that completed expression is formed
may the reciprocal-length transform be used.  This residue pairing is
not proved here.

The interface eisenstein_common_ramification_average_audit checks
(4.845bn) by exact finite totient expansion and records the explicit
\(3M\tau(g)\) upper bound.  It marks only the same-cusp normalized
Poisson gcd aggregation proved, while leaving the physical cross-cusp
aggregation, completed residue pairing, continuous-spectrum gate, and
whole Möbius gate false.


### 4.109n Pole subtraction dualizes the Eisenstein polynomial

After Sections 4.109l--4.109m, the remaining distinction between a
cuspidal functional equation and the continuous spectrum is explicit:
the Eisenstein Dirichlet series has poles.  They can be isolated before
dualization.

For
\[
 \widehat W(s)=\int_0^\infty W(x)x^{s-1}\,dx,\qquad
 \lambda_t(n)=\sum_{ab=n}(a/b)^{it},
\]
put
\[
 A_t(Y;W)=\sum_{n\geq1}\lambda_t(n)W(n/Y).
\]
The completed product

\[
 \boxed{
 \Xi_t(s):=\pi^{-s}
 \Gamma\!\left(\frac{s+it}{2}\right)
 \Gamma\!\left(\frac{s-it}{2}\right)
 \zeta(s+it)\zeta(s-it),
 \qquad
 \Xi_t(s)=\Xi_t(1-s)}
\tag{4.845bp}
\]

is an exact consequence of the two completed zeta functional
equations.  Mellin inversion on \(\Re s>1\), followed by a shift to
\(\Re s<0\), crosses the poles \(s=1-it\) and \(s=1+it\).  Thus, for
\(t\ne0\),

\[
 \boxed{
 \begin{aligned}
 A_t(Y;W)
 &=R_t(Y;W)+D_t(Y;W),\\
 R_t(Y;W)
 &=\zeta(1-2it)Y^{1-it}\widehat W(1-it)\\
 &\quad+\zeta(1+2it)Y^{1+it}\widehat W(1+it).
 \end{aligned}}
\tag{4.845bq}
\]

To state the remaining integral exactly, define

\[
 G_t(s)
 :=\pi^{2s-1}
 \frac{
 \Gamma((1-s-it)/2)\Gamma((1-s+it)/2)}
 {\Gamma((s+it)/2)\Gamma((s-it)/2)}
\]

and

\[
 \boxed{
 \begin{aligned}
 D_t(Y;W)
 &=Y\sum_{n\geq1}\lambda_t(n)\widetilde W_t(nY),\\
 \widetilde W_t(x)
 &:=\frac1{2\pi i}\int_{(1+c)}
 G_t(1-w)\widehat W(1-w)x^{-w}\,dw
 \qquad(c>0).
 \end{aligned}}
\tag{4.845br}
\]

The derivation is first performed with finite vertical truncations;
absolute convergence there justifies Fubini.  Stirling and the rapid
decay of \(\widehat W\) remove the truncations.  Repeated contour shifts
show that \(\widetilde W_t(x)\) is rapidly decreasing once
\(x\gg(1+|t|)^2(\log T)^C\).  Hence a primal length \(Y\) has reciprocal
length \((1+|t|)^2/Y\).  In the physical spectral window
\(|t|\leq(\log T)^C\), this has exponent \(-\log_TY\), truncated at zero.

At \(t=0\) the two poles in (4.845bq) collide, but their symmetric sum
has a finite limit.  From
\(\zeta(1+z)=z^{-1}+\gamma+O(z)\), one obtains

\[
 \boxed{
 \lim_{t\to0}R_t(Y;W)
 =Y\int_0^\infty
 W(x)\bigl(\log(Yx)+2\gamma\bigr)\,dx.}
\tag{4.845bs}
\]

Thus the pole-subtracted unramified polynomial has the same
reciprocal-length advantage as the cuspidal polynomial.  Equations
(4.845bk) and (4.845bo) audit only its same-cusp ramified model.  Until
the physical Atkin--Lehner cross-oldspace matrix is inserted, they do
not close the local nonresidual continuous contribution.

It does not yet close the continuous spectrum.  The residue
\(R_t(Y;W)\) depends on the actual physical Mellin tensor, both
Atkin--Lehner cusps, and the finite ramified allocations.  It must be
added to the \(m=0\) term from (4.845ao) and to the paired contour
residues of (4.845at), and only the completed sum may be simplified.
That exact zero-mode/residue identity has not been proved.

The interface
pole_subtracted_eisenstein_functional_equation_audit records the
reciprocal exponent \(2\tau-y\), the finite central collision with
coefficients \(1\) and \(2\gamma\), and the exact unramified
pole-subtracted transform.  It leaves the cross-cusp oldspace adapter,
local nonresidual closure, zero-mode/residue pairing, full
continuous-spectrum gate, and whole Möbius gate false.


### 4.109o The Ramanujan zero mode carries the inverse-zeta factor

The finite Euler factor required by the missing residue pairing is
already explicit on the geometric side.  For \(v=v_p(n)\), the
prime-power Ramanujan sums satisfy

\[
 c_{p^k}(n)=
 \begin{cases}
 1,&k=0,\\
 p^k-p^{k-1},&1\leq k\leq v,\\
 -p^v,&k=v+1,\\
 0,&k\geq v+2.
 \end{cases}
\tag{4.845bt}
\]

Therefore their local generating function is the finite identity

\[
 \boxed{
 \sum_{k\geq0}c_{p^k}(n)X^k
 =(1-X)\sum_{j=0}^{v}p^jX^j.}
\tag{4.845bu}
\]

Multiplying (4.845bu) over primes, or directly inserting
\(c_q(n)=\sum_{d\mid(q,n)}d\mu(q/d)\) and interchanging absolutely
convergent sums, gives for \(\Re w>1\)

\[
 \boxed{
 \sum_{q\geq1}\frac{c_q(n)}{q^w}
 =\frac{\sigma_{1-w}(n)}{\zeta(w)}.}
\tag{4.845bv}
\]

At \(w=1+2z\), the zero-mode Dirichlet series is
\(\sigma_{-2z}(n)/\zeta(1+2z)\).  It has a simple inverse-zeta zero at
\(z=0\), exactly the finite Euler mechanism appearing in the
normal-crossing model (4.845au).  This proves the finite-prime identity;
it does not prove cancellation of the completed residues.  The latter
also requires the exact Atkin--Lehner cusp normalization, the
archimedean Bessel--Mellin transform, the sign with which the
\(m=0\) term was separated, and the ramified restrictions
\(B\mid q,(q,A)=1\).

The interface ramanujan_zero_mode_euler_audit checks (4.845bt) and
(4.845bu) coefficient by coefficient and records (4.845bv).  It keeps
the archimedean normalization, completed zero-mode/residue pairing,
continuous-spectrum gate, and whole Möbius gate false.


### 4.109p The physical cross-cusp projector retains a half-level deficit

The physical prime-level projector can be computed directly from
[Kiral--Young's explicit Eisenstein coefficient
formula](https://arxiv.org/abs/1710.00914), rather than inferred from
unitarity.  Take \(N=p\), \(u=1/2+it\), and use the two cusps
\(\infty\) and \(0\).  Specializing their theorem for the Eisenstein
series attached to each of these cusps gives, up to the common
archimedean Fourier normalization,

\[
 \boxed{
 \begin{aligned}
 D_p(n,u)
 &=p^{-2u}c_p(n)
   \frac{\sigma_{1-2u}(n)}{\zeta(2u)},\\
 O_p(n,u)
 &=p^{-u}
   \frac{\sigma^{(p)}_{1-2u}(n)}
   {\zeta(2u)(1-p^{-2u})}.
 \end{aligned}}
\tag{4.845bw}
\]

Here \(D_p\) is the coefficient at the same cusp, \(O_p\) is the
coefficient at the opposite cusp, and
\(\sigma^{(p)}_\alpha(n)=\sum_{d\mid n,(d,p)=1}d^\alpha\).
The cross-cusp continuous projector occurring in (4.845ap) is therefore

\[
 D_p(m,u)\overline{O_p(n,u)}
 +O_p(m,u)\overline{D_p(n,u)}.
\]

The local size is already visible at \(t=0\), after removing the common
\(\zeta(1)^{-1}\) zero by analytic continuation.  For
\(v_p(m)=0\) and \(v_p(n)=1\),
\[
 D_p(m,1/2)=-\frac1p,\qquad
 D_p(n,1/2)=\frac{2(p-1)}p,\qquad
 |O_p(\,\cdot\,,1/2)|^2=\frac{p}{(p-1)^2}.
\]
Consequently

\[
 \boxed{
 \left|
 D_p(m,1/2)\overline{O_p(n,1/2)}
 +O_p(m,1/2)\overline{D_p(n,1/2)}
 \right|^2
 =\frac{(2p-3)^2}{p(p-1)^2}
 \asymp\frac1p.}
\tag{4.845bx}
\]

Thus the physical projector has amplitude \(p^{-1/2}\), not the
\(p^{-1}\) suggested by the rejected same-cusp candidate.  Over the
Atkin--Lehner factor \(A\), the comparison loses exactly \(A^{1/2}\).
Whether the remaining physical normalizations, the two residue
polynomials, and the \(A,B\)-box counts absorb this loss must be decided
by a new global residue ledger; neither a basis change nor the
same-cusp Poisson gcd average decides it.

The interface prime_level_eisenstein_cross_cusp_audit records the exact
prime-five values
\[
 D_0=-1/5,\qquad D_1=8/5,\qquad |O|^2=5/16,\qquad
 |\mathcal P_{\infty,0}|^2=49/80.
\]
It marks the Kiral--Young specialization and physical cross projector
identified, rejects the same-cusp candidate, and keeps the global
residue-level ledger, continuous-spectrum gate, and whole Möbius gate
false.


### 4.109q The completed Eisenstein residue is a three-variable gate

The physical cross-cusp formula now permits the continuous remainder
to be stated without an unspecified oldspace adapter.  In one fixed
Type-I/II allocation and dyadic factor box, group the two Möbius
variables on each side as

\[
 \boxed{
 \begin{aligned}
 \alpha_{\mathcal D,\mathcal B}(A)
 &=\sum_{\substack{db=A\\d\in\mathcal D,\ b\in\mathcal B}}
   \mu(d)\mu(b)\,w_{\mathcal D,\mathcal B}(d,b),\\
 \beta_{\mathcal D',\mathcal B'}(B)
 &=\sum_{\substack{d'b'=B\\d'\in\mathcal D',\ b'\in\mathcal B'}}
   \mu(d')\mu(b')\,w'_{\mathcal D',\mathcal B'}(d',b').
 \end{aligned}}
\tag{4.845by}
\]

The endpoint inequalities \(d\leq U,de>U,b\leq V\) or \(b>V\)
are part of the displayed smooth weights.  Since the original entries
are squarefree and coprime, \(A,B\) are squarefree and \((A,B)=1\).
Equation (4.845by) is a finite regrouping, not an estimate.

For one tensor from the physical nuclear decomposition, write the two
Eisenstein polynomials as
\[
 A_t(Y_i;W_i)=R_i(t)+D_i(t)
\]
using (4.845bq)--(4.845br).  The reciprocal-length term
\(D_1D_2\) is the part to which the primal/dual large-sieve argument
applies.  The remaining identity is exactly

\[
 \boxed{
 A_t(Y_1;W_1)A_t(Y_2;W_2)-D_1(t)D_2(t)
 =R_1(t)R_2(t)+R_1(t)D_2(t)+D_1(t)R_2(t).}
\tag{4.845bz}
\]

Let \(\mathscr H_{A,B}(t;m)\) denote the exact Bessel--Mellin test
weight multiplied by the squarefree product of the local
Kiral--Young cross factors (4.845bw).  After the \(h,\delta\)
polynomials in (4.845bz) have been evaluated by their displayed
residue or dual formulas, the normalized continuous residual for the
box is

\[
 \begin{aligned}
 \mathfrak R_{\alpha,\beta}[\Psi]
 :=\frac1M
 \sum_{\substack{A\asymp T^\alpha,\ B\asymp T^\beta\\(A,B)=1}}
 \alpha_{\mathcal D,\mathcal B}(A)
 \beta_{\mathcal D',\mathcal B'}(B)
 \sum_{m\ne0}\widehat U(m/M)
 \int_{\mathbb R}\mathscr H_{A,B}(t;m)\\
 {}\times
 \bigl(R_1(t)R_2(t)+R_1(t)D_2(t)+D_1(t)R_2(t)\bigr)\,dt,
 \qquad M=T^{\min(\alpha,\beta)+o(1)}.
 \end{aligned}
\]

Thus the remaining arithmetic variables are precisely \(A,B,m\):
this is a Möbius-weighted three-variable sum, with all local
ramification, smooth weights, and archimedean transforms specified.
The finite tensor integral has polylogarithmic total variation by
(4.845ai).

In the normalization of (4.845bc), the primal estimate gives
\[
 E_{\rm primal}=3/2+x(\alpha,\beta)/2.
\]
On the residual Type-II square its unique worst point is
\((\alpha,\beta)=(5/4,5/4)\), where

\[
 \boxed{
 |\mathfrak R_{5/4,5/4}[\Psi]|
 \ \text{currently has exponent }\frac{17}{8},
 \qquad
 |\mathfrak R_{5/4,5/4}[\Psi]|
 \ll_{C,W}T^2(\log T)^{-C}
 \ \text{is required}.}
\tag{4.845ca}
\]

The missing power is therefore exactly \(T^{1/8}\).  On the boundary
of (4.845bd), only arbitrary logarithmic decay is required.  Proving
(4.845ca), uniformly over the exact divisor allocations and physical
nuclear measure, closes the continuous local gate; no stronger
all-purpose spectral theorem is needed.

The interface completed_eisenstein_residue_trilinear_audit records the
three residue terms, the three remaining arithmetic variables, the
\(17/8\) center exponent, and the \(1/8\) required saving.  It leaves
the signed trilinear estimate, continuous-spectrum gate, and whole
Möbius gate false.


### 4.109r Ramification density gives a local candidate, not a closure

The pointwise prime-level witness (4.845bx) occurs only when one
Fourier index is \(p\)-ramified.  There is therefore a stronger
*unrestricted-index* average.  Remove the common
\(\zeta(1+2it)^{-1}\) factor as in Section 4.109p and put
\(v=v_p(n)\).  Uniformly for real \(t\), the finite Kiral--Young
factors satisfy

\[
 \boxed{
 |D_p(0,1/2+it)|=\frac1p,\qquad
 |D_p(v,1/2+it)|\leq\frac{p-1}{p}(v+1)\ (v\geq1),
 \qquad
 |O_p(v,1/2+it)|\leq\frac{\sqrt p}{p-1}.}
\tag{4.845cb}
\]

Indeed the first two bounds use
\(\left|\sum_{j=0}^{v}p^{-2itj}\right|\leq v+1\), and the last uses
\(\left|1-p^{-1-2it}\right|\geq1-p^{-1}\).  For an unrestricted
integer, the exact natural valuation probabilities are
\(\Pr(v=k)=(1-p^{-1})p^{-k}\).  Consequently

\[
 \begin{aligned}
 \mathbb E_p|D_p|
 &\leq
 \left(1-\frac1p\right)
 \left\{\frac1p+
 \frac{p-1}{p}\sum_{k\geq1}\frac{k+1}{p^k}\right\}\\
 &=\frac{3p-2}{p^2}.
 \end{aligned}
\]

For two independent unrestricted indices \(m,n\), the triangle
inequality applied to the physical cross projector gives the exact
majorant

\[
 \boxed{
 \left(
 \mathbb E_{p,m,n}
 |D_p(m)\overline{O_p(n)}+O_p(m)\overline{D_p(n)}|
 \right)^2
 \leq
 \frac{4(3p-2)^2}{p^3(p-1)^2}
 \asymp p^{-3}.}
\tag{4.845cc}
\]

At \(p=5\), the three rational values are
\[
 \mathbb E_5|D_5|\leq\frac{13}{25},\qquad
 |O_5|^2\leq\frac5{16},\qquad
 (2|O_5|\mathbb E_5|D_5|)^2\leq\frac{169}{500}.
\]
Thus the unrestricted average has amplitude \(p^{-3/2+o(1)}\),
one full factor \(p^{-1}\) better than the pointwise
\(p^{-1/2+o(1)}\) bound.

The corresponding elementary smooth-interval statement is also
available.  Expanding the valuation factors into divisibility
indicators and counting multiples in an interval of length \(X\)
gives, for squarefree \(A\),

\[
 \boxed{
 \frac1X\sum_{n\in\mathbb Z}V(n/X)
 \prod_{p\mid A}|D_p(n,1/2+it)|
 \ll_{V,C}
 A^{-1}\tau(A)^C+X^{-1}\tau(A)^C.}
\tag{4.845cd}
\]

The constant \(C\) is absolute after fixing finitely many seminorms of
\(V\); the \(O(1)\) boundary error for each divisibility condition
produces only the displayed divisor-power cost.  When \(X\asymp A\),
(4.845cd) is \(A^{-1+o(1)}\).  Formally inserting this extra
\(A^{-1}\) into the center ledger would change
\[
 \frac{17}{8}\longmapsto
 \frac{17}{8}-\frac54=\frac78,
\]
so the candidate has much more than the required \(1/8\) saving.

This is not yet a proof for \(\mathfrak R_{\alpha,\beta}[\Psi]\).
The physical sum has ratio and gcd restrictions inherited from the
original \(r,s,h,\delta\) allocation; its indices are \(m\) and the
completed residue/dual transforms of \(h\delta\), not two independent
unrestricted integers.  In particular, the current derivation has not
proved that every physical nuclear tensor preserves the valuation
measure used in (4.845cc), nor has it controlled the two mixed terms
\(R_1D_2\) and \(D_1R_2\) uniformly at all reciprocal-length
endpoints.  These are theorem hypotheses, not polylogarithmic
bookkeeping.

The interface eisenstein_cross_cusp_ramification_density_audit records
the exact local majorant and the *candidate* center exponent \(7/8\).
It marks the unrestricted two-index density bound proved, while
keeping physical-tensor density preservation, all three completed
residue terms, the continuous local gate, global ratio/gcd
aggregation, and the whole Möbius gate false.


### 4.109s The L2 ramification density closes the nonzero continuous square

The \(L^1\) candidate in Section 4.109r is stronger than the spectral
argument needs and uses the wrong natural measure for the product
index.  The primal large sieve requires a coefficient-energy estimate.
It can be proved before the pole subtraction (4.845bq), so no
residue/dual decomposition is needed for the nonzero Poisson modes.

For independent unrestricted integers \(h,\delta\), the exact
valuation distribution of their product is

\[
 \Pr(v_p(h\delta)=k)
 =(k+1)\left(1-\frac1p\right)^2p^{-k}.
\]
Using (4.845cb) and
\[
 \sum_{k\geq0}(k+1)^3x^k
 =\frac{1+4x+x^2}{(1-x)^4},
\]
one obtains the uniform second-moment bound

\[
 \boxed{
 \mathbb E_{p,h,\delta}|D_p(h\delta,1/2+it)|^2
 \leq
 \frac{2(4p^2-2p+1)}{p^3}
 \asymp\frac8p.}
\tag{4.845ce}
\]

At the standard Kuznetsov first index, (4.845ac) gives
\((m,Q)=1\), so for \(p\mid Q\)
\[
 |D_p(m,1/2+it)|^2=p^{-2}.
\]
If a preliminary gcd cell has not yet imposed this coprimality, the
same calculation with a third unrestricted integer gives the same
power below.  Combining (4.845ce), (4.845cb), and
\(|a+b|^2\leq2|a|^2+2|b|^2\) yields

\[
 \boxed{
 \begin{aligned}
 &\mathbb E_{p,h,\delta}
 \left|
 D_p(m)\overline{O_p(h\delta)}
 +O_p(m)\overline{D_p(h\delta)}
 \right|^2\\
 &\qquad\leq
 \frac{2p}{(p-1)^2}
 \left\{\frac1{p^2}
 \frac{2(4p^2-2p+1)}{p^3}\right\}
 \ll p^{-2}.
 \end{aligned}}
\tag{4.845cf}
\]

For \(p=5\), the product-index diagonal moment is \(182/125\);
the unramified first-index square is \(1/25\); and the right side of
(4.845cf) is exactly \(187/200\).  The pointwise physical bound
(4.845bx) has square size \(p^{-1}\).  Thus (4.845cf) restores one
factor \(p^{-1}\) in coefficient energy, or \(p^{-1/2}\) in the
spectral norm.

It remains to justify multiplication over all primes of the shorter
Atkin--Lehner factor.  This is an elementary weighted CRT estimate,
not an independence assumption.  Let \(A\) be squarefree and let
\(\mathcal P_A(m,h\delta;t)\) be the product of the local physical
cross factors at \(p\mid A\).  The four-variable QCT Fourier
decomposition (4.845ah) gives separate smooth one-variable weights in
\(h\) and \(\delta\), and (4.845aj) only adds Mellin twists.  Expanding
the local ramification indicators and counting
\(d\mid h\delta\) by the \(2^{\omega(d)}\) assignments of primes of
\(d\) to \(h\) or \(\delta\) gives

\[
 \boxed{
 \begin{aligned}
 \frac1{HL}
 \sum_{h,\delta}
 |W_1(h/H)W_2(\delta/L)|
 |\mathcal P_A(m,h\delta;t)|^2
 \ll_{\varepsilon,W_1,W_2}
 (AHL)^\varepsilon
 \left(
 A^{-2}+\frac1{AH}+\frac1{AL}+\frac1{HL}
 \right).
 \end{aligned}}
\tag{4.845cg}
\]

To see the boundary terms explicitly, for every squarefree \(d\mid A\)
use
\[
 \mathbf1_{d\mid h\delta}
 \leq
 \sum_{\substack{ab=d\\(a,b)=1}}
 \mathbf1_{a\mid h}\mathbf1_{b\mid\delta}.
\]
For each assignment,
\[
 \frac1{HL}
 \#\{h\asymp H,\delta\asymp L:a\mid h,\ b\mid\delta\}
 \ll
 \frac1{ab}+\frac1{aL}+\frac1{bH}+\frac1{HL}.
\]
The valuation powers in (4.845ce), all double-divisibility terms, and
all choices of the product-Hecke common divisor contribute only
\(\tau(A)^C=(AHL)^{o(1)}\).  This proves (4.845cg) with the actual
smooth tensor weights.  On the residual square,
\[
 1\leq\alpha,\beta\leq\frac32,\qquad
 A=T^{\eta},\quad
 \eta=\min(\alpha,\beta),\qquad H=L=T^{5/2},
\]
so every boundary term in (4.845cg) is bounded by
\(A^{-2}T^{o(1)}\).

At primes in the complementary level factor the two physical cusps
are locally the same; their contribution is the Poisson-gcd
majorant (4.845bo).  At primes of the shorter factor they are the
cross pair just estimated.  Kiral--Young's squarefree cusp
factorization tensors these local statements, while the finite
product-Hecke common-divisor allocations cost \(T^{o(1)}\).
Consequently the primal continuous exponent (4.845bc) improves to

\[
 \boxed{
 E_{\rm cont}^{\ne0}(\alpha,\beta)
 =\frac32+\frac{x(\alpha,\beta)}2
  -\frac{\min(\alpha,\beta)}2
 \leq\frac32<2.}
\tag{4.845ch}
\]

At the center this is
\[
 \frac{17}{8}-\frac58=\frac32.
\]
Thus every nonzero-Poisson-mode continuous box in the residual square
has the fixed margin \(1/2\); outside the square it was already covered
by (4.845bc).  This argument bypasses the completed-residue trilinear
gate of Section 4.109q rather than proving that stronger signed
statement.

The interface eisenstein_cross_cusp_l2_density_audit records the exact
prime-five moments, the \(5/8\) center saving, the final exponent
\(3/2\), QCT weight separation, the finite common-divisor allocations,
and the weighted CRT boundary estimate.  It marks the physical
cross-cusp **nonzero-mode** continuous residual square covered.  It
also records that the original common-Mellin zero-mode/main-term
identity (4.5a)--(4.8) is proved.  Because this primal route does not
shift the two Eisenstein polynomials separately, the stronger spectral
residue decomposition is not a required intermediate theorem.  It
keeps global ratio/gcd and dyadic aggregation, and the whole Möbius
gate false.


### 4.109t Every balanced factor cell has a half-power margin

Sections 4.109i--4.109s can now be combined without a numerical grid.
Keep the balanced hard geometry
\[
 R=S=T^3,\qquad |h|=|\delta|=T^{5/2},
\]
but allow every factor box produced by the exact Type-I/II identity.
Write
\[
 A=T^\alpha,\qquad B=T^\beta,\qquad
 \lambda=\alpha+\beta,\qquad
 \eta=\min(\alpha,\beta),\qquad 0\leq\alpha,\beta\leq3.
\]
The maximum residual Hecke-polynomial exponent is
\(\min(5/2,\lambda)\).  Hence the primal large-sieve excess from
(4.845bc) is

\[
 \boxed{
 x(\alpha,\beta)
 =\left(\eta+\min(5/2,\lambda)-\lambda\right)_+
 \leq\eta.}
\tag{4.845ci}
\]

This inequality is formal: \(\min(5/2,\lambda)\leq\lambda\).

There is one endpoint correction to the density ledger of Section
4.109s.  Its residual square has \(\eta\leq3/2\), so the
\(A^{-2}\) term in (4.845cg) dominates all three CRT boundary terms.
That dominance does not persist on the whole factor square.  For
general \(A=T^\eta\), \(H=T^h\), and \(L=T^\ell\), (4.845cg) has
square-decay exponent

\[
 d_{\rm CRT}=\min(2\eta,\eta+h,\eta+\ell,h+\ell).
\]

The pointwise cross-projector square already has decay exponent
\(\eta\).  Taking the better of it and the two-variable CRT estimate
gives the additional square saving

\[
 \boxed{
 d_2(\eta;h,\ell)
 =\max\{0,\min(\eta,h,\ell,h+\ell-\eta)\}.}
\tag{4.845cl}
\]

For unequal product intervals there is a second, stronger boundary
estimate.  The local formulae in (4.845ce), with their valuation
powers absorbed by \(T^\varepsilon\), give for squarefree \(A\)

\[
 |\mathcal P_A(m,h\delta;t)|^2
 \ll_\varepsilon A^{-2+\varepsilon}(A,h\delta).
\]

Put \(u=\min(h,\ell)\), \(v=\max(h,\ell)\), bound the variable
\(z\sim T^u\) pointwise, and average the other variable
\(y\sim T^v\).  The elementary divisor identity
\((A,y)=\sum_{d\mid(A,y)}\varphi(d)\) gives

\[
 \frac1{T^v}\sum_{y\asymp T^v}(A,y)
 \ll_\varepsilon T^\varepsilon(1+A/T^v),
 \qquad (A,yz)\leq |z|(A,y).
\]

Consequently this one-variable route has additional square saving

\[
 \boxed{
 d_1(\eta;h,\ell)
 =\max\{0,\min(\eta-u,v-u)\},\qquad
 d=\max(d_1,d_2).}
\tag{4.845cm}
\]

In particular, \((\eta,h,\ell)=(1,1,0)\) has \(d_2=0\) but
\(d_1=1\).  A bounded nonzero shift variable therefore does not erase
the density saving: its gcd with the squarefree level factor is bounded,
and the full divisibility average is taken in the other product
variable.

The zero-saving locus is now exact:

\[
 \boxed{d(\eta;h,\ell)=0
 \quad\Longleftrightarrow\quad
 h=\ell=:u\ \text{ and }\ \eta\geq2u.}
\tag{4.845cn}
\]

If \(h\ne\ell\), then either \(\eta\leq u\), when
\(d_2=\eta>0\), or \(\eta>u\), when
\(d_1=\min(\eta-u,v-u)>0\).  If \(h=\ell=u\), then \(d_1=0\)
and (4.845cl) is positive exactly when \(2u>\eta\).  Thus the
continuous-spectrum density obstruction in the original unbalanced
polytope is confined to the equal short-product face (4.845cn), rather
than to all boxes with a bounded product variable.  This geometric
classification does not yet supply the unbalanced Kuznetsov
normalization or aggregate the transform tails.

At the balanced product lengths \(h=\ell=5/2\), this becomes
\[
 d_2(\eta;5/2,5/2)
 =\max\{0,\min(\eta,5/2,5-\eta)\}.
\]
Here \(d_1=0\), while \(d=d_2\) still dominates
\(x(\alpha,\beta)\).  Indeed, if
\(\lambda\leq5/2\), then \(\eta\leq5/4\) and both quantities equal
\(\eta\).  If \(\lambda>5/2\) and \(\eta\leq5/2\), then
\(d=\eta\) and \(x\leq\eta\).  Finally, if \(\eta>5/2\), then
\(\lambda\geq2\eta>5\), so \(x=0\leq d\).  Thus no unrecorded
short-interval boundary loss occurs.
For a primitive cuspidal conductor \(q_0=T^\rho\) with
\(0\leq\rho\leq\lambda\), the primal/dual normalized excess in
(4.845bg) is at most

\[
 \boxed{
 \eta+\frac{\rho}{2}-\lambda
 \leq\eta-\frac{\lambda}{2}
 =-\frac{|\alpha-\beta|}{2}\leq0.}
\tag{4.845cj}
\]

Thus the Maaß and holomorphic cusp contributions have exponent
\(3/2\).  For the continuous contribution, the boundary-corrected
version of (4.845ch) and (4.845ci) give

\[
 \boxed{
 \begin{aligned}
 E_{\rm cusp/holo}(\alpha,\beta)&\leq\frac32,\\
 E_{\rm cont}^{\ne0}(\alpha,\beta)
 &=\frac32+\frac{x(\alpha,\beta)
                    -d_2(\eta;5/2,5/2)}2
 \leq\frac32,\\
 \max(E_{\rm cusp/holo},E_{\rm cont}^{\ne0})
 &\leq\frac32=2-\frac12.
 \end{aligned}}
\tag{4.845ck}
\]

No case distinction remains: (4.845ck) covers Type-I/Type-I,
Type-I/Type-II, and Type-II/Type-II factor cells, including their
boundary faces.  Divisor allocations, oldclass shifts, and the
five-variable physical nuclear measure have \(T^{o(1)}\) or
polylogarithmic cost, absorbed by the fixed \(1/2\) margin.

This is a complete factor-polytope statement only inside the balanced
hard geometry.  The original exponent polytope also contains
\(R\neq S\), unequal \(h,\delta\) lengths, positive \(q\)-exponent,
and boxes outside the polylogarithmic transform core.  The normalization
leading to the common base \(3/2\) has not yet been rederived uniformly
on those cells.  Equation (4.845ck) must not be used as a global MWKF
coverage certificate before that rederivation.

The interfaces cross_cusp_density_boundary_audit and
balanced_spectral_factor_polytope_audit check (4.845ci)--(4.845cn)
with exact rational arithmetic.  In particular, at
\(\alpha=\beta=3\), the CRT decay is \(5\), not \(6\), and the
additional amplitude saving is \(1\), not \(3/2\).  The continuous
exponent is then \(1/2\), while the cuspidal maximum remains \(3/2\).
The audit therefore still marks all balanced Type-I/II factor cells
covered with margin \(1/2\), while keeping the unbalanced original
polytope, transform-tail aggregation, and whole Möbius gate false.


### 4.109u Unequal product lengths leave no normalized continuous excess

The boundary refinement also removes the assumption
\(H=L=T^{5/2}\) from the normalized product-sieve comparison.  Write

\[
 u=\min(h,\ell),\qquad v=\max(h,\ell),\qquad
 \lambda=\alpha+\beta,qquad\eta=\min(\alpha,\beta).
\]

In (4.845t), split the common divisor at
\(c=T^{(v-\lambda)_+}\).  Above this split both residual Hecke
polynomials have length at most \(T^\lambda\).  Multiplying the
Poisson--Hecke index \(T^\eta\) into the shorter residual polynomial
leaves the square-large-sieve excess

\[
 \boxed{
 x_{u,v}
 =\left(\eta+\max\{0,u-(v-\lambda)_+\}-\lambda\right)_+.}
\tag{4.845co}
\]

If \((v-\lambda)_+>u\), the large-common-divisor range is empty and
the small-common-divisor Möbius-PNT estimate applies; this is the zero
inside the inner maximum in (4.845co).

For every \(\alpha,\beta,h,\ell\geq0\), one has

\[
 \boxed{x_{u,v}\leq d(\eta;h,\ell).}
\tag{4.845cp}
\]

Indeed \(\lambda\geq2\eta\).  If \(v\leq\lambda\), then
\(u\leq\lambda\), so
\(x_{u,v}=(\eta+u-\lambda)_+\leq\eta\); whenever it is positive,
the two-variable density term in (4.845cl) supplies the required
amount.  If \(v>\lambda\), then
\(x_{u,v}=(\eta+u-v)_+\).  Positivity together with
\(v>\lambda\geq2\eta\) forces \(u>\eta\); hence
\(d_2=\eta\) and again \(x_{u,v}\leq d_2\).  On the exact
zero-density face (4.845cn), \(\lambda\geq2\eta\geq4u), so
\(x_{u,u}=0\).

After Cauchy, the large-sieve excess contributes \(x_{u,v}/2\) in
amplitude, while (4.845cl)--(4.845cm) subtract
\(d(\eta;h,\ell)/2\).  Thus the nonzero continuous normalized excess
is nonpositive for every unequal-product cell whenever completion has
Poisson length \(T^\eta\).  The interface
balanced_completion_unequal_product_audit records the common-divisor
split, shorter residual length, excess, and density saving.

This is not yet the full original-polytope theorem.  For
\(R\ne S\), completing the \(r\)-quotient produces Poisson exponent
\((\sigma-\rho+\alpha)_+\), and completing the \(s\)-quotient produces
\((\rho-\sigma+\beta)_+\), rather than \(\eta\).  The outer QCT
normalization, choice of orientation, and \(q\)-dependent tails must be
rederived before (4.845cp) can be promoted to global coverage.


### 4.109v CRT lift and reciprocity close the normalized spectral excess

The two completion orientations can be compared before choosing either
one.  For \(R=T^\rho\), \(S=T^\sigma\), their Poisson exponents are

\[
 \boxed{
 p_L=(\sigma-\rho+\alpha)_+,\qquad
 p_R=(\rho-\sigma+\beta)_+.}
\tag{4.845cq}
\]

If both are positive, then
\[
 p_L+p_R=\alpha+\beta=\lambda.
\]
If one is zero, that inactive orientation has no positive Poisson
length.  Retain the common shorter residual exponent

\[
 c=\max\{0,u-(v-\lambda)_+\}\leq\min(u,\lambda).
\]

The two square-large-sieve excesses and their density corrections are

\[
 \boxed{
 x_L=(p_L+c-\lambda)_+,\quad
 x_R=(p_R+c-\lambda)_+,\qquad
 d_L=d(\alpha;h,\ell),\quad
 d_R=d(\beta;h,\ell).}
\tag{4.845cr}
\]

At least one orientation satisfies \(x_\star\leq d_\star\).  If a
Poisson exponent vanishes, choose it: \(c\leq\lambda\) gives
\(x_\star=0\).  Suppose therefore that both are positive.  Then
\[
 x_L=(c-p_R)_+,\qquad x_R=(c-p_L)_+.
\]
If \(\lambda\geq2c\), one of \(p_L,p_R\) is at least \(c\), and the
opposite excess is zero.

It remains to consider \(\lambda<2c\).  Since
\(c\leq\min(u,\lambda)\), one has \(\lambda<2u\).  On
\([0,\lambda]\), put
\[
 \tau_u(a)=\min(a,2u-a).
\]
The two-variable term in (4.845cl) gives
\[
 d(a;h,\ell)\geq d_2(a;h,\ell)\geq\tau_u(a),
\]
and the elementary tent-function inequality is
\[
 \tau_u(a)+\tau_u(\lambda-a)
 \geq\min(\lambda,2u-\lambda)
 \geq2c-\lambda.
\]
If both \(x_L>d_L\) and \(x_R>d_R\), adding the two strict
inequalities would instead give
\[
 d_L+d_R<2c-(p_L+p_R)=2c-\lambda,
\]
a contradiction.  Therefore

\[
 \boxed{
 \min\{x_L-d_L,\ x_R-d_R\}\leq0.}
\tag{4.845cs}
\]

The cuspidal and holomorphic components may choose their completion
orientation separately.  If one Poisson exponent is zero, it has no
positive primal/dual excess.  Otherwise
\(\min(p_L,p_R)\leq\lambda/2\), so for every primitive conductor
\(q_0\leq T^\lambda\),
\[
 \min(p_L,p_R)+\frac{\log_Tq_0}{2}-\lambda\leq0.
\]

For a bound on the original geometric sum, however, the spectral
components must use one common completion orientation.  The density
projector from Section 4.109g also applies to cusp forms.  In squared
normalization their two worst conductor requirements are

\[
 \boxed{
 q_L=(2p_L-\lambda)_+,qquad
 q_R=(2p_R-\lambda)_+.}
\tag{4.845ct}
\]

There is always one index \(i\in\{L,R\}\) for which both
\(x_i\leq d_i\) and \(q_i\leq d_i\).  The inactive-orientation case is
immediate.  Suppose both are active.  Section 4.109v already proves
that at least one orientation closes the continuous spectrum.  If that
orientation has the smaller \(p_i\), then \(q_i=0\).  Otherwise, say
the left orientation closes continuous but fails cusp.  Then

\[
 p_L>p_R,qquad d_L<p_L-p_R.
\]

If the right continuous excess were positive, then \(c>p_L\), while
left continuous closure would give

\[
 d_L\geq c-p_R>p_L-p_R,
\]

a contradiction.  Hence the right continuous excess is zero, and
\(p_R<p_L\) gives \(q_R=0\).  The reversed case is identical.  Thus

\[
 \boxed{
 \exists i\in\{L,R\}:\qquad
 x_i\leq d_i\quad\text{and}\quad q_i\leq d_i.}
\tag{4.845cu}
\]

Combining the power-exponent exact-valuation calculation from Section
4.109g with this orientation argument, every
original entry-scale asymmetry, every factor allocation, and every pair
of product lengths has no positive normalized factor-model excess:
Maaß, holomorphic, and nonzero continuous components all have a valid
completion orientation.  The interface
unbalanced_completion_orientation_audit records (4.845cq)--(4.845cs)
with exact rational arithmetic.

It marks the base-level factor model, the inverse-scaled geometric
adapter, the exact-valuation level family, and normalized
*power-exponent* all-cell coverage true.  It does not prove the
polylogarithmic tensor estimate isolated in Section 4.109x.  Section
4.109w records the outer normalization conditionally on that estimate;
polylogarithmic transform tails and the AFE tail are further separate
obligations.


### 4.109w The lifted nonzero Poisson core has a conditional seven-log aggregation

Write \(L=\log(2T)\).  Assume PEVP\(_{A,B}\), stated in Section
4.109x.  The resulting local lifted estimates retain every ratio,
gcd, exact-valuation, and Type-I/II allocation inside their coupled
weight; none of these indices is summed a second time after the local
gate.  For a left completion, the exact CRT lift has prefactor \(R\),
whereas a right completion has prefactor \(S\).  Thus the two possible
local gates are

\[
 \boxed{
 \mathfrak S^{L}_{q}=R\mathfrak K^{L}_{q},\qquad
 |\mathfrak K^{L}_{q}|\ll_{W,C} S L^{-B};
 \quad
 \mathfrak S^{R}_{q}=S\mathfrak K^{R}_{q},\qquad
 |\mathfrak K^{R}_{q}|\ll_{W,C} R L^{-B}.}
\tag{4.845cv}
\]

Here \(C\) is a fixed finite collection of normalized kernel
seminorms.  Under PEVP\(_{A,B}\), the common-orientation assertion
(4.845cu) chooses one of
these two gates for all Maaß, holomorphic, and nonzero Eisenstein
components in the same geometric box.  In either orientation it gives
the identical reconstructed bound

\[
 \boxed{ |\mathfrak S_q|\ll_{W,C}RS L^{-B}. }
\tag{4.845cw}
\]

For the six dyadic variables in the exact decomposition there are at
most \(O_W(L^6)\) nonempty boxes.  The outer normalization is exactly
\(2T/(qRS)\), and the gcd variable has the harmonic ledger
\(\sum_{q\leq T^{O(1)}}q^{-1}\ll L\).  Consequently the retained
nonzero Poisson core satisfies

\[
 \boxed{
 \sum_q\ \sum_{\text{six dyadic boxes}}
   {2T\over qRS}|\mathfrak S_q|
 \ll_{W,C} T L^{7-B}=o_W(T)\qquad(B>7).}
\tag{4.845cx}
\]

This is a conditional implication concerning only the compactly
retained nonzero-mode core.  Formula (4.845cx) does not prove
PEVP\(_{A,B}\), nor does it absorb the polylogarithmic
kernel-separation tail or the original AFE tail.  The interface
`lifted_outer_qct_aggregation_audit` therefore records the seven-log
ledger but keeps the polylog tensor gate, the nonzero-core conclusion,
both tail flags, and the whole Möbius gate false.


### 4.109x The current valuation tensor leaves a non-polylogarithmic residual

Let \(\mathscr B_{A,B,D,j}[b,a]\) denote one exact-valuation spectral
bilinear form after the CRT lift, with \(D=(A,h\delta)\), level
\(ABj\), and all physical smooth weights retained.  The local
identities above prove the required exponent, but the logarithmic
endpoint needs the stronger square-function inequality

\[
 \boxed{
 \sum_{D\mid A}\left|
   \sum_{j\mid A}\mu(j)\mathscr B_{A,B,D,j}[b,a]
 \right|^2
 \ll_{C,W}\frac{(\log(2T))^C}{A}
 \left(\sum_m|b_m|^2\right)
 \left(\sum_{h,\delta}|a_{h,\delta}|^2\right).}
\tag{PEVP}_{A,B}
\]

The Fourier normalizations and spectral measure are those of
(EVP)\(_{A,B}\); the coefficient \(a_{h,\delta}\) includes the physical
product weight and the exact condition \(D=(A,h\delta)\).  Unlike
arbitrary EVP, PEVP asks only for this physical product coefficient,
but it keeps the signed \(j\)-sum inside the square.

The estimates currently proved cell by cell give (4.845cy), namely the
same right side with \(5^{\omega(A)}\) in place of
\((\log(2T))^C\).  The primorial calculation following (4.845cy) shows
that this is not a polylogarithmic substitute.  Thus PEVP\(_{A,B}\) is
the remaining Möbius-weighted exact-valuation square-function gate.
Proving it would make (4.845cv)--(4.845cx) unconditional for the compact
core; it would still leave the transform and AFE tails.


### 4.109y Exact-level differencing removes the bad valuation multiplicity

The factor \(5^{\omega(A)}\) in (4.845cy) is created by taking
absolute values before the signed \(j\)-sum.  At one prime \(p\mid A\),
that sum is the exact level difference \(\Delta_p-\Delta_{p^2}\).
It can be evaluated on each primitive representation before any
valuation partition.

First take a primitive representation unramified at \(p\).  Let
\(\lambda_a=\lambda(p^a)\), put \(\lambda_a=0\) for \(a<0\), and set
\[
 D_p=1-\frac{p|\lambda_1|^2}{(p+1)^2}.
\]
For valuations \(a=v_p(m)\) and \(b=v_p(Ah\delta)\geq1\), define
\[
\begin{aligned}
 P_p(a,b)
 &=\lambda_a\lambda_b
  +\frac p{D_p}
   \left(\lambda_{a-1}-\frac{\lambda_1\lambda_a}{p+1}\right)
   \left(\lambda_{b-1}-\frac{\lambda_1\lambda_b}{p+1}\right),\\
 U_{p^2}(a)
 &=\frac{p^{-1}\lambda_a-\lambda_1\lambda_{a-1}
                  +p\lambda_{a-2}}
        {\sqrt{D_p(1-p^{-2})}}.
\end{aligned}
\]
The ambient first-coefficient square normalizations are
\((p+1)^{-1}\) at level \(p\) and \((p(p+1))^{-1}\) at level
\(p^2\).  Hence the literal signed local trace kernel is

\[
 \boxed{
 \mathcal K_p^{(0)}(a,b)
 =\frac{P_p(a,b)}{p+1}
  -\frac{P_p(a,b)+U_{p^2}(a)U_{p^2}(b)}{p(p+1)}.}
\tag{4.845cz}
\]

For \(a=0\), (4.845aq_8) makes the complete level-\(p^2\) oldclass
cross term zero.  The Hecke recurrence therefore gives
\[
 \frac{\mathcal K_p^{(0)}(0,b)}{c_p(1)}
 =-\frac{\lambda_1\lambda_{b-1}/(p+1)-\lambda_{b-2}}
         {(p+1)D_p}.
\]
For \(a\geq1\), insert the three terms in \(U_{p^2}\) and use
\(|c_p(p^a)|=p-1\).  Uniformly for \(b\geq1\), Kim--Sarnak and
\(D_p\gg1\) give the two explicit local inequalities

\[
 \boxed{
 \begin{aligned}
 \left|\frac{\mathcal K_p^{(0)}(0,b)}{c_p(1)}\right|
 &\ll (b+1)p^{-1+(b-2)_+\theta},\\
 \left|\frac{\mathcal K_p^{(0)}(a,b)}{c_p(p^a)}\right|
 &\ll (a+1)(b+1)p^{-1+(a+b-2)\theta}
 \qquad(a\geq1).
 \end{aligned}}
\tag{4.845da}
\]

The exact-valuation coefficient norms contribute
\(p^{-a/2}\) from the Poisson index and \(p^{-(b-1)/2}\) from the
physical product index.  In the first line of (4.845da), \(b=1\) has
exponent \(-2+\theta<-3/2\), while for \(b\geq2\) the exponent is
\[
 -1+(b-2)\theta-\frac{b-1}{2}\leq-\frac32.
\]
The second line has exponent
\[
 -1+(a+b-2)\theta-\frac{a+b-1}{2}\leq-\frac32
 \qquad(\theta<1/2).
\]
Thus every unramified conductor choice has amplitude saving at least
\(p^{-3/2}\), a full prime beyond the required \(p^{-1/2}\), rather
than the equality which produced
\(4^{\omega(D)}\).

For primitive conductor exponent one, the local representation is
Steinberg: \(|\lambda_1|^2=p^{-1}\) and
\(\lambda_b=\lambda_1^b\).  Comparing the level-\(p\) newvector with
its complete level-\(p^2\) oldclass gives the exact squared formula
\[
 \left|\frac{\mathcal K_p^{(1)}(a,b)}{c_p(p^a)}\right|^2
 =\begin{cases}
 p^{-b},&a=0,\\
 p^{-(a+b)},&a\geq1.
 \end{cases}
\]
Primitive conductor exponent two contributes zero because its local
Euler factor has degree zero and \(b\geq1\).  The unramified
Eisenstein oldspace obeys (4.845cz)--(4.845da) with \(\theta=0\), and
the conductor-\(p^2\) character pair again vanishes at positive
valuation.

After summing primitive-conductor choices at the amplitude level, the
unramified and Steinberg weights just computed give
\[
 A^{-1/2}\prod_{p\mid A}(1+O(p^{-1}))
 \ll A^{-1/2}(\log\log(3A))^{O(1)}.
\]
Thus primitive-conductor aggregation itself is polylogarithmic; no
Vinogradov--Korobov comparison is needed for this step.  The stronger
squared ledger, including the two terms in the primitive large sieve,
is recorded after the exact regrouping below.

The functions `unramified_exact_level_difference_kernel` and
`steinberg_exact_level_difference_kernel_square` check the two finite
local formulae.  To promote this improvement to PEVP\(_{A,B}\), the
newform decomposition must still be rearranged with the same Bessel
test at every level and the resulting primitive spectral moments must
be bounded without an \(\varepsilon\)-loss.  Until that global estimate
is proved, the polylog tensor flag remains false.


### 4.109z Primitive-conductor regrouping is exact and exposes the epsilon-free gate

The remaining global rearrangement can be written without an
asymptotic sign.  For \(Q_0\mid Q\), set
\[
 \iota_Q(Q_0):=[\Gamma_0(Q_0):\Gamma_0(Q)]
 =\frac Q{Q_0}
  \prod_{\substack{p\mid Q/Q_0\\p\nmid Q_0}}\left(1+\frac1p\right).
\]
Let \(\pi\) be primitive of conductor \(Q_0\), let \(g\mid Q/Q_0\),
and use the general Blomer--Milićević coefficients \(\xi_{\pi,g}(d)\).
In normalized Fourier coefficients put
\[
 U_{\pi,g}(n):=\sum_{d\mid g}\xi_{\pi,g}(d)\sqrt d\,
                 \lambda_\pi(n/d),
 \qquad \lambda_\pi(x)=0\quad(x\notin\mathbb N).
\]
For one fixed Kuznetsov Bessel test \(\Phi\), the cuspidal part of the
full level trace is exactly

\[
 \boxed{
 \Delta_Q^{\rm cusp}(m,n;\Phi)
 =\sum_{Q_0\mid Q}\ \sum_{\pi\in\mathcal B^*(Q_0)}
  \frac{|\rho_\pi(1)|^2\Phi(t_\pi)}{\iota_Q(Q_0)}
  \sum_{g\mid Q/Q_0}U_{\pi,g}(m)
       \overline{U_{\pi,g}(n)}.}
\tag{4.845db}
\]

The same identity holds for holomorphic forms.  Young's orthogonal
Eisenstein newdata decomposition and his Section 8.5 oldclass basis
give the identical formula for the continuous part, with the primitive
sum replaced by its finite character-pair sum and real spectral
integral.  Compact spectral localization and the ordinary large sieve
make the displayed integrals absolutely convergent.

Now put \(Q=ABj\), where \(j\mid A\), and retain the same \(\Phi\) for
every \(j\).  All divisor sums are finite, so (4.845db) gives the exact
reordering

\[
 \boxed{
 \begin{aligned}
 \sum_{j\mid A}\mu(j)\Delta_{ABj}(m,An;\Phi)
 ={}&\sum_{Q_0\mid A^2B}\ \int_{\mathscr S^*(Q_0)}
 |\rho_\pi(1)|^2\Phi(t_\pi)\\
 &\times\sum_{\substack{j\mid A\\Q_0\mid ABj}}
 \frac{\mu(j)}{\iota_{ABj}(Q_0)}
 \sum_{g\mid ABj/Q_0}U_{\pi,g}(m)
       \overline{U_{\pi,g}(An)}\,d\pi .
 \end{aligned}}
\tag{4.845dc}
\]

At each \(p\mid A\), the inner two sums in (4.845dc) are exactly the
three conductor cases of Section 4.109y.  After the valuation norms,
their amplitude weights satisfy
\[
 w_p(0)\ll p^{-3/2},\qquad
 w_p(1)\leq p^{-1/2},\qquad
 w_p(2)=0.
\]
Consequently even absolute aggregation at the amplitude level costs
only
\[
 A^{-1/2}\prod_{p\mid A}(1+O(p^{-1}))
 \ll A^{-1/2}(\log\log(3A))^{O(1)}.
\]
There is no subexponential conductor-subset overhead and no
Vinogradov--Korobov input is needed in this ledger.

PEVP does not take that triangle inequality: it keeps the signed local
operator inside a square.  Put the complete exact-level multiplier on
one side of Cauchy and the unweighted ambient spectral polynomial on
the other.  The conductor weights in the first square are then
\[
 w_p^{(2)}(0)\ll p^{-3},\qquad
 w_p^{(2)}(1)\leq p^{-1},\qquad
 w_p^{(2)}(2)=0.
\]
Consequently the diagonal part of their complete conductor-subset sum
already satisfies
\[
 \sum_{Q_0\mid A^2B}w_A^{(2)}(Q_0)
 \ll \frac1A\prod_{p\mid A}(1+O(p^{-2}))
 \ll \frac1A.
\]
In the length term of the primitive large sieve, division by the
primitive conductor contributes one further \(p^{-1}\) when the local
conductor exponent is one.  Its two nonzero choices are therefore
\(O(p^{-3})\) and \(p^{-2}\), whence
\[
 \sum_{Q_0\mid A^2B}\frac{w_A^{(2)}(Q_0)}{Q_0}
 \ll \frac1{A^2B}\prod_{p\mid A}(1+O(p^{-1}))
 \ll \frac{(\log\log(3A))^{O(1)}}{A^2B}.
\]
Thus both conductor Euler sums are polylogarithmic and the diagonal
one supplies the required square saving \(A^{-1}\) without using VK.

One loss is still not explicit enough.  The cited spectral large sieve
is stated with \((Q_0Y\mathcal T)^\varepsilon\).  At a zero-power
margin, a fixed \(\varepsilon\)-loss cannot be absorbed by the
Vinogradov--Korobov factor.  What is needed is the weighted,
epsilon-free form

\[
 \boxed{
 \sum_{Q_0\mid A^2B}w_A^{(2)}(Q_0)
 \int_{\mathscr S^*(Q_0)}
 \left|\sum_{y\asymp Y}a_y\sqrt y\,\rho_\pi(y)\right|^2d\pi
 \ll_{C,W}\frac{(\log(2T))^C}{A}
 \left(\mathcal T^2+\frac{Y}{AB}\right)
 \sum_y|a_y|^2,}
\tag{PLS}_{Q_0}
\]

where \(w_A^{(2)}(Q_0)\) is the product of the three squared local
weights and includes the exact ambient normalizations in (4.845dc).
The other Cauchy factor is the unweighted full ambient spectral
polynomial.  A proof
may use the Kuznetsov formula again, but every divisor factor must be
summed in mean; replacing it by a pointwise \(n^\varepsilon\) bound is
not sufficient.

The interface `primitive_conductor_level_difference_audit` records the
exact regrouping, the pre-density unramified exponent \(1\), the
post-density unramified exponent \(3/2\), the Steinberg exponent
\(1/2\), the required square exponent \(1\), and the polylogarithmic
diagonal and length conductor Euler sums.  It keeps the epsilon-free
large-sieve and PEVP flags false.  Consequently (PLS)\(_{Q_0}\),
rather than either \(5^{\omega(A)}\) or the conductor-subset count, is
now the precise compact-core obstruction.


### 4.110 The Möbius level coefficient is not the newform Kuznetsov projector

There remains a possible algebraic escape from Section 4.109: perhaps
the signed Type-I levels annihilate oldforms before the positive density
estimate is applied.  The exact newform trace formula rules out this
automatic identification.

If the unrestricted Type-I level coefficient is
\(\alpha=\mu*\mu\), then finite Dirichlet convolution gives

\[
 \boxed{
 \sum_{L\mid c}\alpha(L)
 =((\mu*\mu)*\mathbf1)(c)=\mu(c).}
\tag{4.846}
\]

Thus summing the divisibility-level geometric formulas does reconstruct
the Möbius modulus weight.  It does not follow that the same coefficient
is a newform projector.

For comparison, let \(N\) be squarefree, let \((mn,N)=1\), and write
\(\Delta_N(m,n)\) for the full Bruggeman--Kuznetsov spectral form.
The squarefree newform inversion in Young's subsection
[“Bruggeman--Kuznetsov for newforms, squarefree level”](https://arxiv.org/abs/1710.03624)
is exactly

\[
 \boxed{
 \begin{aligned}
 \Delta_N^*(m,n)
 =\sum_{LM=N}\frac{\mu(L)}{\nu(L)}
 \sum_{\ell\mid L^\infty}\frac{\ell}{\nu(\ell)^2}
 \sum_{d_1,d_2\mid\ell}
 c_\ell(d_1)c_\ell(d_2)
 \Delta_M(md_1,nd_2),
 \end{aligned}}
\tag{4.847}
\]

where \(\nu(p)=p+1\) on a squarefree prime level.  The coprimality
assumption makes (4.847) the literal specialization of the published
formula: all of its auxiliary \(u,v,a,b,e_1,e_2\) divisor sums reduce to
one.  The remaining \(\ell\mid L^\infty\) sum is still present and the
Hecke indices change from \((m,n)\) to \((md_1,nd_2)\).

At \(N=p\), the \(L=p,\ell=1\) term of (4.847) has coefficient

\[
 \boxed{
 \frac{\mu(p)}{\nu(p)}=-\frac1{p+1},}
\tag{4.848}
\]

followed by the nonempty prime-power oldclass tail \(\ell=p^j\),
\(j\geq1\).  On the other hand,

\[
 \boxed{
 (\mu*\mu)(p)=\mu(1)\mu(p)+\mu(p)\mu(1)=-2.}
\tag{4.849}
\]

For example, at \(p=5\) the leading local coefficients are
\(-1/6\) and \(-2\), with difference \(-11/6\).  The prime-power tail
and changed Hecke indices make the mismatch stronger, not weaker.
Therefore (4.846) is an exact geometric recombination but not the
newform inversion (4.847); old exceptional forms are not annihilated by
an algebraic identity already present in the Type-I split.

This does not exclude proving cancellation after inserting the full
signed coefficient into (4.847).  It says that doing so is a new
weighted newform estimate rather than a free projection.  The adapter
`newform_level_mobius_projector_audit` records the prime witness and
keeps the oldform-annihilation and QCT newform-adapter flags false.


### 4.110a Direct Perron cancellation in the leading oldclass cofactor hits a zero-free barrier

The mismatch in Section 4.110 does not preclude analytic cancellation
in the signed level sum.  It does, however, make it necessary to inspect
the relevant Dirichlet series before claiming a power saving.  Retain
only the leading \(\ell=1\) cofactor in the full-level-to-newform formula
preceding (4.847).  On squarefree levels let
\(\alpha=\mu*\mu\), so \(\alpha(p)=-2\), and keep the published level
index \(\nu(p)=p+1\).  If an exceptional spectral parameter
\(0<\beta\leq7/64\) contributes the favourable level factor
\(L^{2\beta}\), the leading signed cofactor has Dirichlet series

\[
 \boxed{
 D_\beta(w)
 :=\sum_{L\ {\rm squarefree}}
 \frac{\alpha(L)L^{2\beta}}{\nu(L)L^w}
 =\prod_p\left(1-\frac{2p^{2\beta-w}}{p+1}\right).}
\tag{4.849a}
\]

Put \(x_p=p^{-(w+1-2\beta)}\).  Prime by prime,

\[
 \frac{1-2p^{2\beta-w}/(p+1)}{(1-x_p)^2}
 =1+O\!\left(\frac{|x_p|}{p}+|x_p|^2\right).
\]

Consequently the exact factorization is

\[
 \boxed{
 D_\beta(w)
 =\frac{H_\beta(w)}{\zeta(w+1-2\beta)^2},
 \qquad
 H_\beta(w)\ \text{absolutely convergent for }
 \Re w>2\beta-\frac12.}
\tag{4.849b}
\]

Before the coupled-conductor correction in Section 4.109, one possible
attempt was to neutralize a putative \(Q^{2\beta}\) loss by the leading
level sum alone.  That attempt would require, for every fixed smooth
dyadic weight \(W\),

\[
 \boxed{
 \sum_{L\ {\rm squarefree}}
 \frac{\alpha(L)L^{2\beta}}{\nu(L)}W(L/Q)
 \ll_{\varepsilon,W}Q^\varepsilon
 \quad\text{for every }\varepsilon>0.}
\tag{4.849c}
\]

A family of bounds (4.849c) makes the dyadic Dirichlet series
holomorphic in \(\Re w>0\).  Since \(H_\beta\) is analytic and nonzero
near the right edge, (4.849b) would then force

\[
 \boxed{
 \zeta(s)\ne0\quad(\Re s>1-2\beta).
 \quad\text{At }\beta=\frac7{64}\text{ this is }
 \Re s>\frac{25}{32}.}
\tag{4.849d}
\]

No such fixed zero-free strip is known unconditionally.  Section 4.109
shows that this Perron estimate is not the current critical input:
Humphries density already neutralizes the archimedean exceptional
factor after the numerator conductor is retained.  The calculation
remains useful as an exact rejection of direct level-Perron
cancellation as a substitute for the missing finite-prime Hecke
average.

This is deliberately a statement about the direct leading-cofactor
Perron route, not a rejection of the complete spectral strategy.  The
prime-power oldclass tail in (4.847) is recombined exactly in Section
4.110b below.  A signed average over newforms remains a logically
separate possible source of cancellation.  The adapter
exceptional_oldclass_mobius_perron_audit records the exact endpoint
\(2\beta=7/32\), the boundary \(2\beta-1/2=-9/32\), and the required
zero-free line \(25/32\).  Section 4.110b upgrades its full-tail flag
after the exact recombination, while the newform-average and coverage
flags remain false.


### 4.110b The complete prime-power oldclass tail preserves the first-order inverse-zeta factor

The qualification about the oldclass tail in Section 4.110a can be
removed.  Fix a newform \(f\) of level \(M\), let \(p\nmid Mmn\), and
write

\[
 \rho_f(p)=1-\frac{p\lambda_f(p)^2}{(p+1)^2}.
\]

Petrow--Young's exact oldform formula has

\[
 \sum_{j\geq0}\frac{p^j}{\nu(p^j)^2}
 \left(\sum_{d\mid p^j}c_{p^j}(d)\lambda_f(d)\right)^2.
\]

Here \(\nu(p^j)=(p+1)^j\), and the defining Chebyshev identity gives
\(\sum_{d\mid p^j}c_{p^j}(d)\lambda_f(d)=\lambda_f(p)^j\).
Thus this is a geometric series, not an unspecified error:

\[
 \boxed{
 \sum_{j\geq0}\frac{p^j\lambda_f(p)^{2j}}{(p+1)^{2j}}
 =\frac1{\rho_f(p)}.}
 \tag{4.849e}
\]

After the exterior squarefree-level factor \(1/\nu(p)=1/(p+1)\),
the exact complete oldclass multiplier is therefore

\[
 \boxed{
 B_f(p):=\frac1{(p+1)\rho_f(p)}
 =\frac{p+1}{(p+1)^2-p\lambda_f(p)^2}.}
 \tag{4.849f}
\]

If \(|\lambda_f(p)|\ll p^\theta\), \(0\leq\theta<1/2\), then

\[
 \boxed{
 B_f(p)=\frac1p+O_f\!\left(p^{-2+2\theta}\right).}
 \tag{4.849g}
\]

Consequently, after inserting \(\alpha(p)=-2\) and the exceptional
factor \(p^{2\beta-w}\), the full local factor is

\[
 1-2p^{2\beta-w}B_f(p)
 =1-2p^{-(w+1-2\beta)}
  +O_f\!\left(p^{2\beta-\Re w-2+2\theta}\right).
 \tag{4.849h}
\]

The quotient by
\((1-p^{-(w+1-2\beta)})^2\) is therefore absolutely convergent in

\[
 \boxed{
 \Re w>
 \max\left\{2\beta+2\theta-1,\ 2\beta-\frac12\right\}.}
 \tag{4.849i}
\]

At \(\beta=\theta=7/64\), the tail-error boundary is \(-9/16\),
while the quadratic inverse-zeta boundary is \(-9/32\); the latter is
still decisive.  In particular, the \(j\geq1\) tail changes only
second-order Euler terms and does not algebraically supply the missing
\(+2p^{-(w+1-2\beta)}\) term.  Finite local factors can have isolated
zeros, so this statement is deliberately not a blanket nonvanishing
claim for the remaining Euler product.  It is the precise assertion
needed here: the complete oldclass tail does not cancel the
inverse-\(\zeta(w+1-2\beta)^2\) factor prime by prime.  Any remaining
spectral route must obtain genuinely signed cancellation across the
newform family, not from the oldclass geometric series itself.

For the exact test witness \(p=5\), \(\lambda_f(5)^2=1\), one has
\(\rho_f(5)=31/36\), \(B_f(5)=6/31\), tail correction \(5/186\), and
full Möbius coefficient \(-12/31\).  The adapter
exceptional_full_oldclass_tail_audit records these identities and
keeps the newform-average, Perron-closure, and whole-gate flags false.


### 4.111 The new (4/5) Möbius additive-twist bound leaves only a (T^{1/5}) model deficit

A genuinely new input became available after the earlier route audit.
[Robles, Theorem 2](https://arxiv.org/abs/2608.07198) proves that there
is an absolute (C_0>0) such that, for every (x\geq3), every real
\(\alpha\), and every reduced (r/q) with
\(|\alpha-r/q|\leq q^{-2}),

\[
 \boxed{
 \sum_{n\leq x}\mu(n)e(n\alpha)
 \ll
 \left(\frac{x}{\sqrt q}+x^{4/5}+\sqrt{xq}\right)
 (\log x)^{C_0}.}
\tag{4.850}
\]

Unlike Davenport's uniform logarithmic estimate, (4.850) gives a fixed
power saving on the balanced minor arcs.  Put (x=T^\chi) and
(q=T^\kappa).  The three power exponents in (4.850) are

\[
 \chi-\frac\kappa2,qquad
 \frac{4\chi}{5},qquad
 \frac\chi2+\frac\kappa2.
\tag{4.851}
\]

All three are at most (4\chi/5) if and only if

\[
 \boxed{
 \frac{2\chi}{5}\leq\kappa\leq\frac{3\chi}{5}.}
\tag{4.852}
\]

Thus one independently exposed length-(T^\chi) Möbius variable gains
at most (T^{\chi/5}) from the published pointwise theorem.

Apply this ledger to the product-compatible hard shell (4.821), where
the four Möbius variables have \(\chi=1\), the raw determinant exponent
is (3), and the target exponent is (2).  Give (4.850) an
over-optimistic advantage: pretend that the bilinear phases split and
that the theorem can be applied independently to all four variables.
Even this grants only

\[
 \boxed{
 S_{\mathrm{Robles,opt}}=4\left(1-\frac45\right)=\frac45.}
\tag{4.853}
\]

Consequently

\[
 \boxed{
 E_{\mathrm{Robles,opt}}=3-\frac45=\frac{11}{5},
 \qquad
 E_{\mathrm{Robles,opt}}-2=\frac15.}
\tag{4.854}
\]

The word “optimistic” is mathematically essential.  In the centered
Fourier form the phase is (e(\alpha(ab-cd))); the four sums do not
factor into four independent one-variable transforms.  A legal
sequential use of (4.850) must retain the other three coefficients and
therefore cannot simply multiply four pointwise savings.

There is a second obstruction.  Taking (q=1) in (4.850) gives

\[
 \boxed{
 \sum_{n\leq x}\mu(n)e(n\alpha)
 \ll x(\log x)^{C_0},}
\tag{4.855}
\]

with no power saving.  The exact identity (4.769) annihilates the
constant Fourier mode, but it does not annihilate neighborhoods of the
small-denominator major arcs.  Those neighborhoods occur inside the
Schwartz support of \(\widehat w(A\alpha)\) and require their own
signed major-arc analysis.

Therefore the new theorem materially narrows the hard model deficit
from one full power to, at best, (1/5) on balanced minor arcs, but it
does not prove the determinant gate.  A viable hybrid must both make
the four uses joint (or combine them with a determinant estimate) and
extract an additional (T^{1/5}), while separately using the physical
centering on all major arcs.  The adapter
`robles_four_mobius_minor_arc_audit` records (4.851)--(4.854) and keeps
the joint-application, major-arc, physical-kernel, and coverage flags
false.

### 4.112 The legal balanced Type-II use recovers only the determinant-window count

The deliberately favourable calculation in Section 4.111 starts from
the already windowed exponent \(3\).  To avoid counting that geometric
saving twice, apply the actual Type-II corollary in Robles's proof before
the determinant window is imposed.  In the balanced product box put


\[
 P_T(\alpha)=\sum_{a,b\asymp T}
   \mu(a)\mu(b)U(a/T)V(b/T)e(\alpha ab),
\tag{4.856}
\]

and define \(Q_T\) in the same way with the other two variables.  A
dyadic partition and Mellin separation of the product cutoff give
exact integrals of the displayed separated weights.  On a frequency
cell whose reduced approximant has denominator \(q=T^\kappa\), the
Type-II estimate with divisor-bounded grouped coefficients in Robles's
proof, specialized to ambient length \(x=T^2\) and factor lengths
\(M=N=T\), is

\[
 |P_T(\alpha)|
 \ll T\bigl(q+T+T^2/q\bigr)^{1/2}(\log T)^D.
\tag{4.857}
\]

Thus its exact \(T\)-exponent is

\[
 \boxed{
 E_{\rm side}(\kappa)
 =1+\frac12\max\{\kappa,1,2-\kappa\}
 =\frac32+\frac12|\kappa-1|.}
\tag{4.858}
\]

The minimum is \(3/2\), attained only at \(\kappa=1\).  The normalization
must now be restored.  Fourier inversion of the hard model (4.821), with
\(Y=T^2\) and \(H=T\), is exactly

\[
 \begin{aligned}
 \mathcal A(T^2,T)
 &=T\int_{\mathbb R}\widehat w(T\alpha)
       P_T(-\alpha)Q_T(\alpha)\,d\alpha\\
 &=\int_{\mathbb R}\widehat w(u)
       P_T(-u/T)Q_T(u/T)\,du.
 \end{aligned}
\tag{4.859}
\]

The prefactor \(T\) and the Fourier-window width \(T^{-1}\) cancel.  The
unwindowed pair \(P_TQ_T\) has ambient exponent \(4\).  Applying (4.857)
to both sides at the optimal denominator therefore gives

\[
 \boxed{
 E_{\rm two\,sides}(1)=2\cdot\frac32=3,
 \qquad E_{\rm target}=2,
 \qquad E_{\rm deficit}=1.}
\tag{4.860}
\]

Exponent \(3\) is exactly the elementary determinant-window count in
(4.821).  Hence the two Type-II applications recover the geometric
codimension-one saving \(T^4\to T^3\); they do not provide any
post-geometric Möbius saving.  Away from the optimal denominator the
bound is even larger:

\[
 \boxed{
 E_{\rm normalized}(\kappa)=3+|\kappa-1|.}
\tag{4.861}
\]

Finally, bounding the product of the two sides pointwise takes an
absolute value before the \(u\)-integral and loses the exact centering

\[
 \int_{\mathbb R}\widehat w(u)\,du=w(0)=0.
\]

So the missing input is not another one-sided additive-twist estimate.
It is a signed two-side estimate for the centered integral in (4.859)
which gains a full \(T\) beyond (4.860), together with the inherited
coprimality and ratio tensors of (4.768).  The adapter
`robles_balanced_product_fourier_audit` records (4.857)--(4.861) and
keeps the centering, signed-correlation, and coverage flags false.


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

Sections 4.9--4.12 now unconditionally cover the endpoint logarithmic
subface \(\beta+\gamma<3/2\), with the larger range
\(\beta+\gamma<2\) in the unit-slope sector.  The completion coefficient,
fixed slopes, coprimality, and polylogarithmic character twists are no
longer residual hypotheses.  Sections 4.25 and 4.28 also cover the large-q
bounded-zeta subface with shift log depth \(\lambda<2\) for fixed
polylogarithmic zeta-scale exponents.  Section 4.28 extends the critical
depth \(\lambda=2\) to
\(K,M\le\mathscr L^\pi\) for every fixed \(\pi<2\).  The boundary
\(\pi\ge2\) and the deeper shift part of that exponent cell remain
residual; Section 4.27 reduces them to the single centered
product-energy inequality (4.239).

The next slice must address the remaining regions in this order:

1. the \(\pi\ge2\) boundary of the growing-\(K,M\) large-\(q\) critical
   face through (4.239), where the phase ratio \(L/P\) no longer grows
   and integration by parts supplies no saving;
2. the deep endpoint logarithmic cells \(\beta+\gamma\ge3/2\), where the
   fixed-slope black-box transfer has exhausted the square root of Menon's
   one-logarithm saving;
3. the positive-power far shells, whose current required saving is

   \[
   g(\delta)=
   \begin{cases}
      2\delta-2,&1<\delta\le2,\\
      2,&2\le\delta\le5/2,\\
      \delta-\tfrac12,&5/2\le\delta\le3;
   \end{cases}
   \]

4. the separate transform-tail obligation from the exact reduction.

For item 2, another application of the same averaged-Chowla theorem cannot
cross the registered boundary: its method supplies at most one logarithm
in the unit-slope sector and one half after the all-slope transfer.  A
successful estimate must use cancellation in the \(q\)- or completion
frequencies before the cardinal \(q\)-sum.

For item 3, the next genuine power-saving attempt is now more narrowly
specified by Section 4.2 of the Type-I/II note: first use the exact
\(\mu*c_U\) factorization identity to extract the single-Möbius main
term and center the remaining product fibers.  The subsequent Gram
expansion must retain the centered/main cross term before reciprocity,
the full determinant phase, a valid zero/nonzero-mode completion, and
Kuznetsov.  The currently available
Cauchy-first ordering followed by cardinality-level separate majorants
fails by the exact exponent-ledger deficit
\(T^{(\beta-1)/2+1/500}\), uniformly for \(1\le\beta\le2\).  The new
estimate must improve the exact residual function above, not the old
ambient CMT exponent.  Every proposed local theorem should be rejected
if it creates a positive diagonal before using both Möbius weights,
loses more than the registered conductor allowance, or replaces the
actual coefficient by an arbitrary sequence.

The general zero-ray audit narrows this once more.  On
\(s_1a_1=uk,\ s_2a_2=vk\), the two restricted convolution mains multiply
to \(\mu(u)\mu(v)\) on squarefree support: the common \(\mu(k)^2\)
disappears.  If \(u,v\asymp T^\theta\), double square-root cancellation
in the primitive slopes has enough exponent slack only when
\(\theta>\beta-1+1/250\).  The low-slope cells at or below that rational
boundary must use the centered/main cross term, the common \(g\)-sum, or
a nonsplit Gram estimate; an argument that spends Möbius cancellation in
\(k\) is invalid.

After splitting the squarefree prime allocation
\(s=s_us_k,\ a=a_ua_k\), reciprocity removes the primitive slope from the
phase as well:
\(gu\overline{sb}/a\equiv g\overline{s_kb}/a_k\pmod1\), while the real
and common-\(b\) phases depend only on \((g,k,b)\) and cancel between the
two zero-ray amplitudes.  Thus the proposed large-slope benchmark is not
a trace-function estimate in \(u,v\); it is a Möbius correlation against
the remaining smooth/allocation weights.  This makes the low-slope
residual smaller as a parameter region, but structurally harder.

There is now a cleaner alternative to fighting that zero-ray residual
inside the balanced \(U=T\) factorization.  The exact Möbius identity
allows \(U=T^{401/200}\) with no \(V\)-split.  It forces
\(b\ll T^{199/200}\) and gives a uniform \(T^{1/1000}\) exponent margin
over the cardinality of every primitive zero-ray layer.  Divisor bounds
and the logarithmic number of slope boxes therefore cover the entire
\(\Delta=0\) contribution unconditionally.  This does not prove the
theorem: \(ab\asymp T^3\) remains in the reciprocal structure and the
full nonzero-determinant phase is
\[
 e\!\left(\frac{\Delta}{b y_1y_2}\right)
 e\!\left(-\frac{\Delta\bar b}{y_1y_2}\right).
\]
There is no global condition \(b\mid\Delta\).  Only that special
zero-phase subfamily has \(c=\Delta/b\), whose shortest endpoint is
\(T^{901/100}\).  The next estimate must therefore treat the complete
long-\(a\), short-\(b\), nonzero-determinant sector LCO in (4.8al), not
only its complementary-divisor zero mode and not the now avoidable
medium-factor Type-II diagonal.

Nor can one exploit \(b<H\) by Poisson summing only the common-\(b\)
phase in \(h\).  The simultaneous fixed-\(a\) phase has normalized
frequency \(HL/A_0=T^{2+\beta}\), while the recombined phase has modulus
\(ab\asymp T^3\) and \(H/(ab)=T^{-1/2}\).  Treating the fixed-\(a\)
factor as smooth would discard a positive-power oscillation and produce
the false condition \(b\mid\delta\).  A valid LCO estimate must transform
the complete CRT phase.

After that complete transform, the exact residual is the averaged
determinant equation \(rv-js=\delta\), with
\(r,s=T^3\), \(v,j=T^{1/2}\), and \(\delta=T^{5/2}\).  Direct counting is
\(T^{7/2}\) per shift and \(T^6\) after the shift average.  Literal
substitution in Bettin--Chandee Corollary 1 gives the much worse
fixed-shift error \(T^{111/10}\).  The target \(T^{3499/1000}\) therefore
requires a new Möbius saving of exactly \(T^{2501/1000}\) in the complete
shift average, recorded as \(\mathrm{MD}_{2501/1000}\) in (4.8av).

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
length interpolation are rejected; a nonempty endpoint logarithmic region
is now proved; the surviving task is a power-saving pre-Cauchy
two-Möbius spectral inequality for the displayed \(g(\delta)\), together
with the deep-logarithmic and transform-tail estimates.
