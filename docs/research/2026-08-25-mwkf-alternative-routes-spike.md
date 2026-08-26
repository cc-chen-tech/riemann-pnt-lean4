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
 \sum_{V\ {m dyadic}}R_\mu(V;T,U)V^4
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
`Fraction`.  This is a no-go result only for the Watt-first, cellwise use of
BBLR.  It is not a lower bound for the original signed sum.  At that stage
the two visible global options were:

1. prove a BBLR-strength joint estimate after summing all outer scales in
   (4.616), before any triangle inequality; or
2. return to the pre-Cauchy slope family (4.457), where cancellation among
   slopes need not pass through the positive DCV square function.

#### 4.68.1 Completing the shift first removes the hard error deficit

The conclusion after (4.621) is correct for a literal application of the
published Watt estimate, but it is not the best estimate of BBLR's exact
nonzero-frequency expression (14).  In the all-unsigned hard cell, complete
the (h)-sum before estimating the inverse fraction.

Put

\[
 d=(m_1,n_1),\qquad m_1=dm,\qquad n_1=dn,
\tag{4.621a}
\]

so that (m,n\asymp T/d) and ((m,n)=1).  Equation (14) has

\[
 0<|l|\le L,\qquad L\ll \frac{T^\varepsilon}{d},
\tag{4.621b}
\]

and its phase in (h) is

\[
 e\!\left(\mp l h\frac{\bar m}{n}\right).
\]

Poisson summation gives, for every fixed (A>0),

\[
 \sum_h W_0\!\left(\frac{dh}{T}\right)
 e\!\left(\mp l h\frac{\bar m}{n}\right)
 \ll_A \frac Td
 \left(1+\left|l\bar m\right|_n\right)^{-A},
\tag{4.621c}
\]

where (|x|_n) is the least absolute residue.  Here (T/d\asymp n), so
there is no omitted ratio of the shift length to the modulus.

As (m) runs through an interval of length (T/d\asymp n), inversion
permutes the reduced residue system modulo (n).  Multiplication by (l)
has fibres of size at most ((l,n)).  Therefore

\[
 \sum_{\substack{m\asymp T/d\\(m,n)=1}}
 \left|\sum_h W_0\!\left(\frac{dh}{T}\right)
 e\!\left(\mp l h\frac{\bar m}{n}\right)\right|
 \ll_A \frac Td(l,n)T^\varepsilon.
\tag{4.621d}
\]

The integral (F) in equation (14) has length (d), hence
(F\ll d).  Do not now use the pointwise inequality ((l,n)\le l).
Instead sum the frequency gcd by the exact identity

\[
 \sum_{1\le l\le L}(l,n)
 =\sum_{r\mid n}\varphi(r)\left\lfloor\frac Lr\right\rfloor
 \le L\tau(n).
\tag{4.621e}
\]

After (4.621d), the (F)-factor, the (n\asymp T/d)-sum and
(4.621e), the whole fixed-(d) nonzero-frequency contribution is

\[
 \mathcal R_d\ll
 \frac{T^2}{d}L T^\varepsilon
 \ll \frac{T^{2+\varepsilon}}{d^2}.
\tag{4.621f}
\]

Now (4.621b) forces (d\le T^\varepsilon).  Summing over (d) yields

\[
 \boxed{\mathcal R_{\pm}^{\rm hard,unsigned}
 \ll T^{2+\varepsilon}.}
\tag{4.621g}
\]

The approximation error already present in (14) is (H^2T^\varepsilon
=T^{2+\varepsilon}), so (4.621g) reaches the exact local target.  The
previous (T^{5/2}) ledger is therefore a deficit of the Watt-first route,
not a deficit of the hard nonzero-frequency sum itself.

The same calculation gives a finite post-Type coverage test.  Write the
BBLR exponents as

\[
 A=T^a,\ B=T^b,\ M_i=T^{\mu_i},\ N_i=T^{\nu_i},\ H=T^\alpha,
\]

with (a+\mu_1+\mu_2=b+\nu_1+\nu_2=P).  Reindex
(X=am_1/d), (Y=bn_1/d); the factorization multiplicities are divisor
bounded, so all Möbius atoms may remain in the two arbitrary outer
coefficients.  In the BBLR orientation (BN_1\le AM_1), equivalently
(b+\nu_1\le a+\mu_1) at exponent level, completing (h), summing the
(X)-residues and then applying (4.621e) to the complete (l)-average gives
the nonzero-frequency exponent

\[
 \boxed{
  E_{h\text{-comp}}
 =\mu_2+(a+\mu_1-b-\nu_1)_+
  +\max(b+\nu_1,\alpha)
  +(a+\mu_1-\nu_2)_+.}
\tag{4.621h}
\]

If (a+\mu_1-\nu_2<0), the nonzero (l)-family is empty by its exact
cutoff.  Otherwise the subcell is covered whenever

\[
 E_{h\text{-comp}}\le P.
\tag{4.621i}
\]

To recover the full symmetric proposition one must also allow the two
sides to be exchanged.  Set (x=a+\mu_1) and (y=b+\nu_1).  Balance gives
(\nu_2=P-y), so the cutoff exponent is

\[
a+\mu_1-\nu_2=x+y-P.
\]

The better of the two orientations simplifies exactly to

\[
 \boxed{
 E_{h\text{-comp}}^{\rm sym}
 =P+(\alpha-\min(x,y))_+ +(x+y-P)_+.}
\tag{4.621s}
\]

Consequently the complete coverage classification is:

1. if (x+y<P), the nonzero-frequency family is empty;
2. if (x+y=P), one of the two orientations reaches the target exactly
   when (\min(x,y)\ge\alpha);
3. if (x+y>P), the completion bound is strictly above (P).

Thus the remaining nonzero-frequency Type cells are not diffuse: they are
the supercritical half-polytope (x+y>P), together with the
too-small-prefix portion (\min(x,y)<\alpha) of the boundary.  The former
"reversed ordering" residual was an artefact of fixing one orientation.
No assertion is made that failure of this particular completion bound is
a lower bound for the original signed sum.

Formula (4.621s) also locates the remaining power exactly.  On the
supercritical subregion where (\min(x,y)\ge\alpha), the whole deficit is

\[
 E_{h\text{-comp}}^{\rm sym}-P=x+y-P,
\]

which is precisely the exponent of the surviving nonzero (l)-frequency
range.  In the symmetric signed hard cell (x=y=3/2), (P=2), this is one
full power: (L=T) and the bound is (T^3) against target (T^2).  A generic
square-root treatment of the (l)-family would recover only (T^{1/2}) and
would recreate the old half-power deficit.  Closing this region therefore
requires the complete (l)-range saving from its joint interaction with the
two outer coefficient families, or an exact recombination that removes the
range before absolute values.  On the remaining boundary portion
(x+y=P), the deficit is instead the short shift/modulus mismatch
(\alpha-\min(x,y)).

For (4.618), (4.621h) is exactly (2).  For example, the signed cell
(a=b=1), (mu_i=\nu_i=1/2), (alpha=1) instead gives (3), so the
new completion is a genuine additional coverage region, not a proof of all
Type cells.

Finally, (4.621g) concerns only (l\ne0).  The (l=0) Poisson main term
is of larger raw size and still has to be recombined across all four
Möbius outer allocations and the BBLR orderings, together with the already
registered zero-frequency master.  Consequently the whole coupled gate is
not yet proved, but its formerly worst **nonzero-frequency** cell is now
closed without any Möbius estimate.

The adapters `transition_bblr_hard_h_completion_audit` and
`transition_bblr_h_completion_subcell_audit` record (4.621a)--(4.621i).
The adapter `transition_bblr_symmetric_h_completion_audit` records the
left/right minimum (4.621s).
The helpers `inverse_multiplier_unit_fibre_max` and
`frequency_gcd_sum_identity` check the exact fibre and frequency-average
identities on finite moduli.

#### 4.68.2 The remaining BBLR main term is an exact phase-free outer product

The (l=0) term can be isolated without an estimate.  Put

\[
 \mathcal A_d(X)=
 \sum_{am_1=dX}\alpha_aW_1\!\left(\frac{m_1}{M_1}\right),
 \qquad
 \mathcal B_d(Y)=
 \sum_{bn_1=dY}\beta_bW_3\!\left(\frac{n_1}{N_1}\right),
\tag{4.621j}
\]

and

\[
 \mathcal K_d(X,Y)=
 \sum_h W_0\!\left(\frac{dh}{H}\right)
 \int_0^\infty
 W_2\!\left(\frac{Yx}{M_2}\right)
 W_4\!\left(\frac{Xx}{N_2}\right)\,dx.
\tag{4.621k}
\]

Since

\[
 d=(am_1,bn_1),\qquad X=\frac{am_1}{d},\qquad
 Y=\frac{bn_1}{d},\qquad (X,Y)=1,
\]

the main term in BBLR Proposition 3.1 is exactly

\[
 \boxed{
 \mathcal M_{\rm BBLR}
 =\sum_{d\ge1}\sum_{(X,Y)=1}
 \mathcal A_d(X)\mathcal B_d(Y)\mathcal K_d(X,Y).}
\tag{4.621l}
\]

All sums in (4.621l) are finite because the five original smooth weights
are compactly supported.  There is no endpoint error, no inverse residue
and no additive phase.  The two arbitrary outer coefficients remain
separate; in particular their two Möbius-bearing decompositions have not
been replaced by absolute values.

This identity also explains why the main term cannot be discarded
cellwise.  For a balanced side-product exponent (P), shift exponent
(alpha), and (d=T^eta), the (X,Y)-counts, the shift length (H/d), and
the integral length (dM_2/(BN_1)) give the fixed-(d) absolute-value
exponent

\[
 E_{\ell=0,d}=P+\alpha-2\eta.
\tag{4.621m}
\]

The dyadic (d)-layer contains (T^{\eta+o(1)}) values.  Hence

\[
 E_{\ell=0,\rm layer}=P+\alpha-\eta,
 \qquad
 \boxed{E_{\ell=0,\rm global}=P+\alpha.}
\tag{4.621n}
\]

Thus the raw phase-free main term is one complete shift length
(T^\alpha) above the local (T^P) target.  In the all-unsigned hard cell
this specializes to

\[
 \mathcal M_{\rm BBLR}^{\rm hard,unsigned}
 \ll T^{3+\varepsilon}
 \quad\text{against target }T^{2+\varepsilon}.
\tag{4.621o}
\]

Moreover, the plus/minus shifted equations in BBLR have the same
(l=0) term: their only orientation dependence is in the additive phase,
which has disappeared.  The two orientations therefore do not cancel
internally when their external weights agree.  Opposite signs from a
larger AFE recombination are not ruled out, but must be exhibited there.

Thus the
nonzero-frequency completion does not by itself cover the whole cell.
Inside the present DCV/square-function route, the correctly typed missing
object is the fully recombined BBLR zero-frequency contribution

\[
 \mathfrak G_{\rm BBLR}^{(0)}
 :=\sum_{\substack{\text{AFE directions, BBLR orderings,}\\
                    \text{four outer Möbius sectors}}}
 \mathcal M_{\rm BBLR},
 \qquad
 \mathfrak G_{\rm BBLR}^{(0)}
 \stackrel{?}{\ll}T^{P+\varepsilon}.
\tag{4.621p}
\]

The estimate in (4.621p) is not yet proved.  Nor is
\(\mathfrak G_{\rm BBLR}^{(0)}\) identified with the pre-Cauchy
\(\mathcal M_{\rm res}\) in (9.447): they live at different stated stages,
so they cannot be literally cancelled without first constructing an
adapter that undoes or bypasses the DCV reorganization.
The finite helper `bblr_zero_frequency_reindex_sides` verifies (4.621j)--
(4.621l) for arbitrary rational coefficient fixtures and deliberately sets
`registered_zero_master_identification_proved=False`.  This separates the
remaining main-term adapter from the now-bounded nonzero-frequency error.
The adapter `transition_bblr_zero_main_term_audit` records (4.621m)--
(4.621o) and the shift-orientation boundary with exact rational exponents.

There is no further coordinate obstruction to constructing a pair kernel
of the same algebraic shape as the finite master schema (9.437)--(9.448).
This does **not** yet identify the analytic stage: the BBLR comparison may
already lie inside a DCV/square-function reorganization, whereas
\(\mathcal M_{\rm res}\) in (9.447) is pre-Cauchy.  Put (x=dX), (y=dY),
so the coprimality in (4.621l) is equivalent to (d=(x,y)), and define the
labelled product kernel

\[
 W_h^{\rm BBLR}(x,y):=
 W_0\!\left(\frac{(x,y)h}{H}\right)
 \int_0^\infty
 W_2\!\left(\frac{y u}{(x,y)M_2}\right)
 W_4\!\left(\frac{x u}{(x,y)N_2}\right)\,du.
\tag{4.621q}
\]

Writing

\[
 A(x)=\sum_{am_1=x}\alpha_aW_1(m_1/M_1),\qquad
 B(y)=\sum_{bn_1=y}\beta_bW_3(n_1/N_1),
\]

equation (4.621l) becomes the literal pair-kernel identity

\[
 \boxed{
 \mathcal M_{\rm BBLR}
 =\sum_h\sum_{x,y\ge1}A(x)B(y)W_h^{\rm BBLR}(x,y).}
\tag{4.621r}
\]

Thus each original nonzero shift (h), together with its AFE direction,
BBLR ordering and dyadic label, can be retained in a
secondary-zero-packet-shaped kernel; no inverse phase or gcd endpoint is
lost.  What is still missing is not a kernel-coordinate map.  It is the
analytic proof that this BBLR object is at the same pre-Cauchy stage as
(9.440), that after summing every Type sector and ordering the functions
(A,B) in (4.621r) are exactly the completed left/right coefficients in
(9.439), and that the resulting labelled packet family is exhaustive.
Only after all three facts are proved can this BBLR object be compared
literally with the old pre-Cauchy master.  Independently, proving the bound
in (4.621p) inside the DCV route requires the exhaustive ordering/sector
sum and a (T^alpha)-saving estimate for that recombined object.

The finite helper `bblr_zero_frequency_reindex_sides` now verifies all
three equal values: the original factorized sum, the primitive
((d,X,Y))-sum, and the labelled product-pair sum (4.621r).  It marks the
coordinate bijection and shift-label preservation as true, while keeping
`pre_cauchy_stage_identification_proved=False`,
`completed_coefficient_identification_proved=False` and
`packet_family_exhaustive=False`.

#### 4.68.3 The supercritical nonzero family must be grouped by full reciprocal phase

The factorization-blind reindexing is not restricted to (l=0).  Let a
supplied finite BBLR packet retain its original ((h,delta))-provenance and
write

\[
 \mathscr W(d,X,Y;h,\delta,l)
\]

for its complete smooth weight, integral and nonzero-(l) phase.  The
analytic adapter from the original coupled kernel to this labelled BBLR
packet is still an obligation; the following finite statement says that
once those labels are supplied, no Type-factorization step is allowed to
delete them.

With (A_d,B_d) as in (4.621j), exact finite reindexing gives

\[
 \boxed{
 \mathscr S_{\rm BBLR}^{\ne0}
 =\sum_d\sum_{(X,Y)=1}A_d(X)B_d(Y)
   \sum_{h,\delta}\sum_{l\ne0}
   \mathscr W(d,X,Y;h,\delta,l).}
\tag{4.621t}
\]

Thus every Type sector having the same products (am_1=dX) and (bn_1=dY)
recombines inside (A_d(X)) and (B_d(Y)) before any absolute value.  Both
coupled products remain visible:

\[
 a_0:=h\delta,qquad b_0:=hl,qquad
 \phi(d,X,Y;h,l):=-\frac{b_0\bar X}{Y}\pmod1.
\tag{4.621u}
\]

In particular the all-unsigned outer cell cannot be estimated and summed
afterwards: its positive coefficient is cancelled, if at all, only inside
the complete aggregated (A_d,B_d).

The correct (TT^*) resonance is equality of the full rational phases in
(4.621u), not equality of either scalar product.  For two rows (u,v), it
is exactly

\[
 \frac{h_ul_u\overline{X_u}}{Y_u}
 \equiv
 \frac{h_vl_v\overline{X_v}}{Y_v}\pmod1.
\tag{4.621v}
\]

Distinct values of both (h\delta) and (hl) can satisfy (4.621v).  Hence a
partition by the original product frequency does not diagonalize the new
operator.

After lifting a finite row family to a common cyclic modulus (Q), exact
character orthogonality gives

\[
 \boxed{
 Q\sum_\phi\left|\sum_{u:\phi_u=\phi}c_u\right|^2
 =Q\sum_u|c_u|^2
  +Q\sum_{\substack{u\ne v\\\phi_u=\phi_v}}
       c_u\overline{c_v}.}
\tag{4.621w}
\]

The second term in (4.621w) is signed and can cancel the positive identity
diagonal.  Taking absolute values of phase classes, or applying Cauchy
before the Type sectors have recombined, deletes precisely this possible
source of the full (L)-saving.

On the supercritical region with (\min(x,y)\ge\alpha), put
(\lambda=x+y-P>0).  Equations (4.621s) and (4.621w) give the exact budget

\[
 E_{\rm raw}=P+\lambda,qquad
 S_{\rm required}=\lambda,qquad
 S_{\rm generic\ square\ root}=\frac\lambda2,qquad
 S_{\rm still\ missing}=\frac\lambda2.
\tag{4.621x}
\]

At the signed hard cell, (\lambda=1), so the remaining signed phase-class
gain is exactly (T^{1/2}) after a generic square-root treatment.  This is
not a proof of that gain; it identifies its only surviving location inside
the BBLR route.

The finite helper `bblr_nonzero_frequency_reindex_sides` verifies
(4.621t)--(4.621u) with nonzero (l), both original labels and both products
unchanged.  The helpers `bblr_reciprocal_phase_collision_audit` and
`bblr_phase_group_ttstar_sides` verify (4.621v)--(4.621w), including a
fixture in which distinct product frequencies collide and the signed cross
term reduces the positive identity diagonal.  The exponent adapter
`transition_bblr_phase_group_saving_audit` records (4.621x) and keeps
`required_phase_class_cancellation_proved=False`.

### 4.69 Kim's 2026 ternary-correlation theorem enters the shift range but not the gate

The recent circle-method theorem of
[Jiseong Kim, Theorem 1.6](https://arxiv.org/abs/2603.23250) has a Fejér
shift average close to the exact correlation shape in (9.353) of the
Type-I/II note.  It is therefore necessary to audit both its power and its
coefficient class rather than dismiss it from the title alone.

Use (X_0=T^3) and (H_0=T^2=X_0^{2/3}).  In the theorem's
(alpha=0) case, its range and error have the form

\[
 H_0\gg X_0^{1/2+100\varepsilon_K},
 \qquad
 E_K\ll X_0H_0^{1-\varepsilon_K/2}.
\tag{4.622}
\]

The range in (4.622) forces the strict ceiling

\[
 \varepsilon_K<\frac{2/3-1/2}{100}=\frac1{600}.
\tag{4.623}
\]

Measured in the present (T)-exponents, the ambient shifted sum has
exponent (3+2=5), while the coupled target is (9/2).  Even at the
unattained endpoint of (4.623), Kim's error saves only

\[
 \frac{2\varepsilon_K}{2}<\frac1{600},
 \qquad
 \boxed{
 \frac12-\frac1{600}=\frac{299}{600}}
\tag{4.624}
\]

of the required half-power.  Thus its numerical strength is insufficient
even before checking hypotheses.

The coefficient obstruction is independent and decisive.  Definition 1.1
requires the associated twists (L(f,\chi,s)) to be holomorphic in
(Re s>1/2) and to satisfy a critical-line second moment.  For Möbius,
up to the standard imprimitive Euler factors,

\[
 L(\mu,\chi,s)=\sum_{n\ge1}\frac{\mu(n)\chi(n)}{n^s}
 =\frac1{L(s,\chi)}.
\tag{4.625}
\]

Zeros of (L(s,\chi)) produce poles in the required open half-plane
unconditionally.  Assuming GRH moves them to the boundary but does not
create the demanded critical-line (L^2) integral: the square of a simple
reciprocal pole is not locally integrable.  Kim's separate discussion of a
GRH bound for Möbius exponential sums is not an assertion that Möbius lies
in the class of Definition 1.1.

Finally, the dyadically weighted coefficients in (9.352) are not one fixed
multiplicative function.  Full outer-scale recombination can recover a
Möbius coefficient, but that returns exactly the reciprocal-(L) failure
in (4.625).  Consequently

\[
 \boxed{
 \text{Kim 2026: shift length enters; power and coefficient hypotheses fail.}}
\tag{4.626}
\]

The adapter `transition_kim_ternary_correlation_audit` records
(4.622)--(4.624) with exact fractions and keeps separate false flags for
holomorphy, the critical-line second moment, the dyadic multiplicative
coefficient, theorem applicability, and coupled-gate coverage.  This is a
new published-estimate row, not a replacement gate.

### 4.70 Doyle's 2026 short k-free theorem crosses the length line in the wrong direction

The top balanced-variance cell (4.540) has product centre (N=T^2) and
short interval (K=T=N^{1/2}).  Ben Doyle's new
[Lemma 1.2, Theorem 1.7, and Corollary 1.8](https://arxiv.org/abs/2608.16679)
therefore deserve a literal endpoint check.  For (k=2), the middle-part
exponent in that paper is

\[
 \delta_2=\frac{105}{317},
 \qquad
 \frac32\delta_2=\frac{315}{634}
 =0.496845\ldots .
\tag{4.627}
\]

Thus its Möbius corollary applies for
(K\gg N^{315/634+\varepsilon}).  The interval exponent in (4.540)
does enter this range, by the exact margin

\[
 \boxed{\frac12-\frac{315}{634}=\frac1{317}.}
\tag{4.628}
\]

This is genuine length coverage, but not analytic coverage of the gate.
The Möbius conclusion of Theorem 1.7 is the lower bound

\[
 \int_0^1\left|\sum_{N-K<n\le N}\mu(n)e(n\alpha)\right|d\alpha
 \gg K^{1/6},
\tag{4.629}
\]

whereas (4.540) requires an **upper** short-interval (L^2) variance for
the balanced convolution (c_{U,V}).  Reversing (4.629) is impossible.
The estimate which drives Doyle's theorem also concerns the different
middle coefficient

\[
 c_n(y,z)=\sum_{\substack{y<d\le z\\d^2\mid n}}\mu(d),
\tag{4.630}
\]

with one Möbius weight on square divisors.  It is not the two-Möbius
product-divisor coefficient

\[
 c_{U,V}(n)=\sum_{ar=n}\mu(a)\mu(r)U(a/T)V(r/T)
\tag{4.631}
\]

in (4.535).  Therefore neither Lemma 1.2 nor the Möbius (L^1) corollary
can be substituted into (4.540):

\[
 \boxed{
 \text{Doyle 2026: the length threshold enters by }N^{1/317},
 \text{ but conclusion and coefficient both mismatch.}}
\tag{4.632}
\]

The exact adapter `transition_doyle_kfree_moment_audit` records the
fractions in (4.627)--(4.628), the lower-versus-upper direction, and the
square-divisor-versus-balanced-convolution distinction.  It keeps
`theorem_applies_to_actual_packet=False` and
`whole_line_family_covered=False`.  This closes another tempting 2026
paper route without weakening the residual gate.

### 4.71 The 2026 Bessel-Kuznetsov phase transition misses the exact degenerate orbit

Yuhang Shi's recent
[Theorem 1.1](https://arxiv.org/abs/2608.13232) studies the classical
Bessel--Kuznetsov transform of
(phi(x)=W(x)e(alpha x)), with (W) supported on a positive dyadic
interval ([X,2X]).  It proves rapid spectral decay for
(alpha\leq1/(2pi)) and a localized stationary main term above that
threshold.  This is potentially relevant only after checking the actual
Bessel argument of the determinant orbit.

For the ordinary nondegenerate Kloosterman term (S(m_2,m_1;c)), that
argument is proportional to

\[
 x_{\rm Bes}=\frac{4\pi\sqrt{|m_1m_2|}}{c}.
\tag{4.633}
\]

But the exact substitution in (4.134) is

\[
 (m_2,m_1;c)=(0,-h;s),
 \qquad
 S(m_2,m_1;c)=S(0,-h;\delta;s).
\tag{4.634}
\]

Therefore

\[
 \boxed{x_{\rm Bes}=0.}
\tag{4.635}
\]

This is the degenerate Ramanujan/Eisenstein orbit, not a positive-dyadic
Bessel transform.  Consequently there is no actual (alpha) to compare
with (1/(2pi)), and the subcritical rapid-decay conclusion cannot be
inserted into (4.132).

After Cauchy and a second completion, some determinant formulas contain
two nonzero formal Fourier indices.  That does not rescue this application:
Sections 4.15--4.16 and 4.46 already record that no classical
nondegenerate Kuznetsov transform from the entry-weighted QCT kernel has
been derived, and the two Möbius weights remain on matrix entries rather
than the standard Fourier indices.  Thus

\[
 \boxed{
 \text{Shi 2026: a useful transform theorem, but the exact orbit has }
 x_{\rm Bes}=0.}
\tag{4.636}
\]

The adapter `transition_shi_bessel_kuznetsov_audit` records both Fourier
indices, the zero argument, the missing linear-twist identification, and
the missing nondegenerate adapter.  It keeps
`subcritical_rapid_decay_applies=False` and
`whole_line_family_covered=False`.  A different relative trace formula
could still create a nondegenerate transform, but proving that formula is
itself part of the unresolved coupled-kernel problem.

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
