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
 \mu^2(dbe)=1,qquad (dbe,sq)=1.
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
cross-scale aggregation is not proved here.

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
