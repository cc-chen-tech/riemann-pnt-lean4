# Conrey two-fifths theorem: mathematical audit before Lean

## Status

This note reconstructs the mathematical route to Conrey's unconditional
two-fifths theorem.  It is deliberately a paper proof audit, not a Lean
implementation plan disguised as mathematics.

The target is the genuine theorem about **simple** critical-line zeros:

\[
  \kappa^*=
  \liminf_{T\to\infty}\frac{N_0^*(T)}{N(T)}>\frac25,
\]

where `N(T)` counts nontrivial zeta zeros up to height `T` with
multiplicity and `N_0^*(T)` counts simple zeros on `Re s = 1/2`.

The reconstruction has four conclusions.

1. The logical chain from the xi-function argument variation to the
   mollified mean square is complete and independent of Zeta23.
2. The restriction `theta < 4/7` comes from two explicit error exponents,
   not from the numerical optimization.
3. The numerical step can be made with one explicit rational polynomial;
   it does not need the paper's nonconstructive sentence that the optimal
   hyperbolic-sine function can be approximated by polynomials.
4. The deepest external input is a Deshouillers--Iwaniec averaged
   Kloosterman estimate.  Its proof uses the spectral theory developed in
   their 1982 Inventiones paper.  A no-axiom Lean proof therefore requires
   much more than the present zeta library.

The paper proof may regard the published Deshouillers--Iwaniec theorem as a
proved input.  The later Lean audit may not silently replace it by an axiom.

## 1. Sources and exact dependency chain

The principal source is J. B. Conrey, *More than two fifths of the zeros of
the Riemann zeta function are on the critical line*, J. reine angew. Math.
399 (1989), 1--26, DOI `10.1515/crll.1989.399.1`.

The places where that paper cites earlier work were checked against:

* R. Balasubramanian, J. B. Conrey, and D. R. Heath-Brown,
  *Asymptotic mean square of the product of the Riemann zeta-function and a
  Dirichlet polynomial*, J. reine angew. Math. 357 (1985), 161--181,
  DOI `10.1515/crll.1985.357.161`;
* J. B. Conrey, *Zeros of derivatives of Riemann's xi-function on the
  critical line*, J. Number Theory 16 (1983), 49--74,
  DOI `10.1016/0022-314X(83)90031-8`;
* J.-M. Deshouillers and H. Iwaniec, *Power mean-values for Dirichlet's
  polynomials and the Riemann zeta-function, II*, Acta Arith. 43 (1984),
  305--312, DOI `10.4064/aa-43-3-305-312`;
* J.-M. Deshouillers and H. Iwaniec, *Kloosterman sums and Fourier
  coefficients of cusp forms*, Invent. Math. 70 (1982), 219--288,
  DOI `10.1007/BF01390728`.

Conrey's bibliography prints the Acta Arithmetica volume as `48`; the
publisher record and DOI identify it as volume `43`.

## 2. The xi-function and argument variation

Write

\[
  \xi(s)=H(s)\zeta(s),\qquad
  H(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2),
  \qquad L=\log T.
\]

Choose a fixed integer `N`, a nonzero real `g`, and coefficients `g_n` with
the parity conditions in Conrey's equation (18), and set

\[
  \eta(s)=g\xi(s)+\sum_{n=0}^N g_n L^{-n}\xi^{(n)}(s).
\]

On the critical line, even xi derivatives are real and odd derivatives are
purely imaginary.  The parity choice gives

\[
  \operatorname{Re}\eta(\tfrac12+it)=g\xi(\tfrac12+it).
\]

Thus every interval in which the argument of `eta` changes by `pi` contains
a critical-line zero of xi.  Factoring `eta=H V_1`, Stirling's formula gives

\[
  \Delta\arg H(\tfrac12+it)
   =\frac T2\log T+O(T),
\]

while the argument principle gives

\[
  \Delta\arg V_1(\tfrac12+it)
   =-2\pi N_{V_1}^*(T)+O(T).
\]

Here zeros to the right of the critical line count fully and zeros on the
line count with weight one half.  Therefore an upper bound for right-half
plane zeros of `V_1` yields a lower bound for critical-line sign changes.

The differential-polynomial approximation is

\[
  V(s)=Q\!\left(-\frac1L\frac d{ds}\right)\zeta(s),
\]

where `Q(0)=1` and

\[
  Q(z)+\overline{Q(1-\bar z)}=g.
  \tag{Q-sym}
\]

For real coefficients this reduces to `Q(z)+Q(1-z)=g`.  Conrey's 1983
Lemma 1 supplies the uniform logarithmic-derivative asymptotics for `H`
which justify replacing `V_1` by `V` at the required scale.

## 3. Mollifier and Littlewood lemma

Fix `R>0`, put

\[
  \sigma_0=\frac12-\frac R L,\qquad
  y=T^\theta,
\]

and use the Levinson--Conrey mollifier

\[
  B(s,P)=\sum_{n\le y}
   \frac{\mu(n)P\!\left(\frac{\log(y/n)}{\log y}\right)
         n^{\sigma_0-1/2}}{n^s},
  \qquad P(0)=0,\quad P(1)=1.
\]

Multiplication by `B` cannot remove a zero of `V_1`.  Littlewood's lemma on
the rectangle with left edge `sigma_0`, followed by arithmetic--geometric
mean, gives

\[
  2\pi N_{V_1B}(T)
  \le \frac{TL}{2R}
       \log\!\left(
       \frac1T\int_1^T|V_1B(\sigma_0+it)|^2dt\right)+O(T).
\]

Consequently

\[
  \kappa\ge
  1-\frac1R\log\!\left(
       \frac1T\int_1^T|VB(\sigma_0+it)|^2dt\right)+o(1).
  \tag{L}
\]

For simple zeros there is one additional restriction: `Q` must have degree
one.  Then `eta` has the form

\[
  \eta=g\xi+g_0\xi+g_1L^{-1}\xi'.
\]

At a point where `Re eta=0` but `eta!=0`, xi vanishes and xi prime does not;
hence the zero is simple.  The line-zero correction in Conrey's equations
(40)--(43) gives the genuine simple-zero inequality

\[
  \boxed{
  \kappa^*\ge
  1-\frac1R\log\!\left(
       \frac1T\int_2^T|VB(\sigma_0+it)|^2dt\right)+o(1).}
  \tag{L*}
\]

This is the point at which a theorem merely asserting “some positive
critical-line proportion” is insufficient: multiplicity and the
degree-one condition on `Q` are part of the theorem.

## 4. The mollified mean-value theorem

Conrey's Theorem 2 states that, for fixed `R`, fixed polynomials `P,Q`, and
`theta<4/7`,

\[
  \int_2^T|VB(\sigma_0+it)|^2dt
    \sim c(P,Q,R,\theta)T,
  \tag{MV}
\]

where

\[
\begin{aligned}
 c(P,Q,R,\theta)
  &=|P(1)Q(0)|^2 \\
  &\quad+\frac1\theta\int_0^1\!\int_0^1
    e^{2Ry}\left|
      Q(y)P'(x)+\theta Q'(y)P(x)
      +\theta RQ(y)P(x)
    \right|^2dx\,dy.
\end{aligned}
\tag{C}
\]

The proof is best separated into the following exact ledger.

### C1. Gaussian localization and shifted moment

Let `Delta=T^(1-delta)` and `s_0=1/2+iw`, with `T<=w<=2T`.  Introduce the
Gaussian-smoothed shifted integral

\[
 g(a,b,w,P_1,P_2)=\frac1{i\Delta\sqrt\pi}
 \int_{(1/2)} e^{(s-s_0)^2\Delta^{-2}}
 \zeta(s+a/L)\zeta(1-s+b/L)
 \mathcal B(s,P_1)\mathcal B(1-s,P_2)\,ds.
\]

The proposition on Conrey 1989, page 11, evaluates this uniformly as

\[
\begin{aligned}
g&=P_1(1)P_2(1)\\
 &\quad+\frac1\theta\int_0^1e^{-(a+b)y}dy
 \left.\partial_u\partial_v
 \left(e^{-a\theta u-b\theta v}
 \int_0^1P_1(x+u)P_2(x+v)dx\right)
 \right|_{u=v=0}+o(1).
\end{aligned}
\tag{G}
\]

Applying `Q(-d/da)` and its conjugate, then setting `a=b=-R`, gives the
localized version of (MV).  The passage from uniform Gaussian local means
to the integral on `[2,T]` is the argument of BCH 1985, Section 3.

### C2. Arithmetic main term

For `alpha=a/L`, `beta=b/L`, define

\[
 \Sigma(\alpha,\beta,P_1,P_2)
 =\sum_{h,k\le y}
  \frac{b(h,P_1)b(k,P_2)}{h^{1+\alpha}k^{1+\beta}}
  (h,k)^{1+\alpha+\beta}.
\]

Conrey's Lemma 1 gives

\[
 \Sigma\sim\frac1{\theta L}
 \int_0^1(P_1'(x)+a\theta P_1(x))
          (P_2'(x)+b\theta P_2(x))\,dx.
\tag{A}
\]

This is not a bare citation after the present source recovery.  Its proof is
the gcd/Mobius reindexing from Conrey 1983, Section 6, followed by that
paper's Lemmas 10 and 11.  Lemma 10 is the contour evaluation of the tapered
Mobius sum after factoring `1/(zeta(s)F(j,s))`; Lemma 11 is the required
Euler-product partial sum.  The zero-free line and reciprocal bounds for
zeta enter in the contour shift.

### C3. Functional equation and separation of the main term

Moving the shifted contour and using the Estermann-type functional equation
splits the integral into `M_i+R_i+E_i`.  The two `M_i` terms give exactly

\[
  \frac{\Sigma(b,a,P_1,P_2)
       -e^{-a-b}\Sigma(-a,-b,P_1,P_2)}{\alpha+\beta},
\]

which, together with (A), is (G).  The residues `R_i` are rapidly decaying
because of the Gaussian factor.

### C4. The nonzero modes

After dyadic decomposition, the remaining error is reduced to sums

\[
 \mathcal M(N,U,V)=
 \sum_{n\asymp N}\frac{\delta(n)}{n^s}
 \sum_{u\asymp U}\sum_{v\asymp V}
 \frac{b(ug,P_1)b(vg,P_2)}
      {u^{1-s+\beta}v^{1-s+\alpha}}
 e\!\left(\frac{n\bar u}{v}\right),
\]

with `(u,v)=1`.  Vaughan's identity splits the Mobius coefficient into
three pieces.  The long bilinear piece is bounded by the following special
case of Deshouillers--Iwaniec 1984, Lemma 1:

\[
\begin{aligned}
 &\sum_{v\asymp V}\sum_{b\asymp B,(b,v)=1}
 \left|\sum_{n\asymp N}\sum_{a\asymp A,(a,v)=1}
 c(a,n)e\!\left(\frac{n\bar a\bar b}{v}\right)\right|\\
 &\quad\ll_\varepsilon (NUV)^{1/2+\varepsilon}
 \left{(UVA^{-1})^{1/2}
 +(A+N)^{1/4}
 [UVA^{-1}(N+A)(V+A^2)+NU^2]^{1/4}\right\}.
\end{aligned}
\tag{DI}
\]

Conrey's Lemma 8 then gives, for `y<=T^(8/13)`,

\[
 \mathcal M(N,U,V)
 \ll (1+|s|)(TN)^\varepsilon y^{2\eta}T^cN^{-\eta}
 \left(T^{-1/2}y^{7/8}+T^{-1}y^{7/4}\right).
\tag{M8}
\]

The short piece is handled by Weil's pointwise Kloosterman bound.  The proof
of (DI) in the 1984 paper invokes Theorem 12 of Deshouillers--Iwaniec 1982;
that is the spectral Kloosterman input at the bottom of the dependency tree.

## 5. Why the mollifier length is `theta<4/7`

Conrey's Lemma 7 bounds the analytic kernel by

\[
 \iint(1+|s|)|G|\ll
 \Delta^{-c-5/2}T^{5/2+\eta+\varepsilon}.
\]

Combining it with (M8), summing all dyadic boxes, taking
`Delta=T^(1-delta)` and `eta=epsilon/2`, gives

\[
 Z\ll
 \Delta^{-7/2}T^{5/2+o(1)}
 \left(T^{1/2}y^{7/8}+y^{7/4}\right).
\tag{E}
\]

For `y=T^theta`, the two powers of `T`, ignoring arbitrarily small positive
losses, are

\[
 -\frac12+\frac{7\theta}{8},
 \qquad
 -1+\frac{7\theta}{4}.
\]

Both are negative exactly when

\[
  \boxed{\theta<\frac47.}
\]

The auxiliary assumption `y<=T^(8/13)` in Lemma 8 is weaker because
`4/7<8/13`.  Thus no endpoint theorem at `theta=4/7` is used: all numerical
choices at `4/7` are limits from below.

## 6. An explicit rational certificate for more than two-fifths

The original paper minimizes (C) first over a non-polynomial function and
then invokes polynomial approximation.  That is mathematically valid, but
it is an avoidable nuisance for formalization.  Use instead

\[
 \boxed{
 \theta=\frac{571}{1000},\quad
 R=\frac65,\quad
 Q(y)=1-\frac{51}{50}y,\quad
 P(x)=\frac{84x+15x^3+x^5}{100}.}
\tag{P-explicit}
\]

These satisfy

\[
  7\cdot571=3997<4000,
  \qquad P(0)=0,\quad P(1)=1,\quad Q(0)=1,
\]

and `Q` has degree one.  Direct polynomial integration in (C) gives

\[
 \int_0^1\left|
 Q(y)P'(x)+\theta Q'(y)P(x)+\theta RQ(y)P(x)
 \right|^2dx
 =\frac{
  103851307011369636y^2
 -158615980968417540y
 +61041728800527025}
 {54140625000000000},
\]

and hence

\[
 c=
 -\frac{7119751197749681}{5935545000000000}
 +\frac{43767545344030157}{148388625000000000}e^{12/5}.
\tag{c-exact}
\]

No floating-point assertion is needed.  Taylor's formula with positive
terms and a geometric bound for the tail gives

\[
 e^{12/5}<\frac{110231764}{10^7}
\]

after 13 terms, and

\[
 e^{18/25}>\frac{20544332}{10^7}
\]

after 10 terms.  Substitution in (c-exact) yields

\[
 c<
 \frac{253719660815417568775579}
      {123657187500000000000000}
 <\frac{20544332}{10^7}<e^{18/25}.
\]

The rational margin in the middle inequality is

\[
 \frac{325770603207431224421}
      {123657187500000000000000}>0.
\]

Since `18/25=(3/5)R`, (L*) and (MV) give

\[
 \kappa^*
 \ge 1-\frac{\log c}{R}
 >1-\frac35=\frac25.
\]

Numerically, only as a consistency check,

\[
 c=2.0517987287\ldots,
 \qquad
 1-\frac{\log c}{R}=0.4010693024\ldots.
\]

The strict rational certificate, not these decimals, is the future Lean
target.

## 7. What is closed mathematically, and what is not yet in Lean

### Paper-level closure

Assuming the published Deshouillers--Iwaniec spectral Kloosterman theorem,
the route is paper-closed:

1. xi parity converts argument change to critical-line zeros;
2. the degree-one condition converts the surviving zeros to simple zeros;
3. Littlewood's lemma reduces the proportion to a mollified mean square;
4. the shifted Gaussian proposition evaluates that mean square for every
   fixed `theta<4/7`;
5. (E) makes all nonzero modes `o(1)`;
6. the explicit rational choice (P-explicit) gives a strict value above
   `2/5`.

No RH, zero-density theorem, Zeta23 bridge, Farmer all-length mollifier
conjecture, or length-`T^3` moment is used.

### Dependencies still absent from the Lean library

A genuine no-axiom formalization still needs at least the following layers.

1. Riemann--von Mangoldt counting with multiplicity and a separate count of
   simple critical-line zeros.
2. Xi derivatives on the critical line, their real/imaginary parity, and
   argument-change zero counting.
3. The argument principle and Littlewood lemma on rectangles with the
   boundary-zero conventions used above.
4. Differential polynomials in zeta and the uniform Stirling estimates for
   derivatives of `H`.
5. Gaussian contour localization and the shifted two-zeta functional
   equation calculation.
6. The Mobius-taper arithmetic asymptotic (A), including the zero-free line
   and reciprocal zeta bounds used in the contour shift.
7. Vaughan's identity, dyadic decomposition, partial summation, and Weil's
   Kloosterman bound.
8. The Deshouillers--Iwaniec averaged Kloosterman theorem (DI).  Proving this
   rather than postulating it requires the Kuznetsov/spectral cusp-form
   machinery underlying their 1982 Theorem 12.
9. The elementary exact integration and exponential Taylor bounds from
   Section 6.  This item is now formalized; see Section 10.

Items 8 and the analytic argument-principle infrastructure dominate the
formalization cost.  Starting Lean before fixing this ledger would merely
move uncertainty into opaque hypotheses.

## 8. Independent audit verdict

The reconstructed proof was checked against the displayed formulas in all
four dependency papers listed in Section 1.

* **Counting convention: pass.**  The denominator is von Mangoldt's `N(T)`;
  the numerator is Conrey's `N_0^*(T)`, defined by `beta=1/2` and
  `zeta'(rho)!=0`.  It is not the repository's present distinct-zero count.
* **Simple-zero implication: pass.**  It uses the degree-one restriction on
  `Q` and the subtraction of line zeros in equations (40)--(43), not merely
  the sign changes used for `kappa`.
* **Endpoint discipline: pass.**  The mean-value theorem is used at the
  explicit value `571/1000<4/7`; no theorem at `theta=4/7` is assumed.
* **Error exponents: pass.**  Both terms in (E) independently impose
  `theta<4/7`; the auxiliary `8/13` condition is respected.
* **Arithmetic main term: pass at paper level.**  The 1989 sketch resolves
  to Conrey 1983, Lemmas 10 and 11, including the zero-free-line input.
* **Kloosterman input: pass as a published theorem boundary.**  Conrey's
  Lemma 9 is the displayed special case of Deshouillers--Iwaniec 1984,
  Lemma 1.  That lemma explicitly invokes the 1982 spectral Theorem 12.
* **Numerical strictness: pass.**  The exact rational calculation and Taylor
  tails give a positive rational margin before taking logarithms.
* **Current Lean target: fail as a Conrey statement.**  It says only that an
  unspecified positive proportion exists and is definitionally Selberg's
  target.

Thus the mathematical route is accepted modulo a clearly named, already
published spectral theorem.  The no-axiom Lean route is not yet closed,
because that theorem and the required argument-principle infrastructure are
not in the current library.

## 9. Formalization boundary

### Current repository name is not the theorem

The present definition in `RiemannExplorer.lean` is only

```text
exists c > 0, exists T0, forall T >= T0,
  zeroCountOnCriticalLine T >= c * (T / (2*pi) * log T).
```

It is definitionally identical to the Selberg positive-proportion target;
the two directions are proved by `Iff.rfl`.  It has no constant `2/5`, does
not count all zeros with multiplicity in the denominator, and has no simple
critical-line zero count in the numerator.  Therefore it is not a statement
of Conrey's theorem.

The header comment in `RiemannExplorer/Conrey40.lean` also attributes the
result to “Conrey 2003” and mentions `0.4017`.  The theorem audited here is
Conrey 1989; its stated simple-zero result is `kappa* >= 0.401`, with the
worked numerical value `0.4013...`.  The explicit rational certificate in
Section 6 gives `0.401069...`, which is slightly weaker than the paper's
decimal but still strictly above `2/5` and much easier to formalize.

These naming and documentation problems should be corrected only after the
new multiplicity-sensitive target has been introduced, so existing callers
are not silently reinterpreted.

### Order of implementation

The first Lean slice should begin only after the independent mathematical
audit accepts Sections 2--6.  When it begins, the order should be:

1. formalize the exact rational numerical certificate from Section 6;
2. define the correct multiplicity-sensitive counts and state (L*);
3. formalize the elementary mollifier algebra and the constant formula (C);
4. formalize the contour/mean-value route from the outside inward;
5. isolate (DI) as a named theorem boundary, never as “Conrey 40%” itself;
6. decide explicitly whether the project will formalize the spectral theorem
   or declare that the final theorem is conditional on that imported input.

Until step 6 is decided, the repository must not label an `Iff.rfl` bridge or
an existence of an unspecified positive constant as “Conrey 40%”.

## 10. First Lean certificate implemented

After the mathematical and independent audits above passed, the first item in
the implementation order was added as
`HardyTheorem/ConreyExplicitCertificate.lean`, with a separate contract in
`Test/ConreyExplicitCertificateContract.lean`.

The checked statements are exactly:

1. `571/1000 < 4/7`;
2. the explicit constant in Section 6 is less than `exp(18/25)`;
3. with `R=6/5`, this implies
   `2/5 < 1 - log(c)/R`.

The exponential comparisons are not floating-point evaluations.  Lean checks
the upper bound by applying a finite Taylor remainder bound to `exp(4/5)` and
cubing it, and checks the lower bound by a finite Taylor sum for `exp(18/25)`.
The remaining comparisons are exact rational arithmetic.  The axiom audit
reports only Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.

The next elementary slice is now implemented in
`HardyTheorem/ConreyExplicitIntegralBridge.lean`, with its public contract in
`Test/ConreyExplicitIntegralBridgeContract.lean`.  Lean checks, from the
displayed rational choices of `P`, `Q`, `theta`, and `R`, that

1. `conreyExplicitKernel` is the degree-five polynomial obtained from the
   differential expression in (C);
2. `conreyExplicitInnerIntegral_eq` evaluates its squared `x` integral to the
   exact quadratic polynomial displayed in Section 6;
3. `conreyExplicitMeanSquareIntegral_eq_constant` evaluates the remaining
   exponential `y` integral to the certified closed form; and
4. `conreyExplicitIntegralProportion_gt_two_fifths` derives the strict
   `2/5` inequality from that actual integral.

Thus the elementary integration and numerical layer is closed in Lean, with
only Mathlib's standard logical axioms in the audit.  It still does **not**
contain the analytic mean-square theorem or the Deshouillers--Iwaniec spectral
input.

## 11. Exact repository target for the genuine theorem

The repository already has the right denominator in
`PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount T`: it sums analytic
multiplicity over nontrivial zeros satisfying

\[
  0<\operatorname{Im}\rho\le T.
\]

To match Conrey's numerator without importing the unrelated Zeta23 route,
define the positive simple critical-line finset by filtering that same ambient
finset with

\[
  \operatorname{Re}\rho=\frac12,
  \qquad
  \operatorname{ord}_{\rho}\zeta=1.
\]

Its cardinality is exactly the desired `N_0^*(T)`.  In particular, using the
same ambient finset makes the endpoint convention identical in numerator and
denominator and avoids the repository's older `[0,T]` distinct-ordinate API.

Rather than forming a quotient when `N(T)` might vanish at small height, the
Lean target should be the eventual inequality

\[
  \exists c\in\mathbb R,\quad \frac25<c
  \quad\text{and}\quad
  \forall^\infty T,\qquad
  c\,N(T)\le N_0^*(T).
\tag{Conrey-target}
\]

This is the direct denominator-free form of the strict liminf statement.  It
also records the essential distinction from Selberg: `c` is not merely
positive, the numerator counts only simple critical-line zeros, and the
denominator counts every nontrivial zero with analytic multiplicity.

This count and target layer is now implemented in
`HardyTheorem/ConreySimpleZeroCount.lean`.  Lean also checks monotonicity and
the sanity bound `N_0^*(T) ≤ N(T)`.

The explicit integral certificate supplies a real number strictly larger than
`2/5`.  The remaining analytic proof must show that every smaller constant is
eventually a lower bound for `N_0^*(T)/N(T)`.  That implication is where the
argument-principle, mollified mean-square, and spectral Kloosterman layers enter;
the definition of (Conrey-target) itself must not assume any of them.

`HardyTheorem/ConreyTwoFifthsBridge.lean` exposes this exact remainder as the
proposition `conreyExplicitAnalyticLowerBound`.  It then proves
`conreyTwoFifthsSimpleZerosTarget_of_explicit_analytic_lower_bound` by choosing
the midpoint between `2/5` and the certified integral proportion.  The bridge
is an ordinary implication with an explicit hypothesis, not a postulated
analytic theorem.  Consequently the code now cleanly separates:

\[
  \text{unproved analytic lower bound}
  \quad\Longrightarrow\quad
  \text{proved logical bridge}
  \quad\Longrightarrow\quad
  \text{genuine Conrey target}.
\]

## 12. Constant-exact Littlewood mean-square bridge implemented

The next proved slice is the arithmetic--geometric mean step that Conrey uses
after obtaining the mollified second moment.  It is now formalized generically
in `MathlibAux/LogMeanSquare.lean` and specialized to complex boundary
functions in `HardyTheorem/ConreyLittlewoodMeanSquare.lean`.

If `F : R -> C` is continuous and nonzero on `[a,b]`, with `a<b`, Lean checks

\[
  2\int_a^b \log|F(t)|\,dt
  \le (b-a)\log\!\left(
    \frac{1}{b-a}\int_a^b |F(t)|^2\,dt
  \right).
\]

The proof preserves the constant exactly.  For a positive continuous real
function `f`, it applies Jensen's inequality to `exp` and the interval average,
then takes logarithms.  Specializing to `f(t)=|F(t)|^2` gives the factor `2`.
Consequently, an input bound

\[
  \int_a^b |F(t)|^2\,dt \le C(b-a), \qquad C>0,
\]

implies

\[
  2\int_a^b \log|F(t)|\,dt \le (b-a)\log C
\]

with no auxiliary multiplicative loss.  The contract
`Test/ConreyLittlewoodMeanSquareContract.lean` checks both public statements;
its axiom audit reports only Mathlib's standard `propext`,
`Classical.choice`, and `Quot.sound`.

This closes only the Jensen/AGM arrow

\[
  \text{mollified mean-square upper bound}
  \Longrightarrow
  \text{left-edge logarithmic integral upper bound}.
\]

The long mollified mean-square estimate itself, its Mobius arithmetic, and the
Deshouillers--Iwaniec/Kuznetsov spectral input remain open.  No theorem in this
slice assumes any of those statements.

## 13. Degree-one eta simple-zero implication implemented

Conrey's equation (42) is now formalized in
`HardyTheorem/ConreyDegreeOneEta.lean`, with an independent public contract in
`Test/ConreyDegreeOneEtaContract.lean`.

The definition encodes the degree-one parity conditions directly:

\[
  \eta(s)=g\xi(s)+i g_0\xi(s)+(g_1/L)\xi'(s),
  \qquad g,g_0,g_1,L\in\mathbb R.
\]

Using the functional equation and conjugation symmetry, Lean proves on
`s=1/2+it` that `xi(s)` is real and `xi'(s)` is purely imaginary.  It then
checks the exact identity

\[
  \operatorname{Re}\eta(\tfrac12+it)
    =g\operatorname{Re}\xi(\tfrac12+it).
\]

Therefore, if `g` is nonzero, `Re eta(s)=0`, and `eta(s)` itself is nonzero,
then `xi(s)=0` while `xi'(s)` is nonzero.  The analytic-order theorem gives
order one for completed zeta, and the existing critical-strip factorization
transfers both the zero and its order to `riemannZeta`.  The result is exactly

\[
  \zeta(\tfrac12+it)=0,
  \qquad \operatorname{ord}_{1/2+it}\zeta=1.
\]

This closes the local simple-zero implication needed in equation (42).  It
does not yet count the relevant argument crossings: the Littlewood
rectangle/argument-variation inequality and the long mollified mean-square
estimate, including the Deshouillers--Iwaniec spectral input, remain open.

## 14. Zero-free argument-crossing engine implemented

The topological crossing mechanism on the left-hand side of Conrey's equation
(41) is now isolated in `MathlibAux/ArgumentCrossing.lean`, with its public
contract in `Test/ArgumentCrossingContract.lean`.

For a continuous nonvanishing curve

\[
  \gamma:[0,1]\longrightarrow \mathbb C^\times,
\]

the construction lifts `gamma` through the covering map
`Complex.exp : C -> C^x`, normalized by `log (gamma 0)`.  Thus it supplies a
continuous logarithm `Lambda` satisfying

\[
  e^{\Lambda(t)}=\gamma(t),\qquad
  \Lambda(0)=\log\gamma(0).
\]

If a level `pi/2 + k pi` lies between the two endpoint imaginary parts, the
intermediate value theorem gives a time `t_k` with

\[
  \operatorname{Im}\Lambda(t_k)=\frac\pi2+k\pi,
  \qquad \operatorname{Re}\gamma(t_k)=0.
\]

For every finite set of such integers, Lean also chooses these crossing times
simultaneously and proves that `k -> t_k` is injective.  The injectivity step is
essential: it turns distinct lifted argument levels into genuinely distinct
real-part crossings, rather than merely repeated existence claims.

The admissible levels are now packaged as the exact integer interval

\[
  K(\alpha,\beta)=
  \left\{k\in\mathbb Z:
    \alpha\le \frac\pi2+k\pi\le\beta\right\}.
\]

Floor/ceiling arithmetic gives the unconditional quantitative estimate

\[
  \frac{\beta-\alpha}{\pi}-1\le \#K(\alpha,\beta).
\]

No monotonicity assumption `alpha <= beta` is required: when the net argument
change is negative, the left-hand side is already negative and the empty
crossing family is valid.  Consequently every zero-free component contributes
its signed argument change divided by `pi`, with exactly one endpoint-rounding
loss.  This is the form that can be summed after partitioning at the zeros of
`eta`.

This is an unconditional zero-free-interval theorem.  It does not yet prove
the full inequality (41): to apply it to `eta` one must partition the critical
line at the finitely many zeros of `eta`, reconcile the lifts on the resulting
zero-free components, and account for the loss `N_{0,eta}(T)`.  The rectangle
argument estimate and the long mollified mean-square/spectral estimate also
remain open.

## 15. Equation-(40) half-weighted multiplicity algebra implemented

The finite multiplicity algebra in the last inequality of Conrey's equation
(40) is now formalized in `MathlibAux/HalfWeightedMultiplicity.lean`, with its
public contract in `Test/HalfWeightedMultiplicityContract.lean`.

For a finite zero family `S`, a distinguished boundary, and analytic
multiplicities `m(rho)`, define the half-weighted mass by giving boundary zeros
weight `m(rho)/2` and all other zeros weight `m(rho)`.  Lean proves the exact
identity

\[
  2N^*(S)=2N(S)-N_{\partial}(S).
\]

It also proves monotonicity under enlargement of the zero family together with
pointwise growth of multiplicities.  Finally, if the boundary multiplicity
mass of the `V_1` zeros is at most the boundary mass of the product zeros, the
formalized inequality is

\[
  -2N(V_1B)+N_{0,V_1}
  \le -2N^*(V_1B),
\]

which is exactly the direction needed between the second and third lines of
(40).  The coefficient `1/2`, analytic multiplicities, and the inequality
direction are all exposed in the contract.

This closes only the finite counting algebra.  The next layer must define the
actual `V_1` and `B` zero families on Conrey's rectangle, prove the product-zero
and multiplicity inclusions, and connect their full count to the existing
Littlewood weighted rectangle identity.  The asymptotic edge estimates remain
separate.

## 16. The actual degree-one `V_1` factor implemented

The analytic object occurring before Conrey's mollifier is now defined in
`HardyTheorem/ConreyDegreeOneV1.lean`, with its public contract in
`Test/ConreyDegreeOneV1Contract.lean`.  With

\[
  H(s)=\frac12s(s-1)\Gamma_{\mathbb R}(s)
\]

and the degree-one choice from Section 13, the definition is

\[
  V_1(s)=(g+i g_0)\zeta(s)
    +\frac{g_1}{L}\left(\zeta'(s)+\frac{H'(s)}{H(s)}\zeta(s)\right).
\]

Lean proves, throughout the open critical strip `0 < re s < 1`, that `H` is
analytic and nonzero and that

\[
  \xi(s)=H(s)\zeta(s),\qquad
  \eta(s)=H(s)V_1(s).
\]

The nonvanishing of `H` then gives both the pointwise equivalence

\[
  \eta(s)=0\quad\Longleftrightarrow\quad V_1(s)=0
\]

and equality of their analytic orders at `s`.  Thus the zero family denoted by
`N_{0,V_1}` in equation (40) is now connected exactly, including
multiplicity, to the `eta` whose critical-line crossings feed equation (41).

This factorization is the analytic input used by the finite-rectangle count in
Section 17.  The connection from that bounded count to the Littlewood weighted
rectangle identity remains to be constructed.  The horizontal and left-edge
asymptotics and the long mollified mean-square estimate also remain open.

## 17. Conrey's actual mollifier and the local equation-(35) inclusion

The definitions in equations (1) and (33) have now been checked directly
against the primary source and implemented in
`HardyTheorem/ConreyMollifierProduct.lean`, with their public contract in
`Test/ConreyMollifierProductContract.lean`.  For a cutoff `Y`, shift `sigma0`,
and normalized polynomial `P`, the coefficient and mollifier are

\[
 b(n,P)=\mu(n)P\!\left(\frac{\log(Y/n)}{\log Y}\right),
 \qquad
 B(s,P)=\sum_{n\le Y}
   \frac{b(n,P)n^{\sigma_0-1/2}}{n^s}.
\]

For `Y >= 2` and `P(1)=1`, Lean proves that the `n=1` coefficient is exactly
one.  The finite Dirichlet polynomial `B` is entire, tends to one on the
positive real axis, is not identically zero, and therefore has finite analytic
order at every point.

The earlier analyticity result for `V_1` has also been extended from the open
critical strip to the full domain needed by the paper:

\[
  \operatorname{Re}s>0,\qquad s\ne1.
\]

In particular it applies throughout Conrey's zero-counting half-strip
`sigma >= 1/2`, `t > 0`; the pole location `s=1` is excluded automatically by
positive height.  Defining the actual product

\[
  (V_1B)(s)=V_1(s)B(s,P),
\]

Lean proves pointwise that every zero of `V_1` remains a zero of `V_1B`.  At
every point where `V_1` has finite analytic order, it proves the
multiplicity-sensitive form

\[
  \operatorname{ord}_s V_1
    \le \operatorname{ord}_s(V_1B),
\]

using the exact product-order identity and the now-proved finiteness of the
mollifier order.  This is the local analytic content of equation (35), not a
cardinality-only surrogate.

The finite-order premise has now also been discharged for Conrey's
nondegenerate degree-one choice.  In
`HardyTheorem/ConreyDegreeOneNontrivial.lean`, with its contract in
`Test/ConreyDegreeOneNontrivialContract.lean`, Lean first proves that `eta` is
entire.  If `g != 0`, choose a positive good height `T` and put
`s=1/2+iT`.  The good-height condition makes `zeta(s)` nonzero, hence
`xi(s)` is nonzero; critical-line symmetry makes `xi(s)` real, and therefore

\[
  \operatorname{Re}\eta(s)=g\,\xi(s)\ne0.
\]

Thus `eta` is not identically zero and has finite analytic order everywhere.
The factorization `eta=H V_1` and nonvanishing of `H`, now proved throughout
`Re s > 0`, `s != 1`, transfer finite order to `V_1`.  Consequently the local
equation-(35) multiplicity inequality above is available from the actual
coefficient hypothesis `g != 0`, with no auxiliary `V_1` finite-order
assumption.

The first global step is now complete in
`HardyTheorem/ConreyMollifierRectangleCount.lean`, with its contract in
`Test/ConreyMollifierRectangleCountContract.lean`.  On the compact rectangle

\[
  1/2\le \operatorname{Re}s\le A,\qquad 0\le \operatorname{Im}s\le T,
\]

Lean uses the entire functions `eta` and `eta B` to obtain finite divisor
supports without inserting a lower cutoff that would obscure the point
`s=1`.  On positive height their zeros are exactly those of the actual
functions `V_1` and `V_1B`.  After filtering to `0<t<=T`, the two finite zero
families are counted with their actual analytic multiplicities and weight
`1/2` precisely on `Re s=1/2`.  Summing the local product-order inequality
therefore proves the bounded equation-(35) inequality

\[
  N^*_{V_1}(A,T)\le N^*_{V_1B}(A,T).
\]

This is not yet the unbounded half-strip count printed in the paper.  Its sole
remaining equation-(35) step is to prove a uniform far-right zero-free edge
and choose `A` beyond it.  Littlewood's inequality (37) and all of its edge
asymptotics remain separate, as does the long mollified mean-square theorem.

## 18. Uniform far-right zero-free design for equation (35)

The right boundary can be removed uniformly in the ordinate; no boundary
depending on `T` is necessary.  The key observation is a lower bound for the
real part of the digamma function that is uniform in the imaginary part.
For `z=x+iy`, `x>0`, Gauss' series has summand

\[
 d_k(z)=\frac1k-\frac1{z+k}=\frac{z}{k(z+k)},\qquad k\ge1.
\]

Direct calculation gives

\[
 \operatorname{Re}d_k(z)
 =\frac{x(x+k)+y^2}{k((x+k)^2+y^2)}
 \ge \frac{x}{k(x+k)}.
\]

Hence every summand has nonnegative real part, and if `x>=N`, the first `N`
summands contribute at least

\[
 \sum_{k=1}^N\operatorname{Re}d_k(z)
 \ge \frac12\sum_{k=1}^N\frac1k=\frac12H_N.
\]

Since `Re(z^{-1})<=1` for `x>=1`, Gauss' identity implies

\[
 \operatorname{Re}\psi(z)
 \ge-\gamma-1+\frac12H_N\qquad(x\ge N).
\]

The divergence of `H_N` therefore proves

\[
 \forall M\in\mathbb R\;\exists A\;\forall z\in\mathbb C,
 \quad A\le\operatorname{Re}z
 \Longrightarrow M\le\operatorname{Re}\psi(z),
 \tag{D-right}
\]

uniformly for all imaginary parts.

Logarithmic differentiation of
`H(s)=s(s-1)Gamma_R(s)/2` gives, on `Re s>1`,

\[
 \frac{H'(s)}{H(s)}
 =\frac1s+\frac1{s-1}-\frac12\log\pi+rac12\psi(s/2).
\]

The first two rational terms have nonnegative real part.  Thus (D-right)
shows that `Re(H'/H)` tends uniformly to positive infinity as `Re s` tends
to infinity.  On the other hand the already-proved Dirichlet-series estimate
gives, uniformly on `Re s>=3`,

\[
 \left|\frac{\zeta'(s)}{\zeta(s)}\right|\le2\zeta(2).
\]

Put `c=g_1/L`.  Since zeta is nonzero on this half-plane,

\[
 V_1(s)=\zeta(s)\left[g+ig_0+c\left(
   \frac{\zeta'(s)}{\zeta(s)}+\frac{H'(s)}{H(s)}\right)\right].
\]

If `c=0`, the bracket is `g+ig_0`, nonzero because `g!=0`.  If `c!=0`,
choose the digamma threshold so that the real quantity in parentheses exceeds
`|g|/|c|`.  Its product with the real number `c` then has the sign of `c` and
magnitude greater than `|g|`; consequently the real part of the bracket
cannot vanish.  This proves one constant `A_V`, independent of height, beyond
which `V_1` has no zeros.

For the mollifier, `P(1)=1` makes the constant coefficient exactly one, while
each of the finitely many terms with `n>=2` satisfies

\[
 \left|b_n n^{-s}\right|=|b_n|n^{-\operatorname{Re}s}\longrightarrow0
\]

uniformly in `Im s`.  A finite sum gives a constant `A_B` for which
`|B(s)-1|<1`, hence `B(s)!=0`, whenever `Re s>=A_B`.  Taking
`A=max(A_V,A_B)` excludes zeros of both `V_1` and `V_1B` beyond the same
vertical line.  This argument remains wholly independent of Zeta23 and of the
later long-mollifier mean-square estimate.

## 19. Stabilized global equation (35)

The uniform right edge is now used to close the exact count interface rather
than merely recorded as an asymptotic fact.  Fix Conrey's hypotheses
`g!=0`, `Y>=2`, and `P(1)=1`, and choose one common edge `A_35` satisfying

\[
 V_1(s)\ne0,\qquad V_1(s)B(s,P)\ne0
 \quad\text{whenever }\operatorname{Re}s\ge A_{35}.
\]

Define the two half-strip zero finsets by evaluating the compact-rectangle
divisors from Section 17 at `A=A_35`.  The far-right theorem removes the
apparently retained upper bound and gives the exact membership statements

\[
\begin{aligned}
 s\in Z_{V_1}(T)
 &\Longleftrightarrow
 \tfrac12\le\operatorname{Re}s,\quad
 0<\operatorname{Im}s\le T,\quad V_1(s)=0,\\
 s\in Z_{V_1B}(T)
 &\Longleftrightarrow
 \tfrac12\le\operatorname{Re}s,\quad
 0<\operatorname{Im}s\le T,\quad V_1(s)B(s,P)=0.
\end{aligned}
\]

Thus these are finite representations of the actual unbounded half-strip
zero families, not counts whose mathematical statement still depends on an
auxiliary right boundary.  Using the union of the two finsets to identify the
critical-line boundary and the actual analytic orders as multiplicities, the
finite-rectangle inequality from Section 17 specializes to

\[
 N^*_{V_1}(T)\le N^*_{V_1B}(T),
 \tag{35-global}
\]

with weight `1/2` exactly at `Re s=1/2`.  This completes equation (35) at the
level needed by Conrey's subsequent Littlewood argument.  Equations
(37)--(40), the argument partition in (41), and the long mollified mean square
remain separate gates and are not consequences of (35-global) alone.

## 20. Exact Littlewood rectangle core and the `R/L` count factor

The finite-rectangle part of equation (37) has now been derived before any
asymptotic boundary estimate.  For an analytic function `F` whose zeros in
the ordered rectangle

\[
 [\sigma_0,A]\times[t_0,T]
\]

are the finite family `Z`, with analytic multiplicities `m(rho)`, the proved
identity is

\[
\begin{aligned}
 2\pi\sum_{\rho\in Z}(\operatorname{Re}\rho-\sigma_0)m(\rho)
 &=\int_{t_0}^{T}\log|F(\sigma_0+it)|\,dt
   -\int_{t_0}^{T}\log|F(A+it)|\,dt\\
 &\quad+\int_{\sigma_0}^{A}(\sigma-\sigma_0)
       \operatorname{Im}{F'\over F}(\sigma+it_0)\,d\sigma\\
 &\quad-\int_{\sigma_0}^{A}(\sigma-\sigma_0)
       \operatorname{Im}{F'\over F}(\sigma+iT)\,d\sigma\\
 &\quad+(A-\sigma_0)\int_{t_0}^{T}
       \operatorname{Re}{F'\over F}(A+it)\,dt.
\end{aligned}
\tag{37-exact}
\]

The proof first applies the weighted argument principle to
`(s-sigma_0)F'(s)/F(s)`, then integrates by parts on all four sides.  The
eight corner `log|F|` terms cancel exactly.  This sign audit is important:
the left vertical logarithmic integral is positive and the right vertical
one is negative; the bottom horizontal phase is positive and the top one is
negative.

For any `sigma_c >= sigma_0`, Lean also proves the independent finite-sum
inequality

\[
 (\sigma_c-\sigma_0)
 \sum_{\substack{\rho\in Z\\\operatorname{Re}\rho\ge\sigma_c}}m(\rho)
 \le
 \sum_{\rho\in Z}(\operatorname{Re}\rho-\sigma_0)m(\rho).
\tag{37-gap}
\]

With Conrey's choices `sigma_c=1/2` and
`sigma_0=1/2-R/L`, the factor on the left is exactly `R/L`.  Hence the
later `L/R` in the zero-count bound is now accounted for without an
asymptotic convention.  Jensen's inequality from Section 12 supplies the
separate factor `1/2` when the left-edge `log|F|` integral is bounded by a
second moment.

The implementation is in `PrimeNumberTheorem/LittlewoodRectangle.lean`,
with the public contract
`Test/ConreyLittlewoodRectangleContract.lean`.  It also repairs the two
stale rectangle-membership conversions that had prevented this existing
argument-principle chain from building.

This does **not** yet assert Conrey's `O(T/L)` boundary estimate.  To obtain
the displayed inequality in Section 3 for
`F=V_1B`, the remaining equation-(37) work is now exactly:

1. bound the bottom and top weighted phase integrals;
2. bound the far-right argument variation (the moving-right-edge `log|F|`
   integral is now closed in Section 23.4);
3. pass from a boundary-zero-free sequence of heights to every `T` with a
   controlled endpoint error;
4. only then combine (37-exact), (37-gap), and the already proved
   mean-square/Jensen bridge.

The qualitative far-right zero exclusion in item 2 is already available:
`HardyTheorem/ConreyFarRight.lean` proves that the actual degree-one `V_1`,
the normalized finite mollifier `B`, and `V_1 B` are nonzero on one common
right half-plane, uniformly in height.  What is still missing for (37) is
quantitative decay as the right edge tends to `+infinity` and a uniform
bound for the two horizontal phase integrals at admissible heights.  Thus the
next proof should extend the existing far-right module; it should not replace
the actual product by an abstract zero-free surrogate.

The cited model for those quantitative estimates is Conrey 1983, Section 4.
Jensen's formula bounds each horizontal argument variation by `O(L)`, while
the normalized `V` factor and the mollifier must both be `1 + O(L^{-1})` on
the moving right edge.  The right vertical logarithmic integral is then
`O(U/L)`, and after the Littlewood gap is divided by `R/L` this becomes the
required `O(U)` remainder.  For the present global interval one takes `U` of
size `T`.

There is a constant-scale issue in the printed source which must not be
copied literally into the formal statement.  The paper prints
`sigma_1 = log L` and, on the next page,

\[
  2^{-\sigma_1}\ll L^{-1}.
\]

With the standard natural logarithm these two assertions are incompatible:
`2^{-log L}=L^{-log 2}`, which is not `O(L^{-1})`.  The argument is repaired
without changing its admissible region by taking, for example,

\[
  \sigma_1=2\log L,
\]

or more sharply any
`sigma_1 >= (log L + log C)/log 2` when the preceding tail estimate is
`C * 2^{-sigma_1}`.  This still has `sigma_1 = O(log L)` and so remains in
the range `0 <= sigma <= A log L` used by the approximation lemmas, after
enlarging the fixed constant `A`.  It now gives the required `O(L^{-1})`
right-edge error exactly.  The same corrected edge also makes a finite
Dirichlet mollifier tail with coefficients bounded by one `O(L^{-1})`:

\[
 \sum_{n=2}^{y}|b(n)|n^{-\sigma}
 \le 2^{-\sigma}+\int_2^\infty x^{-\sigma}\,dx
 =2^{-\sigma}\left(1+\frac2{\sigma-1}\right)
 \qquad(\sigma>1).
\]

Thus `sigma = 2 log L` gives the claimed rate for all sufficiently large
`L`.  For the repository's Conrey coefficients the corresponding theorem
must expose the bound for the chosen fixed polynomial `P`; the current
general interface assumes only `P(1)=1`, which is enough for nonvanishing but
not for a uniform quantitative tail estimate as `Y` varies.

Reproducing this corrected argument for the repository's exact degree-one
`V_1 B` requires an explicit normalized approximation theorem on
`Re s = sigma_1` and the corresponding Jensen horizontal-edge theorem; the
existing qualitative nonvanishing theorem alone cannot supply either rate.

For the degree-one definition already in the repository, the normalization
is also explicit.  Uniformly for `t` in a fixed proportional interval such
as `[T, 2T]` and `sigma = c log L`, the standard right-half-plane series and
Stirling estimates give

\[
 \zeta(s)=1+O(2^{-\sigma}),\qquad
 \zeta'(s)=O(2^{-\sigma}),\qquad
 \frac1L\frac{H'(s)}{H(s)}=\frac12+O(L^{-1}).
\]

Consequently

\[
 V_1(s)=\kappa+O(L^{-1})+O(2^{-\sigma}),\qquad
 \kappa=g+\frac{g_1}{2}+i g_0.
\]

The quantitative theorem should therefore assume the nonvanishing of this
explicit main constant and prove
`kappa^(-1) V_1(s) = 1 + O(L^(-1))` on the corrected moving edge.  The
qualitative far-right theorem currently assumes only `g != 0`; that is the
right hypothesis for eventual zero exclusion, but it does not identify this
uniform asymptotic main term.  This distinction must be preserved when the
next Lean interface is introduced.

The horizontal Jensen step already has two reusable, function-agnostic
components in the repository.  `PrimeNumberTheorem/AnalyticJensen.lean`
turns a circle-average growth bound and a nonzero center lower bound into an
inner-disk zero-multiplicity bound.  `MathlibAux/HorizontalArgument.lean`
proves that one divisor point contributes at most `pi` to the horizontal
logarithmic-derivative integral.  Thus the new function-specific work is
precisely:

1. an analytic moving Jensen disk for the regularized actual product;
2. a polynomial circle-growth bound for `V_1 B`;
3. the lower bound at the corrected far-right center supplied by the
   normalized approximation above; and
4. admissible endpoint heights avoiding the `V_1 B` divisor.

After these are proved, the existing Jensen and horizontal-argument lemmas
convert them into the two horizontal terms of (37-exact).  No new abstract
argument-principle surrogate is needed.

Equations (38)--(40), the equation-(41) critical-line partition, and the
long mollified mean square remain separate.  No `O`-term or published
spectral estimate is represented by an axiom in this slice.

## 21. Quantitative moving-right estimate for the explicit mollifier

The source of the right-edge estimate omitted in Conrey 1989, equation
(37), is Conrey 1983, Section 4.  On page 59 that paper chooses
`sigma_1 = log L`; on page 60 it then uses

\[
  A2^{-\sigma_1}<L^{-1}.
\]

These two displays are incompatible when `log` is the natural logarithm.
The correction `sigma_1=2 log L` is sufficient and remains inside the
paper's allowed strip `0<sigma<A log L`.  The following calculation gives a
complete quantitative theorem for the repository's explicit mollifier,
without using a spectral estimate.

For

\[
  P(x)={84x+15x^3+x^5\over100}
\]

one has `0 <= P(x) <= 1` on `[0,1]`: all coefficients are nonnegative, and
`x^3 <= x`, `x^5 <= x` there.  Assume throughout this calculation that the
integer cutoff satisfies `Y>=2` and that `sigma_0<=1/2`.  If
`1 <= n <= Y`, then

\[
  x_{n,Y}={\log(Y/n)\over\log Y}\in[0,1].
\]

Consequently, every nonconstant coefficient in Conrey's equation-(33)
mollifier satisfies

\[
 \left|\mu(n)P(x_{n,Y})n^{\sigma_0-1/2}\right|\le1.
\]

Writing `sigma=Re s>1` and using the exact constant coefficient `b(1)=1`
therefore gives, uniformly in `Im s` and over the admissible cutoffs
`Y>=2`,

\[
\begin{aligned}
 |B(s,P)-1|
 &\le \sum_{2\le n\le Y}n^{-\sigma}\\
 &\le 2^{-\sigma}+\int_2^\infty x^{-\sigma}\,dx\\
 &=2^{-\sigma}\left(1+{2\over\sigma-1}\right).
\end{aligned}
\tag{B-right}
\]

Now let `L>=e` and take `sigma=2 log L`.  Then `sigma>=2`, so the
parenthetical factor in (B-right) is at most `3`.  Moreover
`log 2>1/2`, hence

\[
  2^{-2\log L}
   =\exp(-2\log2\log L)
   \le \exp(-\log L)=L^{-1}.
\]

Thus the corrected moving edge has the explicit bound

\[
 \boxed{\quad
  \left|B(2\log L+it,P)-1\right|\le {3\over L}
  \quad(L\ge e,\ Y\ge2,\ \sigma_0\le1/2).\quad}
\tag{B-moving}
\]

This is the first genuinely quantitative part of the missing equation-(37)
boundary estimate.  In particular, `L>3` makes the mollifier nonzero on the
whole moving right edge.  If `L>=6`, then its norm lies between
`1-3/L` and `1+3/L`; the elementary bounds
`log(1+u)<=u` and `-log(1-u)<=u/(1-u)` give

\[
  \left|\log|B(2\log L+it,P)|\right|\le {6\over L}.
\tag{B-log}
\]

Therefore the mollifier alone contributes at most `6U/L` to a right
vertical logarithmic integral of height `U`.  The corresponding normalized
estimate for `V_1` is still a separate obligation: it needs quantitative
Dirichlet-series estimates for `zeta` and `zeta'`, and a uniform Stirling
estimate for `H'/H` when `t` is in a proportional interval.  No product
estimate is claimed until that second factor is proved.

The bounds (B-right) and (B-moving) are implemented in
`HardyTheorem/ConreyMollifierRightEdge.lean`, with public contract
`Test/ConreyMollifierRightEdgeContract.lean`.  The generic theorem keeps
both necessary hypotheses separate: `P(1)=1` supplies the exact constant
term, while `|P(x)|<=1` on `[0,1]` controls the nonconstant coefficients.
The logarithmic corollary (B-log), the `V_1` estimate, and their product
integral have not yet been promoted to public Lean theorems.

## 22. Local mathematics of the full `V_1 B` moving-right normalization

The missing `V_1` estimate does not require importing a new black-box
Stirling theorem.  It follows quantitatively from the Gauss series for the
digamma function already proved in `PrimeNumberTheorem/DigammaBounds.lean`.
This section records the complete constant ledger before formalization.

Put

\[
 L=\log T,\qquad \sigma=2\log L,\qquad
 s=\sigma+it,\qquad z={s\over2},
 \qquad T\le t\le2T,
\]

and take `T` large enough that `L>=e^2`.  In particular `sigma>=4`, while
`sigma<=T<=t`.  Let `N=ceil(|z|)`.  Then

\[
 {t\over2}\le |z|\le t,\qquad
 |z|\le N<|z|+1,
\]

so `N>0`.  Gauss' series is

\[
 \psi(z)=-\gamma-z^{-1}
   +\sum_{n\ge0}\left({1\over n+1}-{1\over z+n+1}\right).
\]

Split it after `N` terms.  For the finite reciprocal part, the imaginary
coordinate alone gives

\[
 \sum_{n<N}{1\over|z+n+1|}
 \le {N\over |\operatorname{Im}z|}
 ={2N\over t}\le3.
\]

The already-proved quadratic majorant for the remaining Gauss terms gives

\[
 \left\|\sum_{n\ge N}
   \left({1\over n+1}-{1\over z+n+1}\right)\right\|
 \le |z|\sum_{m>N}{1\over m^2}
 \le {|z|\over N}\le1.
\]

Also `|z^(-1)|<=1` and `0<gamma<1`.  Hence, with `H_N` denoting the
`N`-th harmonic number,

\[
 \|\psi(z)-H_N\|\le6.                                      \tag{D1}
\]

The elementary harmonic bounds

\[
 \log(N+1)\le H_N\le1+\log N
\]

and

\[
 {T\over2}\le N+1,\qquad N\le3T
\]

give `|H_N-L|<=3`.  Combining this with (D1),

\[
 \boxed{\ \|\psi(s/2)-L\|\le9.\ }                         \tag{D2}
\]

The exact logarithmic derivative identity

\[
 {H'(s)\over H(s)}={1\over s}+{1\over s-1}
   -{\log\pi\over2}+{\psi(s/2)\over2}
\]

then yields, using the imaginary coordinate to bound both rational terms,

\[
 \boxed{\ \left\|{H'(s)\over H(s)}-{L\over2}\right\|
   \le8.\ }                                                \tag{H-right}
\]

The zeta factor needs the same sharp lower-endpoint p-series estimate as the
mollifier, now for the infinite Dirichlet series:

\[
 \|\zeta(s)-1\|
 \le\sum_{n\ge2}n^{-\sigma}
 \le2^{-\sigma}\left(1+{2\over\sigma-1}\right)
 \le {3\over L}.                                          \tag{Z-right}
\]

Since `sigma>=4`, Cauchy's estimate on the unit disk in `Re w>=3` and the
existing `zeta(2)<=5/3` bound give

\[
 \|\zeta'(s)\|\le\zeta(2)\le{5\over3},
 \qquad \|\zeta(s)\|\le1+{3\over L}\le4.                 \tag{Z'-right}
\]

Now define the genuine main constant

\[
 \kappa=g+{g_1\over2}+ig_0.
\]

The exact algebraic decomposition is

\[
 V_1(s)-\kappa
 =\kappa(\zeta(s)-1)+{g_1\over L}\zeta'(s)
   +{g_1\over L}\left({H'(s)\over H(s)}-{L\over2}\right)
      \zeta(s).                                            \tag{V-decomp}
\]

Therefore (H-right), (Z-right), and (Z'-right) prove

\[
 \boxed{\ \|V_1(s)-\kappa\|
   \le {3|\kappa|+34|g_1|\over L}.\ }                     \tag{V-right}
\]

If `kappa!=0`, the normalized factor satisfies

\[
 \|\kappa^{-1}V_1(s)-1\|
 \le {C_V\over L},\qquad
 C_V=3+34{|g_1|\over|\kappa|}.                            \tag{V-normalized}
\]

Together with (B-moving), the actual normalized product obeys

\[
 \left\|\kappa^{-1}V_1(s)B(s,P)-1\right\|
 \le {C_F\over L},\qquad C_F=4C_V+3
 =15+136{|g_1|\over|\kappa|}.                             \tag{VB-right}
\]

For `L>=2 C_F` this distance is at most `1/2`.  Thus the product is nonzero
on the whole moving right edge and

\[
 \left|\log\left|\kappa^{-1}V_1(s)B(s,P)\right|\right|
 \le {2C_F\over L}.                                       \tag{VB-log}
\]

Integrating over a vertical interval of length `U` gives `2 C_F U/L`.
This closes the quantitative right-vertical term on a proportional block
`T<=t<=2T`, once the displayed finite/infinite p-series and Gauss-series
bounds have been checked in Lean.

It does **not** by itself close the global right vertical in Conrey 1989,
equation (37).  The source check matters here: equation (37) integrates over
`1<=t<=T`, whereas Conrey 1983, Section 4 works on `T<=t<=T+U`.  On the full
interval one cannot replace `H'/H` pointwise by `L/2` with `O(1)` error.
The height variation has to be retained and integrated, as in the next
section.  This corrects the stronger provisional interpretation of the
local estimate.

## 23. Global right-vertical compensation for the explicit degree-one choice

For the explicit certificate

\[
 Q(y)=1-{51\over50}y,
\]

the polynomial before the change of variables in equations (25)--(27) is

\[
 Q_1(x)=Q(1/2-x)={49\over100}+{51\over50}x.
\]

Thus the repository's exact degree-one parameters are

\[
 g={49\over100},\qquad g_0=0,\qquad g_1={51\over50},
 \qquad \kappa=g+{g_1\over2}=1.                           \tag{explicit-V1}
\]

This identity is the missing bridge between the explicit mean-square
polynomial and `conreyDegreeOneV1`; it must be used instead of leaving
`g,g_0,g_1` arbitrary in the final equation-(37) specialization.

Keep `L=log T` and the corrected edge `sigma=2 log L`.  For the high part
`sigma<=t<=T`, the Gauss-series argument of Section 22, now with `t` as its
own scale, gives

\[
 \left\|{H'(\sigma+it)\over H(\sigma+it)}
  -{1\over2}\log {t\over2\pi}\right\|\le C_H              \tag{H-height}
\]

for one absolute constant `C_H`.  Define the height-dependent real main
term

\[
 a_L(t)={49\over100}+{51\over100L}\log {t\over2\pi}.
\]

For `2<=t<=T` and all sufficiently large `L`,

\[
 {1\over5}\le a_L(t)\le1,
 \qquad
 1-a_L(t)={51\over100L}\log {2\pi T\over t}.               \tag{a-height}
\]

Consequently

\[
 |\log a_L(t)|
 \le {3\over L}\log {2\pi T\over t},
\]

and elementary integration gives

\[
 \int_2^T |\log a_L(t)|\,dt\ll {T\over L}.                \tag{a-int}
\]

The zeta and mollifier tails are uniformly `O(1/L)`, and (H-height) shows
that `V_1(s)=a_L(t)+O(1/L)` on the high part.  Since (a-height) keeps the
main term uniformly away from zero, the logarithm is Lipschitz there and

\[
 \int_\sigma^T
 \left|\log|V_1(\sigma+it)B(\sigma+it,P)|\right|dt
 \ll {T\over L}.                                          \tag{VB-high-int}
\]

On the short low part `2<=t<=sigma`, the existing coarse bound
`|digamma(z)|<<1+log(|z|+1)` gives

\[
 V_1(\sigma+it)=g+O\!\left({\log\sigma\over L}\right),
\]

uniformly.  Because `g=49/100`, this is bounded away from zero for large
`L`; both its norm and reciprocal norm are bounded by absolute constants.
Its logarithmic integral therefore has size

\[
 O(\sigma)=O(\log L)=o(T/L).                               \tag{VB-low-int}
\]

Combining (VB-high-int), (VB-low-int), and the already proved mollifier
bound supplies the genuine global right-vertical `O(T/L)` input required
by equation (37).  Unlike the local normalization, this argument does not
discard the `log(t/T)` variation; its integral is exactly what recovers the
missing factor `1/L`.

The formalization should therefore proceed in two layers.  First prove the
reusable local Gauss/zeta estimates and `V_1` decomposition.  Then specialize
to (explicit-V1) and prove the global logarithmic integral.  Only after the
second layer is green may the right-vertical item in Section 20 be marked
closed.  The horizontal Jensen terms and admissible endpoint heights remain
separate gates.

### 23.1 Verified checkpoint: the reusable height layer

The first layer is now proved in Lean with no new project axioms:

- `norm_riemannZeta_sub_one_le_rightTail` proves the infinite Dirichlet tail

  \[
  \|\zeta(s)-1\|\le 2^{-\Re s}
    \left(1+{2\over \Re s-1}\right),
  \]

  and `norm_riemannZeta_movingRight_sub_one_le` specializes it to `3/L`;
- `norm_digamma_halfLine_sub_log_le_nine` proves the Gauss-series height
  estimate with constant `9` by splitting at `ceil ||z||`;
- `norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le` proves (H-height)
  with the explicit constant `C_H=8`;
- `conreyDegreeOneV1_sub_heightMain_eq` proves the exact height-dependent
  decomposition, and
  `norm_conreyDegreeOneV1_sub_heightMain_movingRight_le` proves

  \[
  \|V_1(s)-A_L(t)\|
  \le {3\|A_L(t)\|+34|g_1|\over L}
  \]

  on `Re s=2 log L`, `L>=exp 2`, `2<=t`, and `Re s<=t`.

This checkpoint closes the reusable pointwise height estimates only.  It
does **not** yet prove (a-height), (a-int), the low-range reciprocal bound,
or the global absolute-log integral.  Consequently equation (37)'s global
right vertical remains open until the second layer is green.

### 23.2 Verified checkpoint: explicit high-part nonvanishing

The explicit specialization is now proved through the pointwise high-part
nonvanishing step:

- `conreyExplicitDegreeOneHeightMain_eq` identifies the concrete main term

  \[
  a_L(t)={49\over100}+{51\over100L}\log {t\over2\pi};
  \]

- `one_third_le_conreyExplicitDegreeOneHeightMain_re` and
  `conreyExplicitDegreeOneHeightMain_re_le_one` prove
  `1/3 <= a_L(t) <= 1` on `1 <= t <= exp L`, for `L >= exp 2`;
- `one_sub_conreyExplicitDegreeOneHeightMain_re_eq` proves the exact
  compensation identity

  \[
  1-a_L(t)={51\over100L}\log {2\pi e^L\over t};
  \]

- after combining the proved `V1` and mollifier errors,
  `norm_conreyExplicitRightVerticalProduct_sub_heightMain_le` proves

  \[
  \|V_1(2\log L+it)B(2\log L+it)-a_L(t)\|\le {79\over L}
  \]

  on `2 log L <= t <= exp L` for `L >= 600`; and
- `conreyExplicitRightVerticalProduct_ne_zero` derives nonvanishing directly
  from this error and `a_L(t) >= 1/3`, without assuming a boundary
  nonvanishing predicate.

This closes the explicit high-part pointwise and nonvanishing layer.  It does
**not** yet prove the absolute-log Lipschitz bound, its high-part integral,
the low-part reciprocal bound, or the final global right-vertical integral.
Equation (37)'s right vertical therefore remains open at this checkpoint.

### 23.3 Verified checkpoint: high-part logarithmic compensation

The next high-part step is now proved without replacing the moving main term
by a constant:

- `abs_log_sub_log_le_six_mul_abs_sub` proves the elementary positive-line
  Lipschitz estimate needed to pass from the product error to logarithms;
- `abs_log_le_three_mul_one_sub` controls the logarithm of the real main term
  by its exact distance from one;
- `abs_log_norm_conreyExplicitRightVerticalProduct_le` combines these facts
  with Section 23.2 to prove

  \[
  \left|\log\left\|V_1(2\log L+it)B(2\log L+it)\right\|\right|
  \le {500\over L}+{2\over L}\log {2\pi e^L\over t}
  \]

  throughout `2 log L <= t <= exp L`, for `L >= 600`; and
- `integral_log_conrey_height_compensation_one_exp_le` proves the elementary
  global compensation estimate

  \[
  \int_1^{e^L}\log {2\pi e^L\over t}\,dt\le 3e^L.
  \]

- `continuous_conreyExplicitRightVerticalProduct` derives continuity along
  the moving vertical line from the analytic `V1` factor and the entire finite
  mollifier; and
- `integral_abs_log_norm_conreyExplicitRightVerticalProduct_high_le` combines
  continuity, direct nonvanishing, the pointwise logarithmic bound, and the
  compensation integral to prove

  \[
  \int_{2\log L}^{e^L}
  \left|\log\left\|V_1(2\log L+it)B(2\log L+it)\right\|\right|dt
  \le {506e^L\over L}.
  \]

This closes the complete high range and formally recovers the factor `1/L`
without a constant-height substitution.  The low-part reciprocal bound and
the final global interval split are still open.  Hence equation (37)'s right
vertical, the horizontal Jensen terms, and the genuine two-fifths theorem
remain unproved at this checkpoint.

### 23.4 Verified checkpoint: complete global right-edge logarithmic integral

The short low range and the final interval split are now proved in
`ConreyExplicitRightVerticalLow.lean`:

- `log_le_div_hundred_of_ge_forty_thousand` gives the explicit elementary
  scale `log L <= L/100` for `L >= 40000`;
- `norm_logDeriv_conreyH_movingRight_low_le` applies the coarse digamma bound
  on `1 <= t <= 2 log L` and proves

  \[
  \left\|{H'\over H}(2\log L+it)\right\|\le 6+\log L;
  \]

- `norm_conreyExplicitV1_sub_const_low_le` consequently proves

  \[
  \left\|V_1(2\log L+it)-{49\over100}\right\|\le {1\over50};
  \]

- `conreyExplicitRightVerticalProduct_low_norm_bounds` combines this with the
  finite-mollifier tail to obtain the direct, assumption-free bounds

  \[
  {2\over5}\le\|V_1(2\log L+it)B(2\log L+it)\|\le {3\over5};
  \]

- hence `abs_log_norm_conreyExplicitRightVerticalProduct_low_le_two` and
  `integral_abs_log_norm_conreyExplicitRightVerticalProduct_low_le` prove

  \[
  \int_1^{2\log L}|\log\|V_1B\||\,dt\le4\log L;
  \]

- finally `integral_abs_log_norm_conreyExplicitRightVerticalProduct_global_le`
  joins this estimate to Section 23.3 and proves

  \[
  \int_1^{e^L}
  \left|\log\left\|V_1(2\log L+it)B(2\log L+it)\right\|\right|dt
  \le {507e^L\over L}
  \]

  for `L >= 40000`.

This closes the moving-right-edge logarithmic-integral item needed in
equation (37), with a concrete product and no abstract boundary nonvanishing
hypothesis.  It does **not** close the two horizontal weighted phase/Jensen
terms, admissible endpoint selection, or the long mollified mean square.
Those remain the next gates before any genuine two-fifths claim.

### 23.5 Verified checkpoint: actual-product Jensen mass and admissible heights

The paper-first disk design in
`2026-08-28-conrey-horizontal-jensen-math.md` is now implemented for the
actual product, without a conditional growth predicate:

- `exists_norm_conreyExplicitMollifiedV1_le_conreyHorizontalJensenOuterClosedBall`
  proves the outer-disk bound

  \[
  |V_1(s)B(s)|\le C\,Y\,(U+2\log L+10)^6(L+2)^2;
  \]

- `exists_conreyHorizontalJensenInnerZeroMass_le` combines this sphere bound,
  the center lower bound `1/6`, circle-average monotonicity, Jensen's formula,
  and divisor locality to prove the exact multiplicity bound

  \[
  N_D(r)\le
  {\log\{C Y (U+2\log L+10)^6(L+2)^2\}+\log 6
   \over \log(\mathcal R/r)};
  \]

- `card_conreyHorizontalJensenInnerZeroSupport_le_mass` bounds the number of
  distinct inner-disk zeros by this multiplicity mass; and
- `exists_conreyHorizontalJensenAdmissibleHeight` selects
  `t in [U,U+1]`, quantitatively separated from every inner-disk zero height,
  so the actual product is nonzero on the complete segment
  `[sigma0, 2 log L] + it`.

The finite height set is computed from the divisor on the inner disk (which,
by divisor locality, is the outer divisor restricted to that disk).  It does
not include uncontrolled zeros in the outer annulus.

The follow-up buffered-factor, Borel--Caratheodory, and horizontal-integral
modules now go further: at one factor-support-selected height they bound the
actual weighted logarithmic derivative by

\[
 1{,}100{,}000{,}000{,}000\,L^7=o(e^L/L).
\]

Thus the selected-height horizontal Jensen term is closed.  The subsequent
right-half-plane argument module also proves `Re F >= 3/10` on the whole
moving edge and bounds the far-right argument variation by `pi`.

The two horizontal selectors have now been applied simultaneously in
`HardyTheorem/ConreyEquation37Edges.lean`: one height lies in
`[2 log L+1,2 log L+2]`, the other in `[exp L-1,exp L]`, and the complete
non-left boundary remainder is at most

\[
 {507e^L\over L}+2.2\cdot10^{12}L^7+
 \bigl(2\log L-(1/2-R/L)\bigr)\pi.
\]

This assembly exposed one boundary convention that the preceding ledger had
not stated.  The current exact Lean Littlewood theorem requires all rectangle
zeros to be strictly interior.  The selected heights and the positive-real-
part right edge exclude bottom, top, and right boundary zeros, but the actual
product need not be nonzero on `Re s=sigma_0`.  The boundary is now handled
by shifting it from the right through zero-free lines.  Target zeros with
`Re rho>=1/2` remain in every shifted rectangle, and reverse Fatou gives the
needed one-sided bound for the limiting left logarithmic integral; full
`L^1` convergence is unnecessary.  The general epsilon theorem is formalized
in `PrimeNumberTheorem/LittlewoodLeftBoundaryLimit.lean`.  Ordinary
convergence of its shifted non-left remainder and specialization to the
actual product remain the next contour-core tasks.

After that, the transfer from selected endpoints to every height,
equations (38)--(41), and the long mollified second moment remain open;
strict `> 2/5` is not proved.

## 27. Exact left-boundary tail limit

The ordinary convergence checkpoint is now combined with the reverse-Fatou
left-boundary inequality by applying the latter to every tail of the chosen
zero-free-line sequence.  If

\[
 A_n=2\pi(c-x_n)M_{\ge c},\qquad
 R_n=R_{\mathrm{nonleft}}(x_n),
\]

then `A_n -> A_0` and `R_n -> R_0`.  Applying reverse Fatou to the tail
`x_{N+k}` with error `epsilon/3` forces its selected index beyond the common
convergence threshold and yields

\[
 A_0\le I(x_0)+R_0+\epsilon.
\]

Letting `epsilon` tend to zero proves the exact limiting inequality with both
the coefficient and the non-left remainder evaluated at `x_0`.  This is
formalized in `PrimeNumberTheorem/LittlewoodTailLimit.lean`; it uses no
zero-free hypothesis on the limiting left side and no false two-sided `L^1`
convergence statement.

For Conrey, `x_0=1/2-R/L` and `c=1/2`, so the coefficient is exactly `R/L`.
The remaining equation-(37) specialization must still construct the finite
divisor and a right-shifted sequence of zero-free vertical lines for the
actual product `V_1B` at the two selected horizontal heights.  Equations
(38)--(41) and the long `theta<4/7` mollified mean square remain downstream.

## 28. Equation-(41) global deleted-level accounting

The next equation-(41) audit found that summing the zero-free crossing bound
component by component is not sharp enough: it pays one floor/ceiling loss on
each component and then risks charging the critical-line zeros a second time.
The correct construction first reconciles the component argument lifts across
an order-`m` zero by a phase bridge of length `m*pi`, then counts the global
half-odd-integer argument levels only once.

A half-open order-`m` bridge can swallow at most `m` such levels.  Hence the
critical-line zero multiplicity removes at most `N_{0,eta}` levels, while the
two global endpoints contribute only one further rounding loss.  The exact
finite target is

\[
  \#\{t:\operatorname{Re}\eta(1/2+it)=0,\ \eta(1/2+it)\ne0\}
  \ge \frac1\pi\Delta\arg\eta-N_{0,\eta}-1.
\]

The first reusable counting layer is now formalized as
`argumentCrossingIndices_sdiff_card_lower_bound`: deleting an arbitrary bad
level finset `B` from the global level interval costs at most `#B`, without
introducing another componentwise rounding loss.  The independent note
`2026-08-29-conrey-equation41-global-partition-math.md` records the full
four-layer design.

The order-`m` half-open bridge capacity, local analytic phase alignment, and
global attribution for the actual `eta` remain open.  Thus equation (41) and
the Conrey simple-zero proportion are not yet proved.
