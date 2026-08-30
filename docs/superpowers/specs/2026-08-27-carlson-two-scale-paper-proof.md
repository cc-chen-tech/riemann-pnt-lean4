# A two-scale Carlson proof at `sigma = 2/3`

## 1. Statement and method class

Let `N(sigma,T)` count nontrivial zeros of the Riemann zeta function with
`Re rho > sigma` and `0 < Im rho <= T`, with analytic multiplicity.  The
argument below gives

\[
  N(2/3,T) \ll T^{467/576}(\log T)^6.
\]

Thus one may take `delta=5/64` and `B=6`.  This is a Carlson contour proof
with a new published long-mollifier mean-square input.  It is not an
application of Ingham's zero-density theorem.

## 2. The two-scale plateau mollifier

Put

\[
 a=\frac{57}{100},\qquad b=\frac{571}{1000};
 \qquad a<b<\frac47.
\]

For a dyadic height scale `U`, let `Y_0=floor(U^a)` and
`Y_1=floor(U^b)`, and define

\[
 w_U(n)=
 \begin{cases}
  1,&n\le Y_0,\\
  \dfrac{\log(Y_1/n)}{\log(Y_1/Y_0)},&Y_0<n\le Y_1,\\
  0,&n>Y_1,
 \end{cases}
 \qquad
 M_U(s)=\sum_n\mu(n)w_U(n)n^{-s}.
\]

If

\[
 S_Y(s)=\sum_{n\le Y}\mu(n)
   \frac{\log(Y/n)}{\log Y}\,n^{-s},
\]

then coefficient by coefficient

\[
 M_U(s)=
 \frac{\log Y_1}{\log(Y_1/Y_0)}S_{Y_1}(s)
 -\frac{\log Y_0}{\log(Y_1/Y_0)}S_{Y_0}(s).                \tag{2.1}
\]

For `n<=Y_0`, the two logarithmic weights subtract to `1`; for
`Y_0<n<=Y_1`, only the first term is present.  The two multipliers in (2.1)
are bounded constants for all large `U`, tending respectively to
`b/(b-a)` and `-a/(b-a)`.  Also `0<=w_U(n)<=1` on its support, so the
mollifier coefficients have modulus at most one and their constant
coefficient is one.

## 3. Published critical-boundary input

Conrey's Theorem 2 in *More than two fifths of the zeros of the Riemann zeta
function are on the critical line*, J. reine angew. Math. 399 (1989), proves
the mollified second-moment asymptotic for every fixed `theta<4/7` and every
fixed polynomial `P` with `P(0)=0`.  Take `Q=1`, `R=0`, and `P(u)=u`.
The printed hypothesis is `R << 1`, so `R=0` is directly allowed; then
`sigma_0=1/2` and `V=zeta`.

More precisely, Conrey's equation (50) gives the following local form.  Fix
a sufficiently small `eta>0`, put `Delta=U^(1-eta)`, and let `U<=w<=2U`.
Uniformly in `w`,

\[
 \frac1{\Delta\sqrt\pi}\int_{-\infty}^{\infty}
   e^{-(t-w)^2/\Delta^2}
   |\zeta(1/2+it)S_{U^\theta}(1/2+it)|^2dt
 \ll_\theta 1.                                             \tag{3.1}
\]

Apply (3.1) separately with `theta=a,b` to the two terms of (2.1), and use
`|z_1+z_2|^2 <= 2|z_1|^2+2|z_2|^2`.  The floor in `Y_j` is the usual
integer interpretation of Conrey's cutoff and changes no estimate.  Thus

\[
 \int_{-\infty}^{\infty}e^{-(t-w)^2/\Delta^2}
   |\zeta(1/2+it)M_U(1/2+it)|^2dt\ll \Delta.               \tag{3.2}
\]

Consequently, for `F_U(s)=zeta(s)M_U(s)-1`,

\[
 \int_{-\infty}^{\infty}e^{-(t-w)^2/\Delta^2}
   |F_U(1/2+it)|^2dt\ll \Delta.                            \tag{3.3}
\]

This local formulation matters: one cannot control a width-`U` analytic
Gaussian over the whole real line merely from a global mean on `[0,U]`.
Equation (50) supplies exactly the windowed estimate used below.

## 4. Exact right-boundary cancellation

For `Re s>1`, absolute convergence gives

\[
 F_U(s)=\sum_{m\ge2}c_U(m)m^{-s},\qquad
 c_U(m)=\sum_{d\mid m}\mu(d)w_U(d).
\]

If `2<=m<=Y_0`, every divisor of `m` lies in the plateau where `w_U(d)=1`;
hence

\[
 c_U(m)=\sum_{d\mid m}\mu(d)=0.                            \tag{4.1}
\]

There is a shorter absolute-convergence estimate which is also stronger.
Let `M_{Y_0}` be the sharp Moebius cutoff.  Both
`M_U-M_{Y_0}` and `1/zeta-M_{Y_0}` are supported beyond `Y_0`, and their
coefficients have modulus at most one.  Hence, for every fixed `R>1`,

\[
 \left|M_U(R+it)-\frac1{\zeta(R+it)}\right|
 \le 2\sum_{n>Y_0}n^{-R}\ll_R Y_0^{1-R}.                 \tag{4.2}
\]

Since `F_U=zeta(M_U-1/zeta)`, this gives, uniformly in `t`,

\[
 |F_U(R+it)|\ll_R U^{a(1-R)}.                              \tag{4.3}
\]

At `R=4` the formal proof uses the elementary telescoping majorant
`sum_{n>Y_0}n^{-4}<=Y_0^{-3}` and `|zeta(4+it)|<=5/3`, obtaining the explicit
bound `|F_U(4+it)|<=(10/3)Y_0^{-3}`.  No cancellation between the taper and
the complete Moebius tail is used.

This is exact coefficient cancellation, not heuristic square-root
cancellation.  The critical-line positive diagonal is not removed: (3.2)
has order `Delta`.

## 5. Pole-free local Hilbert three-lines step

The strip from `1/2` to `R` crosses the pole of `zeta`.  Remove it before
interpolation:

\[
 H_U(s)=\frac{s-1}{s+1}F_U(s).                             \tag{5.1}
\]

The numerator cancels the simple pole of `zeta`, while the denominator has
its only pole at `-1`; hence `H_U` is analytic on `Re s>=1/2` and has
polynomial vertical growth on every fixed strip.

Fix `U<=w<=2U` and define the `L^2(R)`-valued function

\[
 \Phi_{U,w}(z)(t)=
  \exp\!\left(\frac{(z+it-iw)^2}{2\Delta^2}\right)H_U(z+it).
                                                               \tag{5.2}
\]

For each fixed `t` the integrand is analytic in `z`.  Gaussian decay and
the polynomial vertical growth give a holomorphic `L^2(R)`-valued map.
After translating `t` by `Im z`, its norm depends only on `Re z`.  The
Hilbert-valued Hadamard three-lines theorem therefore gives, for
`1/2<=x<=R` and `lambda(x)=(x-1/2)/(R-1/2)`,

\[
 \|\Phi_{U,w}(x)\|_2^2
 \le \|\Phi_{U,w}(1/2)\|_2^{2(1-\lambda(x))}
      \|\Phi_{U,w}(R)\|_2^{2\lambda(x)}.                   \tag{5.3}
\]

The harmless factor `(s-1)/(s+1)` is bounded above on both boundary lines.
Equations (3.3) and (4.3) consequently give, uniformly in `w`,

\[
 \|\Phi_{U,w}(1/2)\|_2^2\ll \Delta U^\varepsilon,
 \qquad
 \|\Phi_{U,w}(R)\|_2^2
 \ll \Delta U^{2a(1-R)}.                                  \tag{5.4}
\]

The `U^epsilon` is only a uniform reserve; Conrey's asymptotic is stronger.
On `|t-w|<=Delta/2` and `1/2<x<1`, the Gaussian and
`|(s-1)/(s+1)|` are bounded below by positive absolute constants for large
`U`.  Thus (5.3) bounds the unweighted integral of `|F_U|^2` on that
half-window.  Cover `[U,2U]` by `O(U/Delta)` overlapping half-windows.
The number of windows cancels the factor `Delta` in (5.4), yielding

\[
 \int_U^{2U}|F_U(x+it)|^2dt
 \ll U^{(1-\lambda(x))(1+\varepsilon)
           +\lambda(x)(1+2a(1-R))}(\log U)^2.              \tag{5.5}
\]

Take `R=1000` and `epsilon=1/10000`.  At `x=2/3`,
`lambda=1/5997`, and the exponent in (5.5) is

\[
 q_*=1-\frac{18981}{99950}+\frac{1499}{14992500}
     =\frac{12146849}{14992500}.                            \tag{5.6}
\]

There is also a weaker but formally much shorter specialization which uses
only the already formalized strip endpoint `R=4`.  Here

\[
 \lambda(2/3)=\frac1{21},\qquad
 q_4=1+\frac{20}{21}\frac1{10000}
        +\frac1{21}\,2\frac{57}{100}(1-4)
     =\frac{8791}{10500}.
\]

Since

\[
 \frac{151}{180}-q_4=\frac{13}{7875}>0,
 \qquad \frac{151}{180}=\frac89-\frac1{20},               \tag{5.7}
\]

the `R=4` specialization alone proves the explicit saving
`delta=1/20`.  Thus `R=1000` is needed only for the stronger displayed
`delta=5/64`, not for the existence of a power saving.

There is a still weaker first target which avoids the `4/7` range entirely.
Take
```
a=2/5,  b=9/20,  R=4,  epsilon=1/2000.
```
Then `1/3<a<b<1/2`, so only the classical sub-half-length mollified
mean-square range is required.  The exact interpolation output is

\[
 q_{1/2}=\frac{1861}{2100},\qquad
 \frac89-q_{1/2}=\frac{17}{6300}.
\]

Choosing the round saving `delta=1/400` leaves the strict exponent slack

\[
 \left(\frac89-\frac1{400}\right)-q_{1/2}=\frac1{5040}>0. \tag{5.8}
\]

At paper level this is already a specialization of the same published
Conrey theorem.  Its importance for formalization is different: the required
`theta<1/2` mean square can in principle be proved from the classical
square-root approximate functional equation and finite Dirichlet-polynomial
mean value, without the Deshouillers--Iwaniec/Kuznetsov input needed beyond
`1/2`.  Here the phase normalization must be fixed before this reduction is
used.  Put

\[
 s=\frac12+it,\qquad
 \frac{\Gamma_{\mathbb R}(s)}{|\Gamma_{\mathbb R}(s)|}
       =e^{i\vartheta(t)}.
\]

Since `1-s=conj(s)` and
`Gamma_R(conj(s))=conj(Gamma_R(s))`, the multiplier in the dual AFE sum is

\[
 \chi(s)=\frac{\Gamma_{\mathbb R}(1-s)}
                 {\Gamma_{\mathbb R}(s)}
        =\frac{\overline{\Gamma_{\mathbb R}(s)}}
               {\Gamma_{\mathbb R}(s)}
        =e^{-2i\vartheta(t)}.                              \tag{5.9}
\]

In particular `exp(+i thetaPhase t)` is not the AFE dual multiplier.  The
previous placeholder in `HardyTheorem/AFE.lean` used that incorrect phase;
it must be replaced by (5.9), not treated as an analytic hypothesis.  The
repository still does not contain a proof of the resulting corrected AFE, so
(5.8) is a strictly smaller analytic gate, not a claim that the Lean density
certificate is already unconditional.

If `x=2/3+O(1/log U)`, this exponent changes by `O(1/log U)`, hence only by
an absolute multiplicative constant after exponentiation.

## 6. Carlson contour on a dyadic shell

Use `M_U` and its detector

\[
 h_U(s)=1-F_U(s)^2=\zeta(s)M_U(s)(2-\zeta(s)M_U(s)).       \tag{6.1}
\]

Every zeta zero is a detector zero with at least the same analytic
multiplicity.  Choose the left edge in

\[
 \frac23-\frac{2}{\log U}<x_0<
 \frac23-\frac{1}{\log U},                                \tag{6.2}
\]

avoiding the finitely many detector zeros.  Apply (4.3) with `R=4`; for
large `U`, `|F_U(4+it)|<1`, so the fixed right edge is detector-zero-free.
The value `R=1000` is used only in interpolation, not as the contour edge.

For completeness, the coefficient-generic horizontal estimate needed here
is the following lemma.  If a finite Dirichlet polynomial `M` has support at
most `Y`, coefficient one at `n=1`, coefficients bounded by one, and
`|zeta(s)M(s)-1|<=1/3` on `Re s=4`, then the regularized detector
`(s-1)^2(1-(zeta(s)M(s)-1)^2)` has polynomial growth
`O(Y^2(|t|+3)^10)` in the fixed Jensen disks centered on `Re s=4`.

Here are the details, including the normalizations used by the contour.  For
a height parameter `V>=5`, put

\[
 c=4+i(V+1/2),\quad R_0=31/8,\quad b=123/32,
 \quad r_0=15/4.
\]

The closed `R_0`-disk has `Re s>=1/8` and `|Im s|<=V+5`.  Hence
`|M(s)|<=Y`.  The standard fixed-strip polynomial bound
`|zeta(s)|<<(|Im s|+3)^4` therefore gives, for

\[
 G(s)=(s-1)^2\{1-(\zeta(s)M(s)-1)^2\},
\]

the uniform outer-circle estimate

\[
 |G(s)|\le C Y^2(V+14)^{10}.                            \tag{6.2a}
\]

The expression
`((s-1)zeta(s))M(s)(2(s-1)-((s-1)zeta(s))M(s))` shows that `G` is
entire.  At the center, the right-line hypothesis gives
`|1-F(c)^2|>=8/9`, where `F=zeta M-1`; since `|c-1|^2>1`,
`|G(c)|>=1`.  Jensen's theorem between radii `b` and `R_0` now bounds the
complete analytic divisor mass in the `b`-disk by

\[
 L\le {\log(CY^2(V+14)^{10})\over\log(R_0/b)}
   \ll \log(Y(V+14)).                                   \tag{6.2b}
\]

Choose a radius `r in [121/32,122/32]` separated from every modulus
`|rho-c|` of a zero in the `b`-disk by
`delta_r >> 1/(L+1)`.  This is the elementary finite-interval pigeonhole
lemma, applied to at most `L` distinct radii.  Factor, with multiplicity,

\[
 G(s)=g(s)\prod_{|\rho-c|\le b}(s-\rho)^{m_\rho}.
\]

Then `g` is analytic and zero-free in the `b`-disk.  On `|s-c|=r`,
(6.2a) and the radial separation give

\[
 \log|g(s)|\le \log(CY^2(V+14)^{10})-L\log\delta_r
   \ll (\log(Y(V+14)))^2.                               \tag{6.2c}
\]

At the center the same factorization, `|G(c)|>=1`, and
`|c-rho|<=b` give `log|g(c)|>=-L log b`.  Applying the standard
Borel--Caratheodory/logarithmic-derivative estimate to an analytic logarithm
of `g` between the `r`-circle and the `r_0`-disk yields

\[
 |g'(s)/g(s)|\ll (\log(Y(V+14)))^2\qquad(|s-c|\le r_0). \tag{6.2d}
\]

Finally choose `v in [V,V+1]` separated from every ordinate of a zero in
the `b`-disk by `delta_h=1/(4(L+1))`.  The forbidden intervals have total
length at most `1/2`, so such a `v` exists.  The segment
`{x+iv: 1/2<=x<=4}` lies in the `r_0`-disk.  It is zero-free, and the
principal parts satisfy

\[
 \left|\sum_\rho {m_\rho\over x+iv-\rho}\right|
 \le L/\delta_h\ll (L+1)^2.                             \tag{6.2e}
\]

Combining (6.2d) and (6.2e) proves the required uniform
`O((log(Y(V+14)))^2)` horizontal logarithmic-derivative bound.  Thus the
argument uses no special formula for the coefficients beyond the four
hypotheses above.  The quantitative `1/3` bound is essential because it
supplies `|G(c)|>=1`; mere nonvanishing would not give (6.2b) with a uniform
logarithmic majorant.  These Jensen, factorization, Borel--Caratheodory, and
finite-pigeonhole lemmas are already formalized in
`CarlsonDetectorGrowth.lean`.  The two-scale support bound, the explicit
far-right estimate `|F(4+it)|<=5/36<1/3`, the fixed-circle growth bound,
and the resulting unconditional Jensen divisor-mass bound are now
formalized in `CarlsonTwoScaleFarRight.lean` and
`CarlsonTwoScaleDetectorGrowth.lean`; divisor locality also identifies
this outer-Jensen mass with the complete divisor on the inner factorization
disk, and the corresponding nonvanishing analytic factor with its center
divisor-mass lower bound has been extracted.  The two-scale post-Jensen
wrapper is now also formalized: it identifies finite zero support, performs
the radial and height pigeonhole selections, extracts the analytic nonzero
factor with its principal-part identity, applies the quantitative
Borel--Caratheodory estimate, and produces a zero-free horizontal segment
with the exact bound "factor term plus mass divided by separation".  The
Jensen mass majorant is now substituted into both the radial and horizontal
separations as well, exposing a zero-data-independent explicit logarithmic-
polynomial majorant.  Thus the post-Jensen local horizontal layer is closed.

Choose the bottom side in `[U-1,U]` and the top side in `[2U,2U+1]`, so the
rectangle contains every zero with ordinate in `[U,2U]`.  Apply Littlewood's
lemma to this rectangle.  The preceding horizontal estimate, exact
cancellation of the `(s-1)^2` regularizer, and
`log|1-F^2|<=log(1+|F|^2)<=|F|^2` give

\[
 (2\pi)(2/3-x_0)N(2/3;U,2U)
 \ll \int_{U+O(1)}^{2U+O(1)}|F_U(x_0+it)|^2dt
      +(\log U)^3.                                        \tag{6.3}
\]

The `O(1)` endpoint extensions require only two extra local Gaussian
windows.  Since `2/3-x_0>=1/log U`, equations (5.5)--(6.3) imply

\[
 N(2/3;U,2U)\ll U^{q_*}(\log U)^4.                        \tag{6.4}
\]

Summing over dyadic shells up to `T` is a convergent geometric sum because
`q_*>0`; finitely many low shells are absorbed in the constant.  Therefore
the same estimate holds for `N(2/3,T)`.  Finally,

\[
 \frac{467}{576}-q_*=\frac{409373}{719640000}>0,
\]

so weakening the power slightly and allowing two spare logarithms proves

\[
 \boxed{N(2/3,T)\ll T^{467/576}(\log T)^6}.
\]

## 7. Endpoint ledger and method classification

1. **Carlson internal retuning.**  In the old two-endpoint class the unique
   optimum remains `x=1/3`, with exponent `8/9`; no length change improves it.
2. **Carlson plus a new large-values input.**  The proof above uses
   Conrey/Deshouillers--Iwaniec to control the critical-boundary
   non-diagonal for a taper of length below `U^(4/7)`, while an exact inner
   plateau preserves far-right Mobius cancellation.  This suppresses the
   old upper endpoint and permits the effective length `a=57/100`.
3. **Direct replacement by another density theorem.**  Not used.

At `sigma=2/3`, the limiting power from a plateau `a` and an infinitely far
interpolation boundary is `1-a/3`.  Relative to the old upper endpoint at
that same length, the effective upper-endpoint saving is
`delta_U=a-1/3`, while `delta_L=0`; thus the fixed-saving ledger reads

\[
 \frac89-\frac23\delta_L-\frac13\delta_U=1-\frac a3.
\]

For the finite choices `R=1000` and `epsilon=1/10000`, the exact effective
saving is instead `delta_U=3(8/9-q_*)`; substituting it gives `q_*`
identically.  This is an endpoint accounting identity for this chosen
route, not a claim that the saving is uniform in the mollifier length.

## 8. Lean translation boundary

The finite two-scale mollifier/detector, identity (2.1), cancellation (4.1),
the explicit fixed-right estimate `5/36`, fixed-circle growth,
unconditional Jensen local zero-mass bound, local divisor factorization,
good-radius selection, Borel--Caratheodory estimate, and zero-free horizontal
segment with its exact mass/separation bound are formalized.  The squared
Banach-valued Hadamard bound underlying (5.3), together with the exact
pointwise Gaussian norm normalization in (5.2), is also formalized.  A
continuous vertical section satisfying either a strict sub-Gaussian square
bound or a centered polynomial square bound has formally been promoted to
`L^2(R)` with the exact Gaussian normalization, including the exact center
shift for an arbitrary complex strip parameter.  The pole-free mollified
error in (5.1) has been defined through the analytic zeta pole unit, proved
analytic on `Re(s)>0`, identified with the paper formula away from the pole,
and proved continuous on each such vertical line.  Its norm is formally
uniformly bounded on the compact rectangle `1/2 <= Re(s) <= 4`,
`|Im(s)| <= 1`; the complementary high-height estimate has been combined
with it into a degree-ten square-growth bound on the full strip
`1/2 <= Re(s) <= 4`.  Consequently the concrete Gaussian section is
formally in `L^2(R)` for every complex strip parameter in that strip.  It has
also been packaged as an actual `Lp C 2 volume` element, with an a.e.-exact
representative and an exact norm-square integral formula.  For an arbitrary
analytic scalar factor `H`, the exact pointwise complex derivative of the
Gaussian section in the strip parameter is formalized.  Cauchy's derivative
estimate converts the degree-ten square-growth bound for the pole-free error
on `1/2 <= Re(s) <= 4` into a degree-twenty derivative-square bound, first on
the fixed inner strip and then, with a point-dependent radius, on every
compact inner strip.  The exact derivative `MemLp` certificate and both
component certificates are retained on the fixed inner strip, with the old
`2/3` interfaces as corollaries.

The functional-analytic passage is now closed on the full open strip.  The
controlled section is totalized by zero outside `1/2 <= Re(z) <= 4`, so it is
an `L²(R)` value for every parameter while agreeing locally with the original
section at every point with `1/2 < Re(z) < 4`.  At such a point the formal
radius
```
min(1/48, (Re(z)-1/2)/4, (4-Re(z))/4)
```
is positive.  The variable-radius Cauchy estimate supplies a degree-twenty
polynomial times half-rate Gaussian majorant uniformly on the corresponding
closed ball.  The complex mean-value estimate bounds the squared slope error
by four times this majorant; measurability, Gaussian integrability, dominated
convergence, and the `MemLp.toLp` derivative bridge then give an actual
`HasDerivAt` theorem for the totalized `Lp C 2 volume` map at every
`1/2 < Re(z) < 4`.  The totalization makes no differentiability claim on the
two artificial boundary lines themselves.  Thus the local analyticity
hypothesis needed inside the Hadamard strip is no longer an open gate.  The
right endpoint has also been closed with exact constants: the taper and
complete Moebius tails are separately bounded by `Y0^-3`, the pole-removal
factor has norm at most one, and the resulting Gaussian `L²` norm at
`Re(z)=4` is bounded by
```
exp(16/Delta^2) * ((10/3) * Y0^-3)^2
  * sqrt(pi / (1/Delta^2)).
```
Imaginary translation of the strip parameter has now been proved to be an
exact translation of the height variable, so the formal `L^2` norm depends
only on `Re(z)`.  Hence on every interior strip
`1/2 < l < u < 4` the unbounded-strip boundedness hypothesis reduces to the
boundedness of a continuous norm function on the compact interval `[l,u]`.
The resulting concrete squared-norm Hadamard theorem takes endpoint
second-moment bounds `A,B` and returns exactly
```
norm(Phi(x))^2 <= A^(1-(x-l)/(u-l)) * B^((x-l)/(u-l)),
```
with no square-root loss.  Its formal axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.

The one-sided boundary continuity has now also been proved.  The degree-ten
strip growth and the exact Gaussian formula give a single integrable
polynomial-Gaussian majorant for all real parameters in `[1/2,4]`;
filter-form dominated convergence then proves continuity of
`x |-> norm(Phi(x))^2` on that closed interval.  Its formal axiom audit again
contains only `propext`, `Classical.choice`, and `Quot.sound`.

The pure real-variable boundary passage is now closed as well.  A general
lemma approaches both endpoints by `1/(n+1)`, uses continuity of the endpoint
data, joint continuity of real `rpow` (the two limiting exponents are positive
away from the trivial endpoint cases), and closedness of `<=`.  Instantiating
it gives the exact closed-strip inequality with endpoint second moments
`A,B`, again without a square-root loss and with only the three permitted
axioms.  This is distinct from the deep Conrey--Deshouillers--Iwaniec estimate
itself.  The Conrey left endpoint still remains.

The finite Gaussian covering is now formalized independently.  The explicit
midpoint grid covers `[U,V]` by windows of radius `Delta/2`, uses at most
```
floor ((V-U)/Delta) + 1
```
centres, and promotes a uniform full Gaussian local integral bound `L` to
```
integral_[U,V] g
  <= exp(1/4) * (floor ((V-U)/Delta) + 1) * L.
```
The factor `exp(1/4)` is exactly the reciprocal of the least Gaussian weight
on a half-window.  This step is purely real-variable and its axiom audit also
contains only `propext`, `Classical.choice`, and `Quot.sound`.

The detector adapter is now formalized too.  On `Re(s)=2/3` the inverse
pole-removal factor satisfies
```
norm ((s+1)/(s-1)) <= 5,
```
so the ordinary two-scale mollified error has square at most `25` times the
pole-free error square.  Its vertical section is continuous, the resulting
Gaussian local integrals are integrable, and the exact covering consequence
is
```
integral_[U,V] |F(2/3+it)|^2
  <= exp(1/4) * (floor ((V-U)/Delta) + 1) * (25*L),
```
whenever every covering centre has pole-free Gaussian `L^2` norm square at
most `L`.  No height restriction or unproved analytic premise is used in this
adapter, and its axiom audit again has only the three permitted axioms.

The critical-boundary normalization has now also been reduced exactly to the
published input.  The plateau--taper error is proved equal to
```
A * (zeta*S_Y1 - 1) - B * (zeta*S_Y0 - 1),
A = log(Y1)/log(Y1/Y0),  B = log(Y0)/log(Y1/Y0),  A-B=1.
```
Lean proves the component square inequality, Gaussian integrability, the
passage from Conrey's product `zeta*S_Y` to the error `zeta*S_Y-1` with
exact cost
```
2*C + 2*sqrt(pi/(1/Delta^2)),
```
and the pole-removal factor at `Re(s)=1/2`.  Consequently the only remaining
critical-boundary premise is the two one-scale Gaussian product moments in
Conrey equation (50), not any downstream two-scale or Hilbert-space claim.
This reduction has only the three permitted axioms.

The rational ledger for the smaller half-length target is formalized too:
`a=2/5`, `b=9/20`, `R=4`, `epsilon=1/2000` gives interpolation exponent
`1861/2100`, target saving `1/400`, slack `1/5040`, and `14/17` forcing
margin `3/6800`.  These are arithmetic certificates only; they do not assert
the missing half-length Gaussian mean square.

The first square-root AFE reduction is now formalized further, but it also
exposes a moving-cutoff obstruction that must not be hidden.  For a fixed
cutoff `N`, Lean proves the exact main and dual exponential-polynomial
identities, their full-line Gaussian integrability, and the bound
```
integral_R gaussian(Delta,w;t) * E_(N,X)(t)
  <= 2 * sqrt(pi/(1/Delta^2)) * C_Schur
       * 2*(1+log(NX))^4,
```
under `2*N*X <= Delta`.  The canonical AFE cutoff on a window where
```
sqrt(U/(2*pi)) < sqrt(L/(2*pi)) + 1
```
is proved to be either `N(L)` or `N(L)+1`.  Conditional only on the explicit
proposition `zeta_critical_afe_target`, the actual mollified-zeta integral on
such a window is consequently bounded by the two fixed-cutoff full-line
energies plus the exact full Gaussian mass times the canonical remainder.
All these theorems have only the three permitted axioms; the AFE remains a
parameter, not an axiom.

This local statement cannot be summed cutoff by cutoff.  In the half-range
case `N asymp U^(1/2)`, `X=U^b`, and Conrey's broad Gaussian has
`Delta=U^(1-eta)`.  The fixed-polynomial separation condition requires
`eta <= 1/2-b`.  Across one broad Gaussian there are then at least
```
Delta/sqrt(U) = U^(1/2-eta) >= U^b
```
different square-root cutoffs.  Applying the full-line bound independently
to every cutoff fibre therefore inserts a critical-boundary loss at least
`kappa=b`.  At `b=9/20`, interpolation transmits this with weight `20/21`,
giving exactly
```
1861/2100 + (20/21)*(9/20) = 2761/2100
                               = 8/9 + 2683/6300.
```
Thus this precisely defined independent-fibre method is a no-go even for
recovering Carlson's baseline.  This arithmetic obstruction is formalized.

There is, however, a direct paper-level repair which does not require a
separate rational-ray estimate.  Fix `0<eta<1/2-b`, put
`Delta=U^(1-eta)`, and let

```
 A(t)=sum_(m<=U^b) a_m m^(-1/2-it),   |a_m|<=1.
```

On `t asymp U`, the symmetric square-root approximate functional equation is

```
 zeta(1/2+it)=D_(K(t))(t)+chi(t) overline(D_(K(t))(t))+O(U^(-1/4)),
 D_K(t)=sum_(n<=K)n^(-1/2-it),
 K(t)=floor sqrt(t/(2 pi)),             |chi(t)|=1.       (8.1)
```

The key observation is pointwise, before integration:

```
 |chi(t) overline(D_(K(t))(t)) A(t)|
   =|D_(K(t))(t) A(t)|.                                (8.2)
```

Hence the dual AFE phase does not create a second rational-frequency
problem.  It is still essential that the phase in (8.1) be the correct
`exp(-2 I thetaPhase t)`; equality (8.2) then uses only its unit modulus.
Both AFE pieces are controlled by the same maximal ordinary Dirichlet
polynomial.

Here is the complete maximal estimate.  Set `N=floor(C sqrt(U))`.  For an
interval `J` of integers in `[1,N]`, write

```
 P_J(t)=A(t) sum_(n in J)n^(-1/2-it)
       =sum_(r<=U^b N)c_J(r)r^(-1/2-it),
 c_J(r)=sum_(mn=r, n in J)a_m.                           (8.3)
```

For every partition of `[1,N]` into disjoint intervals `J`, divisor Cauchy
gives, coefficient by coefficient,

```
 sum_J |c_J(r)|^2
 <=d(r) sum_(mn=r)|a_m|^2
 <=d(r)^2.                                               (8.4)
```

Consequently the ordinary Dirichlet-polynomial mean-value theorem, summed
over that partition, gives on every interval `I` of length `O(Delta)`

```
 sum_J integral_I |P_J(t)|^2 dt
 <<(Delta+U^(b+1/2)) sum_(r<=C U^(b+1/2)) d(r)^2/r
 <<Delta (log U)^4,                                      (8.5)
```

because `b+1/2<1-eta`.  Decompose every prefix `[1,K]` into at most
`O(log U)` binary intervals.  Cauchy over those intervals and then summing
(8.5) over the `O(log U)` dyadic levels proves the
Rademacher--Menshov bound

```
 integral_I max_(K<=N)|D_K(t)A(t)|^2 dt
 <<Delta (log U)^6.                                      (8.6)
```

Partition the Gaussian into translates of length `Delta`; their bounds in
(8.6) are summable with weights `exp(-c j^2)`.  Since the centre lies in
`[U,2U]` and `Delta=o(U)`, the translates leaving `t asymp U` contribute
`O(U^(-100))` by the Gaussian tail and polynomial growth.  Finally the AFE
remainder contributes

```
 integral gaussian * |A(t)O(U^(-1/4))|^2 dt
 <<Delta U^(b-1/2)
 <<Delta.                                                (8.7)
```

Equations (8.1)--(8.7) therefore prove, for every fixed
`b<1/2` (choose `eta<1/2-b`),

```
 integral_R exp(-(t-w)^2/Delta^2)
   |zeta(1/2+it)A(t)|^2 dt
 <<Delta (log U)^6,                                      (8.8)
```

uniformly for `U<=w<=2U`.  This applies separately to the linear mollifier
lengths `a=2/5` and `b=9/20`; the fixed coefficients in the two-scale
identity then preserve (8.8).  Thus the half-range critical-boundary input is
closed at paper level by the classical symmetric AFE, the ordinary
Dirichlet-polynomial mean-value theorem, and the finite dyadic maximal
argument above.  No Conrey--Deshouillers--Iwaniec estimate is needed for
this first `delta=1/400` target.  The remaining work is to formalize (8.1)
and (8.3)--(8.6), then perform the already specified dyadic density and
forcing assembly.

All proved analytic layers have now been composed into one public bridge.
Uniform Gaussian product bounds `C0,C1` for the two standard linear
mollifiers imply directly
```
integral_[U,V] |F_twoScale(2/3+it)|^2
  <= exp(1/4) * (floor ((V-U)/Delta) + 1)
       * 25 * L(Delta,Y0,Y1,C0,C1),
```
where `L` is the exact `20/21,1/21` interpolation of the proved critical and
right endpoint expressions.  The bridge contains no additional analytic
hypothesis and its axiom audit has only `propext`, `Classical.choice`, and
`Quot.sound`.  Thus the sole remaining formal premise before the ordinary
interior second moment is the critical-boundary product bound.  At the
`2/5,9/20` lengths it is supplied at paper level by (8.8); only lengths beyond
`1/2` require the Conrey--Deshouillers--Iwaniec theorem.

At the first formal target `R=4`, the closed-strip theorem has also been
specialized at `x=2/3`.  The interpolation weights reduce exactly to
`20/21` and `1/21`; the right endpoint is discharged by the proved
inverse-cube plateau-tail estimate.  The resulting theorem has only one
analytic hypothesis, namely the critical-boundary second-moment bound.  For
the half-range target this is (8.8); only the stronger `theta>1/2` targets
must come from the Conrey--Deshouillers--Iwaniec input.
The paper proof
leaves the following concrete Lean lemmas, none of which may be replaced by
a final density axiom:

1. For the smallest unconditional formal target `delta=1/400`, formalize
   the paper proof (8.1)--(8.8): the symmetric square-root AFE with exact
   dual phase `exp(-2 I thetaPhase t)`, the partition energy (8.4), and the
   nested-prefix dyadic maximal estimate (8.6).  Independent cutoff-fibre
   summation remains forbidden.  For `delta=1/20` or `5/64`,
   formalize Conrey's full `theta<4/7` theorem and its DI spectral input.

   The finite Cauchy ingredients are now formal: every prefix is bounded by
   the complete aligned dyadic tree, and the abstract divisor-fibre estimate
   gives collected energy at most `D^2` from fibre cardinality and raw energy
   at most `D`.  The arithmetic dyadic owner-map instantiation is also formal:
   at every level and product index `k`, the sum over aligned block owners is
   at most `d(k)^2`.  The critical-line `1/k` weight and the fourfold-divisor
   sum are now formal as well, giving each complete dyadic level coefficient
   energy at most `2(1+log(2^K X))^4`, uniformly in the level.  The levelwise
   Gaussian Schur mean square is now formal too: under `2(2^K X)<=Delta`, the
   sum of the Gaussian block moments has exactly the common Gaussian-mass
   factor times this polylogarithmic energy.  Its summation over the complete
   tree is now formal and costs only one factor `K+1`.  The remaining part of
   (8.4)--(8.6) has now also formalized the coefficient part of the exact
   block identity: filtering factor pairs by product and then by owner equals
   first restricting the zeta index to that owner block and then collecting
   by product.  The finite double-sum/product identity and the existing exact
   critical-line `cpow`-to-exponential conversion are now formal too, so every
   raw block times the concrete Selberg mollifier is exactly the polynomial
   used in the Gaussian tree estimate.  The actual moving prefix times the
   concrete mollifier is now pointwise bounded by `(K+1)` times the complete
   tree energy, with the ambient support handled by exact zero extension.
   The Gaussian integrability and monotone-integral composition are now
   formal too.  For every measurable selector `t |-> cutoff(t)` with
   `cutoff(t)<=2^K`, the selected moving-prefix moment is bounded by
   `(K+1)^2` times the common Gaussian mass, Schur constant, and
   `2(1+log(2^K X))^4`.  Thus the full Rademacher--Menshov selector estimate
   has only the intended logarithmic-square maximal loss and no hidden power
   of `U`.  Its axiom audit contains only `propext`, `Classical.choice`, and
   `Quot.sound`.  The canonical floor-square-root AFE cutoff is now proved
   measurable.  Since it is unbounded on the whole real line, Lean applies
   the maximal theorem to its exact clamp
   `min(criticalAfeCutoff(t)+1,2^K)` and proves that this clamp recovers the
   genuine prefix whenever `criticalAfeCutoff(t)+1<=2^K`.  The successor is
   essential: the AFE sum contains `1<=n<=criticalAfeCutoff(t)`, whereas the
   dyadic prefix is the half-open interval `[0,m)`.  Lean also proves the
   exact identity between this recovered prefix and the canonical AFE main
   sum times the concrete mollifier.  The resulting global
   Gaussian theorem has no measurability premise and the same allowed axiom
   audit.  The local-window cutoff upper bound is now formal as well: from
   `t in [L,U]` and `sqrt(U/(2*pi))<2^K`, Lean derives
   `criticalAfeCutoff(t)+1<=2^K`, so the recovered prefix identity applies
   pointwise throughout the window.  The global integrability hidden in the
   maximal proof is now exported, and the local-set-integral comparison is
   closed: the genuine main AFE term on `[L,U]` is replaced pointwise by the
   clamp, enlarged to the full real line by nonnegativity, and bounded by the
   proved `(K+1)^2` Gaussian selector estimate.  Its axiom audit again has
   only `propext`, `Classical.choice`, and `Quot.sound`.  The dual AFE
   polynomial is now proved to be the exact complex conjugate of the main
   polynomial.  Together with the proved unit norm of the corrected dual
   phase, this makes the complete dual-product norm-square pointwise equal to
   the main-product norm-square; its window Gaussian bound is therefore
   identical, with no new constant or logarithmic loss.  Its axiom audit is
   again the allowed three axioms.  The canonical remainder has now been
   assembled too.  Conditional only on the still-explicit symmetric AFE
   target, the complete mollified-zeta window moment is bounded by
   `3*(2*B_dyadic + GaussianMass*K_remainder)`, where `B_dyadic` is the
   proved `(K+1)^2` selector bound and `K_remainder` is exactly
   `(R*L^(-1/4)*2*sqrt(X))^2`.  The proof uses continuity only for the actual
   zeta product, while the right majorant is globally integrable.  Its axiom
   audit is again the allowed three axioms.  Thus the symmetric square-root
   AFE itself is now the sole analytic premise at this layer.  The half-range
   remainder and dyadic scale have now also been instantiated.  Lean proves
   exactly
   ```
   X <= L^(9/20)  =>  K_remainder <= 4*R^2*L^(-1/20) <= 4*R^2.
   ```
   It also chooses the first dyadic power above
   `sqrt(U/(2*pi))`, proves that it is at most twice this square-root scale,
   and hence reduces the polynomial separation hypothesis to the single
   condition
   ```
   4*sqrt(U/(2*pi))*X <= Delta.
   ```
   These facts are composed with the complete critical AFE window theorem,
   and their axiom audit again contains only the allowed three axioms.  The
   selected depth and polynomial logarithm are now normalized as well:
   ```
   K+1 <= 2*(1+log U),
   1+log(2^K*X) <= 2*(1+log U),
   B_dyadic <= 128*GaussianMass*C_Schur*(1+log U)^6.
   ```
   Lean composes this with the remainder to obtain the complete conditional
   local product bound
   ```
   integral_[L,U] gaussian*|zeta*M_X|^2
     <= 3*GaussianMass*(256*C_Schur*(1+log U)^6 + 4*R^2).
   ```
   Finally it fixes the common broad width `Delta=4*U^(19/20)` and proves
   that this covers every `X<=U^(9/20)`.  All these scale and logarithmic
   theorems again have only the allowed three axioms.  The full-real-line
   product integrability and the exact tail ledger are now formal too.  For
   every fixed `X>=2`, unconditional polynomial zeta growth and the elementary
   mollifier bound give
   ```
   |zeta(1/2+it) M_X(1/2+it)|^2 <= C_X (|t|+3)^8,
   ```
   hence the Gaussian product is integrable.  Lean then proves exactly
   ```
   integral_R gaussian*|zeta*M_X|^2
     = integral_[L,U] gaussian*|zeta*M_X|^2 + Tail(Delta,w,X,L,U)
   ```
   and combines this equality with the local AFE bound above.  The axiom
   audit is again the allowed three axioms.  The quantitative tail majorant
   is now formal as well.  Lean first replaces the fixed-length compact
   constant by one absolute constant and proves, uniformly for every `X>=2`,
   ```
   |zeta(1/2+it) M_X(1/2+it)|^2 <= C*X*(|t|+3)^8.
   ```
   Translation and dilation reduce the residual eighth polynomial Gaussian
   moment to one fixed nonnegative constant `K_8`, at cost `Delta^9`.  Hence,
   whenever the complement of `[L,U]` is at distance at least `D` from `w`,
   Lean proves exactly
   ```
   Tail <= C*X*(|w|+3)^8*Delta^9*K_8
             * exp(-D^2/(2*Delta^2)).
   ```
   It also proves that `w in [2V,3V]` is at distance at least `V` from the
   complement of `[V,4V]`.  At the algebraically convenient width
   `Delta=16*V^(19/20)`, Lean proves the exact exponent identity
   ```
   V^2/(2*Delta^2) = V^(1/10)/512
   ```
   and reduces the entire tail uniformly to
   `A*V^18*exp(-V^(1/10)/512)`.  The latter tends to zero, so the tail is
   eventually at most `1`, uniformly over `w in [2V,3V]` and
   `X<=V^(9/20)`.  Finally Lean verifies that this slightly enlarged width
   still dominates every AFE product frequency and obtains the conditional
   full-real-line bound
   ```
   integral_R gaussian*|zeta*M_X|^2
     <= 3*GaussianMass*(256*C_Schur*(1+log(4V))^6 + 4*R^2) + 1.
   ```
   Thus the Gaussian tail transfer is closed, not assumed.  All new theorems
   again have only the allowed three axioms.  The remaining analytic premise
   at this layer is exactly the explicit symmetric square-root AFE target;
   after discharging it, the standard linear mollifier can be identified and
   the full-line bound fed into the two-scale interface.
2. use item 1 for
   the left boundary norm, insert it into the proved closed-strip Hadamard
   specialization, and insert the resulting local norm into the now-proved
   detector-covering adapter; extending
   the same package to `R=1000` is an optional
   strengthening to `delta=5/64` rather than a gate to a power saving;
3. the dyadic assembly of those inputs into the unconditional
   `N(2/3,T)` certificate and its connection to the forcing chain.

Until all three remaining items are proved in Lean without new mathematical
axioms, the repository-level improved density certificate remains conditional.
At paper level the first `delta=1/400` target now uses only the classical
symmetric AFE and Dirichlet-polynomial mean value through (8.1)--(8.8);
the stronger `theta<4/7` targets still use the cited Conrey theorem.

### 8.1 A strictly weaker AFE which is sufficient for the formal target

The exact phase and the log-free remainder in `zeta_critical_afe_target` are
stronger than the critical-boundary argument needs.  It is enough to prove
that there are constants `R>0` and `T0>=1` such that, for every `t>=T0`, there
are `u(t),E(t) in C` with

\[
 |u(t)|=1,
 \qquad
 \zeta(1/2+it)=D_{K(t)}(t)+u(t)\overline{D_{K(t)}(t)}+E(t),             \tag{8.9}
\]

and

\[
 |E(t)|\le R t^{-1/4}(1+\log t).                                      \tag{8.10}
\]

Here `K(t)=floor(sqrt(t/(2*pi)))`, with the same inclusive cutoff as in
(8.1).  No regularity of `u(t)` is required.  Indeed, pointwise,

\[
 |u(t)\overline{D_{K(t)}(t)}A(t)|^2
   =|D_{K(t)}(t)A(t)|^2,                                                \tag{8.11}
\]

because `|u(t)|=1` and complex conjugation preserves norm.  Thus the same
dyadic maximal estimate controls both finite sums.  Moreover the elementary
bound `|A(t)|<=2 sqrt(X)` gives

\[
 |E(t)A(t)|^2
 \le 4R^2 X t^{-1/2}(1+\log t)^2
 \le 4R^2 t^{-1/20}(1+\log t)^2=O_R(1)                                \tag{8.12}
\]

for `X<=t^(9/20)`.  The last function tends to zero.  Hence replacing the
sharp remainder in (8.1) by (8.10) changes no power and costs at most two
harmless logarithms before its eventual boundedness is used.

Titchmarsh, Theorem 4.13, proves precisely the stronger formula with the
exact functional-equation multiplier and error

\[
 O(x^{-\sigma}\log t)+O(t^{1/2-\sigma}y^{\sigma-1}),
 \qquad 2\pi xy=t.
\]

At `sigma=1/2` and `x=y=sqrt(t/(2*pi))` this is (8.9)--(8.10); on the
critical line the exact multiplier has norm one.  Consequently the paper
proof of the first `delta=1/400` target needs only Titchmarsh's imperfect
approximate functional equation, not the sharper Theorem 4.15.

For Lean, the shortest honest proof route is correspondingly narrower than
the full sharp AFE.  The required analytic leaf is the weighted
van-der-Corput/Poisson transformation used in Titchmarsh Lemma 4.10 and
Theorem 4.13, specialized to `g(u)=u^(-1/2)` and
`f(u)=-(t/(2*pi))*log u`.  The repository already contains the exact Abel
floor-error identity, the absolutely convergent second-Bernoulli Fourier
series, and first- and second-derivative oscillatory integral bounds.  What
is not yet present is the transformation which extracts the stationary
modes as the conjugate square-root Dirichlet polynomial.  In the mathlib
Fourier convention used below these are the negative modes `k=-m`, with
positive dual index `m`.  The positive modes and the negative modes outside
the stationary range are nonstationary; their reciprocal distance-to-endpoint sum is the single
`log t` in (8.10).  This is the exact next analytic lemma.  A long cutoff
followed by independent mean value, or independent summation over moving
cutoff fibres, does not prove (8.9) and incurs the power losses already
recorded above.

One boundary-integral sublemma in this route is now unconditional in Lean.
For `0<Re(z)<1`, `c>0`, `A<=B`, and

\[
  2|\Im z|\le cA,
\]

the principal-power normalization is kept exactly and the repository proves

\[
 \left|\int_A^B u^{z-1}e^{icu}\,du\right|
 \le \frac{8}{c}A^{\Re z-1}.                                      \tag{8.13}
\]

Indeed
`u^(z-1)e^(icu)=u^(-(1-Re(z))) exp(i(cu+Im(z)log u))`; the phase derivative
is `c+Im(z)/u`, so the displayed hypothesis leaves it at distance at least
`c/2` from zero, while the radial weight is positive decreasing.  The bound
therefore follows from the already formal first-derivative estimate and is
uniform in `B`.  This supplies the Cauchy right tail needed when the damped
Gamma ray is moved to angle `pi/2`; it does not by itself prove the boundary
Gamma identity or the Poisson transformation, which remain the next gates.
Lean now also applies (8.13) to the natural truncations
`integral_[1,N] u^(z-1)e^(icu) du` and proves the Cauchy criterion, hence the
existence of their limit for every `Re(z)<1` and `c>0`.  This latter theorem
still makes no assertion about the value of the limit; identifying it with
`exp(i*pi*z/2)c^(-z)Gamma(z)` is the remaining Abel-boundary step.

The damping-uniform version is formal as well.  If `r>=0` and the other
hypotheses of (8.13) hold, Lean proves

\[
 \left|\int_A^B u^{z-1}e^{-ru}e^{-icu}\,du\right|
 \le \frac{8}{c}A^{\Re z-1},                                      \tag{8.14}
\]

with no dependence on `r` or `B`.  The proof abstracts the same
bounded-primitive argument to a positive decreasing `C^1` weight and applies
it to
`exp(-(1-Re(z))log u-r u)`.  Thus the two tails in the Abel boundary passage
are now quantitatively uniform; the remaining work is the compact-interval
limit, the positive-real scaling of the rotated Mellin integral, and the
final limit-uniqueness calculation.

The compact-interval limit is now formal too.  For every fixed
`0<a<=b`, arbitrary `z` and real frequency `c`, Lean proves

\[
 \lim_{r\to0+}\int_a^b u^{z-1}e^{-ru}e^{-icu}\,du
   =\int_a^b u^{z-1}e^{-icu}\,du.                                  \tag{8.15}
\]

The dominating function is exactly `u^(Re(z)-1)` on `[a,b]`; no tail or
absolute-convergence claim is hidden in (8.15).  Together, (8.14) and (8.15)
close the compact-plus-right-tail part of the Abel passage.  It remains to
add the absolutely convergent `(0,1]` piece and identify the damped whole-ray
integral with the already formal rotated Mellin/Gamma expression.

The endpoint piece is now formal.  Under the exact local condition
`0<Re(z)`, Lean proves the analogue of (8.15) on `[0,1]`.  The proof only
uses continuity on `(0,1]`; the omitted endpoint has measure zero, while
`intervalIntegrable_rpow'` supplies integrability of
`u^(Re(z)-1)`.  Hence all three limiting pieces needed for the Abel passage
are available: the origin segment, an arbitrary fixed positive compact
segment, and a right tail uniform in the damping.  The remaining boundary
Gamma gate is now algebraic/measure-theoretic assembly with the rotated
Mellin identity, not a further oscillatory estimate.

The negative phase selected by the upper Gamma-ray rotation now has its own
canonical boundary value in Lean.  Natural truncations of
`integral_[1,N] u^(z-1)e^(-icu) du` converge for `Re(z)<1`, and their distance
to the canonical value satisfies the same `8*N^(Re(z)-1)/c` bound.  In
addition, for `0<Re(z)<1` and `r>0`, the actual set integral on `Ioi A` is
absolutely integrable and satisfies

\[
 \left|\int_A^\infty u^{z-1}e^{-ru}e^{-icu}\,du\right|
 \le \frac{8}{c}A^{\Re z-1},                                      \tag{8.16}
\]

uniformly in `r`.  This is obtained by first majorizing with
`u^(Re(z)-1)e^(-ru)` and then passing the finite bound (8.14) to the
improper limit.  Thus the final Abel assembly can compare actual whole-ray
damped integrals with the canonical conditional boundary value without any
unproved interchange of limits.

The full Abel assembly is now formal.  Define

\[
 J_r^-(z,c)=\int_0^\infty u^{z-1}e^{-ru}e^{-icu}\,du
\]

for `r>0`, and define `J_0^-(z,c)` as the ordinary integral on `[0,1]`
plus the canonical natural-truncation limit on `[1,infinity)`.  Then for
`0<Re(z)<1` and `c>0`, Lean proves

\[
 \lim_{r\to0+}J_r^-(z,c)=J_0^-(z,c).                              \tag{8.17}
\]

The proof chooses one integer `N` so that both
`2*|Im(z)|<=c*N` and `8*N^(Re(z)-1)/c<epsilon/3` hold, applies dominated
convergence on `[0,N]`, and spends the other two thirds of the error on the
damped and undamped tails.  Positive damping is separately proved to make
the whole `Ioi 0` integral absolutely integrable, so (8.17) does not rely on
the convention that a nonintegrable set integral is zero.  The remaining
Gamma gate is the positive-real scaling of the rotated Mellin identity and
limit uniqueness; no further tail estimate is needed.

That remaining unit-frequency Gamma gate is now formal.  For
`0<Re(z)<1`, positive-real scaling of the already proved rotated Mellin
identity gives, for `0<epsilon<pi/2`,

\[
 J^-_{\tan\epsilon}(z,1)
 = (\cos\epsilon)^z
   e^{-i(\pi/2-\epsilon)z}\Gamma(z).
\]

Composing (8.17) with `tan epsilon -> 0+` and using continuity of the
principal power at `cos 0=1`, Lean then proves

\[
 J^-_0(z,1)=e^{-i\pi z/2}\Gamma(z).                               \tag{8.18}
\]

The proof uses limit uniqueness in the nontrivial right-neighborhood filter;
there is no appeal to a formal integral whose integrand is not absolutely
integrable.  What remains for the exact Titchmarsh kernel is positive
frequency, arbitrary positive scaling, and the weighted Poisson summation
step.

The frequency and sign normalizations are now formal as well.  For every
`c>0`, positive-real scaling and a second Abel-limit uniqueness argument give

\[
 J^-_0(z,c)=c^{-z}e^{-i\pi z/2}\Gamma(z).
\]

Conjugating at the conjugate exponent then gives the exact Titchmarsh sign,

\[
 J^+_0(z,c)=c^{-z}e^{i\pi z/2}\Gamma(z).                          \tag{8.19}
\]

Lean also proves that the actual natural truncations

\[
 \int_0^1u^{z-1}e^{icu}\,du+\int_1^N u^{z-1}e^{icu}\,du
\]

converge to `J^+_0(z,c)`.  Thus (8.19) is not merely a definition by
conjugation: it is the value of the intended conditionally convergent
positive-phase improper integral.  The Gamma boundary integral is therefore
closed.  The next unresolved analytic input is precisely the weighted
truncated Poisson transformation used in Titchmarsh Theorem 4.13.

The first exact Poisson layer is now formal as well.  For real `x<=N`, let
`w_{x,N}` be a fixed smooth bump centered at `(x+N)/2`, with inner radius
`(N-x)/2+1` and outer radius `(N-x)/2+2`.  Then

\[
  0\leq w_{x,N}\leq1,\qquad
  w_{x,N}(u)=1\quad(x\leq u\leq N),
\]

and

\[
  w_{x,N}(u)=0\quad
  (u\leq x-2\ \hbox{or}\ u\geq N+2).                         \tag{8.20}
\]

For `2<x<=N`, the function

\[
  F_{s,x,N}(u)=w_{x,N}(u)\exp(-s\log u)                         \tag{8.21}
\]

is globally smooth and compactly supported.  The apparent singularity at
zero is harmless because (8.20) makes the function identically zero on a
neighborhood of zero.  It is therefore a Schwartz function, and the
mathlib Poisson theorem gives the unconditional identity

\[
  \sum_{n\in\mathbb Z}F_{s,x,N}(n)
   =\sum_{k\in\mathbb Z}\widehat F_{s,x,N}(k),\qquad
  \widehat F(k)=\int_{\mathbb R}F(u)e^{-2\pi iku}\,du.          \tag{8.22}
\]

On `[x,N]`, (8.21) is exactly `u^{-s}` with the principal-power
normalization.  The difference between its integer sum and the hard finite
sum is supported on the two transition intervals of total length four; on
the critical line it is therefore `O((x-2)^(-1/2))`.  Thus smoothing the
finite endpoints cannot consume a power of `T`.

For integral endpoints `m<=n` the formal statement is sharper: all integer
terms outside `[m-1,n+1]` vanish, all terms in `[m,n]` are unchanged, and
the smoothed sum is exactly the hard sum plus the two terms at `m-1` and
`n+1`.  Lean also proves the pointwise bound

\[
  |F_{s,m,n}(u)|\leq u^{-\Re s}\qquad(u>0),                       \tag{8.22a}
\]

so these two terms have total size at most
`(m-1)^(-sigma)+(n+1)^(-sigma)`.

With `s=sigma+it`, the phase in the `k`-th Fourier integral is

\[
  -t\log u-2\pi ku.
\]

This normalization is now an exact Lean identity, including the Fourier
sign, the factor `2*pi`, the positive amplitude
`w_{x,N}(u)u^(-sigma)`, and restriction of every Fourier integral to
`[x-2,N+2]`.

The corresponding phase geometry is now formal too.  With
`Phi_k(u)=-t log u-2*pi*k*u`, Lean proves

\[
 \Phi_k'(u)=-\frac{t}{u}-2\pi k,\qquad
 \Phi_{-m}'(u)=2\pi m-\frac{t}{u}.                              \tag{8.22b}
\]

For `t,u>0`, every `k>=0` has `Phi_k'(u)<0`; and for every positive natural
number `m`,

\[
 \Phi_{-m}'(u)=0\quad\Longleftrightarrow\quad
 u=\frac{t}{2\pi m}.                                           \tag{8.22c}
\]

These statements have only `propext`, `Classical.choice`, and `Quot.sound`
in their axiom audit.

The exact nonstationary bounds on a positive core interval `[a,b]` are now
formal as well.  For `t>=0`, `p>0`, and
`Psi_k(u)=2*pi*k*u-t log u`, Lean proves

\[
 \left|\int_a^b u^{-p}e^{i\Psi_k(u)}du\right|
 \leq \frac{4a^{-p}}{t/b-2\pi k}
 \quad\left(t/b-2\pi k>0\right),                               \tag{8.22d}
\]

and

\[
 \left|\int_a^b u^{-p}e^{i\Psi_k(u)}du\right|
 \leq \frac{4a^{-p}}{2\pi k-t/a}
 \quad\left(2\pi k-t/a>0\right).                              \tag{8.22e}
\]

The proof uses the monotonicity of `Psi'_k` and retains the precise distance
to the nearest endpoint frequency.  Consequently these estimates are in the
right normalization for the two harmonic endpoint sums; no uniform-gap
coarsening has been introduced.

Lean also proves the exact curvature identity

\[
 \Psi_k''(u)=\frac{t}{u^2},                                    \tag{8.22e'}
\]

away from `u=0`.  In particular the curvature is positive at positive
height and independent of `k`.  This is the normalized `F''` input for the
remaining twice-integrated far-frequency estimate; treating
`u^{-it}` as part of a nonoscillatory Fourier amplitude would instead create
a spurious power loss and is explicitly not used.

The exact twice-integrated nonlinear-phase identity is now formal.  Write
`E=exp(iF)` and choose quotient amplitudes `Q,R` satisfying

\[
 A=Q(iF'),\qquad Q'=R(iF').                                  \tag{8.22e''}
\]

If `Q,Q',R,R'` have the stated interval differentiability/integrability and
both `Q` and `R` vanish at both endpoints, two integrations by parts give

\[
 \int_a^b A(u)e^{iF(u)}du
   =\int_a^b R'(u)e^{iF(u)}du,
 \qquad
 \left|\int_a^b A(u)e^{iF(u)}du\right|
   \leq\int_a^b|R'(u)|du.                                    \tag{8.22e'''}
\]

The Lean theorem is purely algebraic/analytic infrastructure and its axiom
audit has only the allowed three axioms.  The first quotient is now also
formalized without choosing a branch or a complex division convention:

\[
 Q(u)=(F'(u))^{-1}(-i)A(u).
\]

At every point where `F'` is nonzero, Lean proves the exact derivative

\[
 Q'=\frac1{F'}(-iA')-\frac{F''}{(F')^2}(-iA),
\]

as well as `Q(iF')=A`; it also proves that `A=0` implies `Q=0`, so the
first endpoint condition follows directly from the cutoff endpoint
condition.  Lean now defines the corresponding second quotient
`R=Q'/(iF')`, proves `R(iF')=Q'`, and proves the sharp endpoint implication
`A=A'=0 -> R=0`.  It also proves

\[
 \left(-\frac{F''}{(F')^2}\right)'
 =-\frac{F'''}{(F')^2}+\frac{2(F'')^2}{(F')^3},
\]

the exact four product-rule terms in `Q''`, and the exact quotient-rule
derivative of `R`.  Lean now also proves the collected identity

\[
 R'=-\frac{A''}{(F')^2}
     +\frac{3F''A'}{(F')^3}
     +\frac{F'''A}{(F')^3}
     -\frac{3(F'')^2A}{(F')^4}.                              \tag{8.22e''''}
\]

Thus only the L1 estimates for these four amplitude classes remain.

For those quantitative estimates the earlier `ContDiffBump` plateau is not
used: its public API exposes smoothness and support but no derivative bound
uniform in the two endpoints.  Lean now contains the explicit replacement

\[
 w_{x,N}(u)=\eta(u-x+1)\eta(N+1-u),
 \qquad \eta=\operatorname{smoothTransition}.                \tag{8.22e'''''}
\]

It is `C-infinity`, lies in `[0,1]`, is exactly one on `[x,N]`, and vanishes
outside `[x-1,N+1]`.  Both transition strips therefore have fixed width one,
and every derivative bound reduces to a bound for the single fixed function
`eta`; there is no endpoint- or height-dependent bump constant.  These
properties and compact support are formal with only the allowed axioms.  The
first and second derivatives of `eta` are now proved to vanish outside
`[0,1]`; compactness and continuity then give constants `C1,C2>=0` such that

\[
 |\eta'(u)|\leq C_1,
 \qquad |\eta''(u)|\leq C_2                              \tag{8.22e''''''}
\]

for every real `u`.  These constants are absolute and independent of
`x,N,t,k`.  The exact translated product rules and their uniform consequences
are now formal too:

\[
 |w_{x,N}'(u)|\leq 2C_1,
 \qquad
 |w_{x,N}''(u)|\leq 2C_2+2C_1^2.                         \tag{8.22e'''''''}
\]

Thus the remaining derivative gate is only the elementary product with the
Mellin amplitude `u^(-sigma)` on the positive support interval; no cutoff
constant can depend on height.  That exact product rule is now formal.  With
`A=w_{x,N}u^(-sigma)`, Lean proves, for `u!=0`,

\[
 A'=w'u^{-\sigma}-\sigma w u^{-\sigma-1},
\]

and

\[
 A''=w''u^{-\sigma}-2\sigma w'u^{-\sigma-1}
     +\sigma(\sigma+1)w u^{-\sigma-2}.                    \tag{8.22e''''''''}
\]

Both real and complex-embedded `HasDerivAt` statements pass the axiom audit.
Lean also proves that `w'` and `w''` vanish identically off

\[
 [x-1,x]\cup[N,N+1],                                      \tag{8.22e'''''''''}
\]

including vanishing throughout the plateau `[x,N]`.  Hence their L1 costs
come from two unit intervals, not from an interval of length `N`.  The next
step is the pointwise size bound on the positive support and its integration
in the four classes of (8.22e'''').

The pointwise size part is now formal as well.  For `u>0`, the same absolute
constants `C1,C2` give

\[
 |A(u)|\leq u^{-\sigma},
\]

\[
 |A'(u)|\leq 2C_1u^{-\sigma}
       +|\sigma|u^{-\sigma-1},
\]

and

\[
 |A''(u)|\leq (2C_2+2C_1^2)u^{-\sigma}
       +4C_1|\sigma|u^{-\sigma-1}
       +|\sigma||\sigma+1|u^{-\sigma-2}.                 \tag{8.22e''''''''''a}
\]

All three inequalities pass the allowed-axiom audit.  The still-open part of
this step is integration after inserting the nonstationary lower bound for
`|F'|`; no pointwise amplitude estimate remains implicit.

Lean now composes these three bounds with the exact four-term estimate for
`R'`.  The resulting theorem is precisely the sum of the `|F'|^{-2}` term
times (8.22e''''''''''a), the `3|F''||F'|^{-3}` term times the `A'` bound,
and the two `A` terms with coefficients `|F'''||F'|^{-3}` and
`3|F''|^2|F'|^{-4}`.  Every multiplier is kept under an absolute value, so
the composition uses only monotonicity of multiplication by a nonnegative
number.  This combined majorant also passes the allowed-axiom audit.  Thus
the exact next lemma is a velocity-gap lemma on `[x-1,N+1]`, followed by the
ordinary integrals of these already explicit nonnegative functions; neither
amplitude expansion nor quotient algebra remains open.

The velocity-gap lemma is now formal in all three required regions.  For
`t>=0`, `u>0`, and `k>=0`, Lean proves the exact identity

\[
 |F'_k(u)|=\frac tu+2\pi k,
\]

and hence both `t/u` and `2*pi*k` are lower bounds.  For a negative mode
`k=-m` and `u in [a,b]`, it proves

\[
 \frac tb-2\pi m\leq |F'_{-m}(u)|
 \quad\hbox{when }2\pi m\leq\frac tb,
\]

and

\[
 2\pi m-\frac ta\leq |F'_{-m}(u)|
 \quad\hbox{when }\frac ta\leq2\pi m.                     \tag{8.22e''''''''''b}
\]

The exact `2*pi` normalization is retained, and all three statements pass
the allowed-axiom audit.  After the closest endpoint integers are kept in the
expanded stationary band, the remaining open step is therefore only to turn
the positive gaps in (8.22e''''''''''b) into reciprocal powers, integrate
the rpow majorants, and invoke the already proved shifted harmonic sums.

The reciprocal-power conversion is now formal for every natural `n`:

\[
 0<g\leq |v|\quad\Longrightarrow\quad
 \left|\frac{c}{v^n}\right|\leq\frac{|c|}{g^n}.           \tag{8.22e''''''''''c}
\]

Lean also fixes the numerator normalization (for `t>=0`, `u>0`)

\[
 |F''(u)|=\frac{t}{u^2},\qquad
 |F'''(u)|=\frac{2t}{u^3}.                                \tag{8.22e''''''''''d}
\]

Both statements pass the allowed-axiom audit.  Consequently the only
remaining part of this far-tail estimate is the interval integration of the
resulting rpow monomials and the finite/infinite frequency summation; the
passage from endpoint gap to denominator powers is no longer an open premise.

**Uniformity checkpoint (2026-08-30).** The pointwise gap majorant is now
formal, and the positive-interval rpow antiderivative and its endpoint upper
bounds are formal too.  These facts do not yet imply a uniform far-tail
estimate: integrating the coarse `u^(-1/2)` term over the full support gives
`O(sqrt(N))`.  That bound is valid but unsuitable for the cutoff limit.
The next integration step must retain the support of `w'` and `w''`.
Writing `a=x-1`, `D1=2*C1`, and `D2=2*C2+2*C1^2`, for `p>=0` the required
transition estimate is

\[
 \int_a^{N+1}|w^{(j)}(u)|u^{-p}\,du\leq 2D_j a^{-p},\qquad j=1,2.
\]

It follows by splitting at `x,N`: the middle integral is zero and each
outer interval has length one.  For `sigma>0` this gives the uniform target

\[
 \int_a^{N+1}|A''(u)|\,du
 \leq 2D_2a^{-\sigma}+(4\sigma D_1+\sigma)a^{-\sigma-1}.
\]

This support-aware estimate is now formal in
`AFEExplicitMellinSecondL1`, including its pointwise precursor, with no
upper-cutoff dependence and only the allowed foundational axioms.
Modes near the endpoint frequency continue to use the first-derivative
harmonic bound; only the distant frequency tail uses the second-derivative
estimate.

For that tail no support refinement of the other three terms is necessary.
For `sigma>0`, `t>=0`, and a constant gap `0<g<=|F'|`, put

\[
 B_2=2D_2a^{-\sigma}+(4\sigma D_1+\sigma)a^{-\sigma-1}.
\]

Retain the actual `|A''|` in the first term, and use the coarse bounds only
in terms already multiplied by `u^(-2)` or faster decay.  The exact
four-term quotient bound then gives

\[
 |R'|\leq g^{-2}|A''|
  +\frac{6C_1t}{g^3}u^{-\sigma-2}
  +\frac{(3\sigma+2)t}{g^3}u^{-\sigma-3}
  +\frac{3t^2}{g^4}u^{-\sigma-4}.
\]

All coefficients are nonnegative.  Integrating and using
`integral_a^b u^(-sigma-j) <= a^(1-sigma-j)/(sigma+j-1)` for `j=2,3,4`
therefore proves the cutoff-uniform bound

\[
 \left|\int_a^{N+1} A(u)e^{iF(u)}\,du\right|
 \leq \frac{B_2}{g^2}
 +\frac{6C_1t}{g^3}\frac{a^{-\sigma-1}}{\sigma+1}
 +\frac{(3\sigma+2)t}{g^3}\frac{a^{-\sigma-2}}{\sigma+2}
 +\frac{3t^2}{g^4}\frac{a^{-\sigma-3}}{\sigma+3}.
\]

The proof uses the already established zero boundary terms at both ends.
Both the support-preserving pointwise gap bound and this integrated bound
are now formal in `AFEExplicitPoissonUniformIntegral`; its exact-statement
contract and allowed-axiom audit pass (exit code zero).
This is only a nonstationary-mode estimate: summation over the distant
frequencies, the intermediate endpoint band, and replacement of the
stationary integrals by their Gamma values remain separate obligations.

In particular, for an integer `m>=1` with `t/a<=pi*m`, both modes
`k=m` and `k=-m` have gap `g=pi*m`: the positive mode has
`|F'|=t/u+2*pi*m`, while the negative mode has
`F'=2*pi*m-t/u>=pi*m`.  Thus `t/g<=a` and the last bound is at most

\[
 \frac{1}{(\pi m)^2}\left[
 \left(2D_2+\frac{6C_1}{\sigma+1}\right)a^{-\sigma}
 +\left(4\sigma D_1+\sigma+
       \frac{3\sigma+2}{\sigma+2}+\frac3{\sigma+3}\right)
       a^{-\sigma-1}\right].
\]

For `a>=1` this is `C_sigma*a^(-sigma)/(pi*m)^2`.  The elementary bound
`sum_(m>=1) 1/m^2 <= 2` follows from
`1/m^2 <= 1/(m-1)-1/m` for `m>=2` and telescoping.  Consequently the
combined distant tails are bounded by `4*C_sigma*a^(-sigma)/pi^2`,
uniformly in `N`.  Frequencies failing `t/a<=pi*m` have not been estimated
by this argument; they remain in the finite endpoint/stationary ledger.
For a simpler explicit constant, the same argument permits

\[
 C_\sigma=4C_2+4C_1^2+8\sigma C_1+6C_1+4\sigma+5.
\]

Indeed, put `r=t/(a*g)`, so `0<=r<=1`.  After extracting
`a^(-sigma)/g^2`, the bracket is
`2D2+(8*sigma*C1+sigma)/a+6*C1*r/(sigma+1)`
`+(3*sigma+2)*r/(a*(sigma+2))+3*r^2/(a*(sigma+3))`.
Every displayed reciprocal ratio is at most one for `a>=1,sigma>0`.
This verifies the stated constant without any asymptotic convention.
The paired-mode estimate and its sum over every finite far-frequency set
are now proved in `AFEExplicitPoissonFarTail`.  The same file also proves
that the nonnegative mass of the whole distant tail is summable and that
its infinite sum satisfies the identical bound.  Summability is part of the
theorem, not inferred from an isolated `tsum` inequality.  The finite-set
and infinite-series contracts and their allowed-axiom audits pass.

**Cutoff interface check.** The older `AFEWeightedPoissonCutoff` Poisson
identity uses `intervalPlateauBump` with width-two transitions.  The uniform
derivative and tail bounds above instead use `explicitIntervalPlateau` with
width-one transitions.  These functions are not definitionally equal.
The Schwartz Poisson formula must therefore be instantiated for the explicit
cutoff and its Fourier transform identified with `explicitPoissonMode`,
before composing this tail estimate with a Poisson pipeline.  This fresh
instantiation is now proved in `AFEExplicitPoissonIdentity`, including
smoothness at zero, exact Fourier sign, the Poisson identity, and the exact
finite primal sum at integer endpoints.  No equality between the two
different cutoff functions is asserted.

For this interface use exactly
`f_s(u)=w_(x,N)(u)*exp(-s*log(u))`.  It is smooth away from zero and
identically zero on a neighborhood of zero when `x>1`, hence globally
smooth and compactly supported.  Schwartz Poisson summation applies to
this very function.  With the convention `exp(-2*pi*i*k*u)`, its Fourier
transform is exactly `explicitPoissonMode` at `s=sigma+i*t`, since
`exp(-s*log u)=u^(-sigma)*exp(-i*t*log u)` on `u>0`.
For integer endpoints `m<=n`, there are no extra smoothing summands:
`w_(m,n)=1` at the integers in `[m,n]` and `w_(m,n)=0` at every other
integer, including `m-1` and `n+1`.  Thus its primal Poisson sum is exactly
`sum_(m<=j<=n) j^(-s)`.  This is a fresh instantiation, not an equality
between the old width-two bump and the explicit width-one cutoff.

For the remaining nonstationary finite band, a support-aware first-derivative
bound is available on paper.  Suppose `sigma>0`, `a=x-1>0`, `b=N+1`, the
phase is twice continuously differentiable on `[a,b]`, its derivative is
monotone, and `|F'|>=g>0` throughout.  Define
`H(v)=integral_a^v u^(-sigma)*exp(i*F(u)) du`.  The existing first-derivative
lemma, applied to every `[a,v]`, gives `|H(v)|<=4*a^(-sigma)/g`.
Since `w(a)=w(b)=0`, integration by parts gives
`integral_a^b w*H' = -integral_a^b w'*H`.  The two unit transitions give
`integral_a^b |w'| <= 4*C1`; hence

\[
 \left|\int_a^b w(u)u^{-\sigma}e^{iF(u)}\,du\right|
 \leq 16C_1a^{-\sigma}/g.
\]

This step uses no cancellation of arithmetic coefficients.  Its endpoint
gaps can be summed with the previously proved shifted harmonic bounds.
The first-derivative estimate is now formal in
`AFEExplicitPoissonFirstDerivative`, including construction and
differentiability of the primitive, its pointwise bound, both zero cutoff
boundary terms, and the transition L1 bound.  The exact contract builds
successfully and its axiom audit contains only the allowed three axioms.
The zero Fourier mode must instead retain its exact Mellin antiderivative
and be combined with the Euler--Maclaurin main term before the `N` limit;
the small gap `t/(N+1)` must not be treated as uniform in this argument.

For the actual Poisson phase, `F'=-t/u-2*pi*k` is increasing on the positive
axis when `t>=0`.  Hence positive indices `k=m>=1` have gap `2*pi*m`,
and the first-derivative bound gives

\[
 \sum_{m=1}^{M}|I_m|
 \leq \frac{8C_1a^{-\sigma}}{\pi}(1+\log M).
\]

For the negative modes put `beta=t/(2*pi*a)` and
`m_j=floor(beta)+1+j`, `1<=j<=M`.  Their gap is
`2*pi*(m_j-beta)>0`, so the shifted harmonic bound gives

\[
 \sum_{j=1}^{M}|I_{-m_j}|
 \leq \frac{8C_1a^{-\sigma}}{\pi}(1+\log M).
\]

The nearest integer `floor(beta)+1` is deliberately omitted from this
formula.  It remains in the endpoint/stationary error ledger.  If `N>=t`,
then for every positive integer `m` its stationary point
`t/(2*pi*m)` lies below `N+1`; thus no negative mode has a stationary
point beyond the right support endpoint.  This simplification is legitimate
in the eventual upper-cutoff limit but is not assumed in the two displayed
finite-sum estimates, which hold for every `N>=x`.
Both displayed finite-band estimates are now proved in
`AFEExplicitPoissonFiniteBand`; the proof derives phase smoothness and
monotonicity internally and retains the exact `2*pi` frequency normalization.
The contract build exits zero (8721 jobs including cached dependencies),
with only `propext`, `Classical.choice`, and `Quot.sound` in both axiom audits.

The zero mode has a separate elementary treatment.  Put `s=sigma+i*t`,
`sigma>=0`, `t>0`, and retain the same width-one cutoff.  Split its integral
at `x,N`.  On the core the cutoff is one, so the principal-power
antiderivative on the positive axis gives

\[
 I_0=\frac{N^{1-s}-x^{1-s}}{1-s}+E_L+E_U,
 \qquad |E_L|\leq(x-1)^{-\sigma},\quad |E_U|\leq N^{-\sigma}.
\]

The two error bounds use only the unit transition lengths and `0<=w<=1`.
Consequently, since `|1-s|>=t`,

\[
 \left|I_0-\frac{N^{1-s}}{1-s}\right|
 \leq(x-1)^{-\sigma}+N^{-\sigma}+\frac{x^{1-\sigma}}{t}.
\]

This is the precise zero-mode estimate to combine with the already proved
Euler--Maclaurin truncation.  For `sigma>0`, the upper transition error
tends to zero as `N` tends to infinity.  The subtraction must precede this
limit; neither `I_0` nor `N^(1-s)/(1-s)` is asserted to converge separately.
Both displayed zero-mode inequalities are now formal in
`AFEExplicitPoissonZeroMode`.  Its exact contract build exits zero (8720
jobs including cached dependencies), and both axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.  This closes the uniform
zero-mode estimate, not the subsequent combined cutoff-limit assembly.

For a stationary negative mode the lower tail of its full Gamma integral
must also retain oscillation.  Here is the exact bound, with no lower-cutoff
loss: if `0<sigma<1`, `c>=0`, `x>0`, and `c*x<t`, then

\[
 \left|\int_0^x u^{-\sigma}e^{i(cu-t\log u)}\,du\right|
 \leq \frac{2x^{1-\sigma}}{t-cx}.                         \tag{8.22-lower}
\]

To prove it first take `0<A<=x`, set `F(u)=cu-t log u` and
`r(u)=u^(1-sigma)/(t-cu)`.  The denominator is positive, and

\[
 r'(u)=\frac{(1-\sigma)u^{-\sigma}}{t-cu}
       +\frac{c u^{1-\sigma}}{(t-cu)^2}\geq0,
 \qquad (i r(u))(iF'(u))=u^{-\sigma}.
\]

Integration by parts therefore bounds the integral on `[A,x]` by
`r(x)+r(A)+integral_A^x r'=2r(x)`.  All functions involved are smooth
on this compact positive interval, so the derivative integral is exactly
`r(x)-r(A)`.  Finally `u^(-sigma)` is integrable at zero because `sigma<1`,
and `r(A)` tends to zero.  Thus the interval integrals converge to the
displayed integral as `A` tends down to zero, preserving the bound.
For `c=2*pi*m`, this keeps precisely the harmonic endpoint denominator
needed when summing modes below the stationary endpoint.  It is not a
bound for the nearest stationary modes, which remain in the separate
second-derivative endpoint band.
The compact lower-cutoff bound and its extension to zero are now formal in
`OscillatoryGammaLowerTail`.  The exact contract builds successfully (8700
jobs including cached dependencies), with only the three allowed base
axioms.  The proof in fact only needs `sigma<1`; positive `sigma` is needed
later for the upper tail, not for this lower-tail lemma.

Combining (8.22-lower) with the already formal right-tail estimate gives
the following next Gamma-replacement lemma.  For `0<sigma<1`, `c>0`,
`0<x<t/c`, integer `N>=1`, and `c*N>=2t`, put `s=sigma+i*t`.  Then

\[
 \left|\int_x^N u^{-s}e^{icu}\,du
 -c^{s-1}e^{i\pi(1-s)/2}\Gamma(1-s)\right|
 \leq\frac{2x^{1-\sigma}}{t-cx}+\frac{8N^{-\sigma}}c.
\]

Indeed the full conditional Gamma integral minus the displayed core is
the integrable lower tail on `[0,x]` plus the conditional upper tail on
`[N,infinity)`.  The latter is bounded by the existing upper-tail theorem
at `z=1-s`.  This statement concerns the hard core only.  The left
smoothing transition still needs its first-derivative gap estimate before
summing over `m`; bounding each transition just by its absolute length
would lose a factor comparable to the number of stationary modes.
For the formal conditional-limit identification, write the positive whole
Gamma value as `integral_0^1 f + B`, where `B` is the canonical limit of
`integral_1^n f`.  The two already proved convergence statements and
uniqueness of limits give this equality.  Interval additivity then gives
exactly
`whole - integral_x^N f = (B - integral_1^N f) + integral_0^x f`.
All finite-interval integrals here are genuine integrals since
`Re(z-1)=-sigma>-1`.  Only after these identities are established is the
norm bounded; no absolute integrability on the infinite ray is asserted.
Both the canonical-value and explicit-Gamma versions are now formal in
`OscillatoryGammaCoreReplacement`; their contract build exits zero (8708
jobs including cached dependencies), with only `propext`,
`Classical.choice`, and `Quot.sound` in the axiom audit.  No cutoff limit
or phase-sign hypothesis is supplied by the caller.

The final upper-cutoff passage need not prove convergence of each smoothed
Fourier mode.  Keep `t` fixed and first apply Poisson summation at each
finite integer `N`.  Subtract `N^(1-s)/(1-s)` on that finite identity,
replace the finitely many inner stationary cores by the Gamma values,
and bound every other term using the estimates uniform in `N`.  After
the remaining smoothing and nearest-endpoint bounds are supplied, this
gives a bound of the form

\[
 \left|\left(\sum_{n\leq N}n^{-s}-\frac{N^{1-s}}{1-s}\right)
       -D_K(s)-P(s)D_K(1-s)\right|
 \leq R(t)+C(t)N^{-\sigma}.
\]

Here `K`, the finite frequency split, and `C(t)` are fixed before sending
`N` to infinity.  Euler--Maclaurin identifies the limit of the single
parenthesized primal expression as `zeta(s)` for `sigma>0`, while
`C(t)*N^(-sigma)` tends to zero.  Continuity of the norm preserves the
inequality.  Thus no termwise exchange of the upper-cutoff limit with the
infinite Poisson sum, nor a separate convergence theorem for the normalized
zero mode, is necessary.  This simplification does not dispense with the
uniform smoothing and nearest-endpoint estimates in `R(t)`.

The next restricted-cutoff estimate has an explicit uniform constant.
Let `x-1<=ell<=r<=N+1`, `ell>0`, `sigma>0`, and assume that `F` is twice
continuously differentiable near `[ell,r]`, its derivative is monotone,
and `|F'|>=g>0` there.  Then the same fixed width-one cutoff satisfies

\[
 \left|\int_\ell^r w_{x,N}(u)u^{-\sigma}e^{iF(u)}\,du\right|
 \leq\frac{4(1+4C_1)\ell^{-\sigma}}g.
\]

Indeed the weighted primitive `H(v)=integral_ell^v u^(-sigma)*exp(iF(u))`
has norm at most `4*ell^(-sigma)/g` on every initial subinterval by the
already proved first-derivative theorem.  Integration by parts against
`w` leaves `w(r)H(r)-integral_ell^r w'H`; the lower boundary is zero
because `H(ell)=0`.  The right boundary costs at most one primitive
bound, and the derivative integral costs at most `4*C1` copies because
its absolute mass on a subinterval is bounded by the full transition
mass.  This proves the displayed inequality without requiring `w(r)=0`.
If `w(r)=0`, the constant improves to `16*C1`, recovering the full-support
bound already formalized.  For the lower smoothing transition use
`ell=x-1`, `r=x`, and `g=t/x-2*pi*m`; the denominator then agrees exactly
with the lower Gamma-tail harmonic gap.

For clarity, the square-root endpoint band can be chosen with a fixed,
explicit width.  Let `K=floor(sqrt(t/(2*pi)))>=6`, take `x=K+1`, and
eventually `N>=2K`.  Then

\[
 K-1+\frac1{K+1}\leq\frac{t}{2\pi(K+1)}<K+1,
 \qquad K\leq\frac{t}{2\pi K}<K+2+\frac1K.
\]

Keep the five indices `m=K-1,...,K+3` in the endpoint band.  In particular
`K-1` cannot be thrown into a unit-gap lower-tail bound: at the bottom of
the height cell its distance is only `1/(K+1)`.  Modes `m<=K-2` have a
unit lower-tail gap, and all `m>=K+4` are in the shifted nonstationary
sum, apart from harmless overcounting of nonnegative terms.

For every endpoint-band mode, on `[K,2K]` the phase `F=2*pi*m*u-t*log u`
satisfies `F''>=pi/2`.  The second-derivative primitive bound is
`12/sqrt(pi/2)`, uniform over every subinterval.  Transferring it to the
amplitude `w*u^(-sigma)`, with `sigma>0`, costs at most
`(4*C1+2)*K^(-sigma)`: the differentiated cutoff contributes
`4*C1*K^(-sigma)`, the power derivative at most `K^(-sigma)`, and the
right boundary at most `K^(-sigma)`.  On `[2K,N+1]`,

\[
 F'\geq2\pi(K-1)-\pi(K+1)^2/K
       =\pi(K-4-1/K)\geq\pi K/4.
\]

First-derivative primitive transfer thus bounds this part by
`64*C1*(2K)^(-sigma)/(pi*K)`, uniformly in `N`.  Each of these five
full smoothed integrals is therefore `O(K^(-sigma))`.  On the critical
line, the full Gamma terms for `m=K-1,K` also have this size, by the
prefactor correction below; retaining them in the desired dual sum costs
no more than this error.  This is a second-derivative argument, not an
absolute length estimate over the whole support interval.

At both outer endpoints the real and complex amplitudes now satisfy the exact
formal boundary conditions

\[
 A=A'=0.                                                   \tag{8.22e''''''''''}
\]

Consequently the previously proved implication `A=A'=0 -> R=0` applies
without any limiting argument, and both boundary terms in the twice-integrated
identity vanish.

The collected identity (8.22e'''') now also has its exact formal norm bound:

\[
 \lVert R'\rVert\leq
 \frac{\lVert A''\rVert}{|F'|^2}
 +\frac{3|F''|\lVert A'\rVert}{|F'|^3}
 +\frac{|F'''|\lVert A\rVert}{|F'|^3}
 +\frac{3|F''|^2\lVert A\rVert}{|F'|^4}.                 \tag{8.22e'''''''''''}
\]

The Lean statement retains absolute values on the four real coefficients,
so no sign assumption or cancellation is silently used.

For the actual Poisson phase, the full velocity chain is now formal:

\[
 F'=-\frac tu-2\pi k,qquad
 F''=\frac{t}{u^2},qquad
 F'''=-\frac{2t}{u^3}.                                    \tag{8.22e''''''''''''}
\]

Each `HasDerivAt` statement is proved for `u!=0` and passes the allowed-axiom
audit.  Thus (8.22e''''''''''') can now be instantiated with exact powers of
`t` and `u`.

That instantiation is now formal as a single object.  For each Poisson mode,
Lean defines the actual `Q`, `R`, and `R'`, and proves, away from a stationary
point,

\[
 Q(iF')=A,qquad R(iF')=Q',
\]

the derivative identity for `R`, the specialized four-term norm bound, and
the exact endpoint equalities `Q=R=0`.  Therefore every algebraic,
differentiability, and boundary hypothesis of the twice-integrated
nonstationary estimate has an explicit AFE witness.  Lean now also proves
that `A''`, `F'''`, `Q'`, and `R'` are continuous at every positive
nonstationary point.  Hence on `1<x<=N`, if `F'` has no zero in
`[x-1,N+1]`, all interval-integrability hypotheses follow internally and
the generic identity specializes without any additional analytic premise to

\[
 \left|\int_{x-1}^{N+1}A(u)e^{i\Psi_k(u)}\,du\right|
 \leq \int_{x-1}^{N+1}|R'_k(u)|\,du.                       \tag{8.22e'''''''''''''}
\]

This theorem, including the three integrability deductions and four endpoint
cancellations, passes the axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`.  The supported L1 integration and
inverse-square frequency summation are now proved as described above, so
the distant-tail estimate has no remaining continuity, integrability,
summability, or cutoff-identification premise.  This statement does not
cover the finite nonstationary band or the stationary Gamma replacements.

The discrete endpoint bookkeeping is formal.  If `beta>=0`, remove the
single integer nearest either side of `beta`.  For every `M>=0`, Lean proves

\[
 \sum_{1\leq j\leq M}
 \frac1{\beta-(\lfloor\beta\rfloor-j)}\leq H_M,
 \qquad
 \sum_{1\leq j\leq M}
 \frac1{\lfloor\beta\rfloor+1+j-\beta}\leq H_M,                 \tag{8.22f}
\]

and composes both with `H_M<=1+log M`.  The omitted nearest integer is to be
kept in the expanded stationary/endpoint band and treated by the
second-derivative argument above, not by absolute length over the whole
support interval.  It is not absorbed into (8.22f).  Thus the finite nonstationary band contributes
only the intended endpoint logarithm once (8.22d)--(8.22e) are summed.

Thus only negative modes `k=-m<0` can be stationary, at
`u=t/(2*pi*m)`.  Lean now proves both the point-membership equivalence and
the equivalent existential statement for a zero of the phase derivative.
Intersecting the point with the open support interval gives exactly

\[
  \frac{t}{2\pi(N+2)}<m<\frac{t}{2\pi(x-2)},                    \tag{8.23}
\]

up to the two constant-width transition strips.  Formula (8.19), with
`z=1-s` and `c=2*pi*m`, identifies the full positive-frequency integral as

\[
 (2\pi m)^{s-1}e^{i\pi(1-s)/2}\Gamma(1-s).                    \tag{8.24}
\]

The coefficient in (8.24) must not be declared a unit phase without a
correction.  Write
`P(s)=(2*pi)^(s-1)*exp(i*pi*(1-s)/2)*Gamma(1-s)` and use the standard
functional-equation coefficient
`chi(s)=2*(2*pi)^(s-1)*sin(pi*s/2)*Gamma(1-s)`.  Euler's sine identity gives
the exact relation

\[
 \chi(s)=(1-e^{i\pi s})P(s).
\]

On `s=1/2+i*t`, `|chi(s)|=1`, and for `t>=1`, `|P(s)|<=2` and
`|P(s)-chi(s)|<=2*exp(-pi*t)`.  Multiplying by the dual sum of length `y`
costs at most `4*exp(-pi*t)*sqrt(y)`, using
`sum_(m<=y) m^(-1/2)<=2*sqrt(y)`.  For `y<=sqrt(t)` this is absorbed by
the required `O(t^(-1/4))` remainder.  This prefactor correction is an
explicit remaining assembly obligation, not an assumed unit-norm identity
for the raw Gamma coefficient.

For the weaker formal target `zeta_critical_unitPhase_logAfe_target`, an
equally exact normalization avoids identifying this unit phase with the
theta-function multiplier.  Reflection and complex conjugation of Gamma
give, at `s=1/2+i*t`,

\[
 |\Gamma(1-s)|^2=\frac{\pi}{\cosh(\pi t)},\qquad
 |P(s)|^2=\frac{1}{1+e^{-2\pi t}}.
\]

Here the power factor has squared norm `(2*pi)^(-1)` and the exponential
factor has squared norm `exp(pi*t)`, so the signs and normalization agree
with (8.24).  In particular `P(s)!=0`.  Put `U=P(s)/|P(s)|`; then `|U|=1`
and, writing `e=exp(-2*pi*t)`,

\[
 |P(s)-U|=1-|P(s)|
 =\frac{e}{(1+e)(1+|P(s)|)}\leq e.
\]

Consequently replacing `P(s)` by `U` in the dual sum changes the error by
at most `2*sqrt(y)*exp(-2*pi*t)`.  No regularity of `U(t)` is required by
the downstream energy inequality.  This proves the required normalization
on paper without identifying `U` with `chi(s)`, and does not assert that
the raw Gamma coefficient is itself a unit phase.  The squared-norm
identity, nonvanishing, the uniform bound `|P|<=1`, and the existence of
this exponentially close unit phase are now formal in
`AFECriticalGammaPrefactor`.  Its contract build exits zero (8698 jobs
including cached dependencies), with only the three allowed base axioms.

The same phase must be used for every frequency, not chosen separately
after summation.  For every real `m>0`, multiplicativity of principal
powers of positive real numbers gives exactly

\[
 G_m:=(2\pi m)^{s-1}e^{i\pi(1-s)/2}\Gamma(1-s)
      =P(s)m^{s-1}.
\]

On the critical line `|m^(s-1)|=m^(-1/2)`, so `|G_m|<=m^(-1/2)` and the
single `U(t)` above satisfies, simultaneously for all `m>0`,

\[
 |G_m-U(t)m^{s-1}|\leq e^{-2\pi t}m^{-1/2}.
\]

For every integer `K>=0`, subtracting the finite sums, taking norms, and
using `sum_(1<=m<=K) m^(-1/2)<=2*sqrt(K)` therefore gives

\[
 \left|\sum_{m=1}^K G_m-U(t)\sum_{m=1}^K m^{s-1}\right|
 \leq 2\sqrt K\,e^{-2\pi t}.
\]

These are purely multiplicative and finite-sum deductions from the exact
Gamma norm identity; no phase regularity or additional moment estimate
is needed.  The positive-frequency norm bound and the finite-sum statement,
with `exists U` preceding `forall K`, are now formal in
`AFECriticalGammaFrequency`.  Its standalone contract build exits zero
(8706 jobs including cached dependencies).  A combined regression of the
Gamma core, prefactor, frequency, lower tail, zero mode, finite band, far
tail, and Poisson identity contracts also exits zero (8748 jobs); every
audited theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
This closes the common-phase obligation, not the remaining restricted
smoothing, nearest-endpoint, or complete weak-AFE assembly obligations.

For the explicit width-one cutoff, the stationary membership bounds use
`N+1` and `x-1` in place of `N+2` and `x-2` in (8.23).
Finite nonstationary endpoint-distance sums and the zero-mode uniform
norm bound are now formal.  The remaining quantitative assembly is to
cancel that zero-mode main term before taking the cutoff limit, replace
the stationary truncated integrals by (8.24), and apply the endpoint-band
and smoothing-transition bounds so that their total contribution is
`O(x^(-sigma) log t)+O(t^(1/2-sigma)y^(sigma-1))`.  No Poisson identity,
Gamma boundary value, or smoothing existence remains unproved.

**Verification checkpoint (2026-08-30).** One combined `lake build` of
`Test.TwoUnitTransitionIntegralContract`, `Test.AFEExplicitPlateauIntegralContract`,
`Test.AFEExplicitMellinSecondL1Contract`, `Test.AFEExplicitPoissonGapMajorantContract`,
`Test.AFEExplicitPoissonUniformIntegralContract`, `Test.AFEExplicitPoissonFarTailContract`,
and `Test.AFEExplicitPoissonIdentityContract` exited zero (8725 jobs,
including cached dependencies).  Their axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`.  These tests certify the stated local
lemmas and cutoff interface, not the complete weak AFE or an improved
zero-density certificate.

**Further verification checkpoint (2026-08-30).** The combined build of
`Test.AFEExplicitPoissonZeroModeContract`,
`Test.OscillatoryGammaLowerTailContract`,
`Test.AFEExplicitPoissonFiniteBandContract`,
`Test.AFEExplicitPoissonFarTailContract`, and
`Test.AFEExplicitPoissonIdentityContract` exits zero (8729 jobs, including
cached dependencies).  All displayed theorem audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.  The remaining work is the
stationary Gamma replacement, the restricted smoothing/nearest-endpoint
bounds, the combined upper-cutoff limit, and the exact unit-phase
normalization.  No improved density certificate or forcing integration is
claimed by this checkpoint.

## 9. Primary sources

- J. B. Conrey, *More than two fifths of the zeros of the Riemann zeta
  function are on the critical line*, J. reine angew. Math. 399 (1989),
  1--26, DOI `10.1515/crll.1989.399.1`.  Theorem 2 and equation (50) are the
  exact mean-square statements used in Sections 3 and 5.
- J.-M. Deshouillers and H. Iwaniec, *Power mean-values for Dirichlet's
  polynomials and the Riemann zeta-function, II*, Acta Arith. 43 (1984),
  305--312, DOI `10.4064/aa-43-3-305-312`.  This is the spectral large-values
  input used inside Conrey's proof of the `theta<4/7` range.
- E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the Riemann
  Zeta-function*, second edition, Oxford University Press, 1986, Theorems
  4.13 and 4.15.  Theorem 4.13 supplies the logarithmic AFE (8.9)--(8.10);
  Theorem 4.15 removes the extra logarithm but is not needed here.
