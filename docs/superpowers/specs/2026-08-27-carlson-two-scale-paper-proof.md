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

Also `|c_U(m)|<=d(m)`.  For every fixed `R>2`, split the divisor pairs
`m=uv` according as `u<=Y_0` or `u>Y_0`.  In the first range, sum
`v>Y_0/u` by the integral test and then sum `u^(-1)`; in the second range,
sum `v>=1` and use the tail of `sum u^(-R)`.  This proves

\[
 \sum_{m>Y_0}d(m)m^{-R}
 \ll_R Y_0^{1-R}(1+\log Y_0),                              \tag{4.2}
\]

and therefore, uniformly in `t`,

\[
 |F_U(R+it)|\ll_R U^{a(1-R)}\log U.                        \tag{4.3}
\]

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
 \ll \Delta U^{2a(1-R)}(\log U)^2.                        \tag{5.4}
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
Gaussian section in the strip parameter has now also been formalized; this
is the pointwise input, but not yet the dominated `L^2` difference-quotient
argument needed for `Lp C 2 volume`-valued analyticity.  Cauchy's derivative
estimate has additionally converted the concrete degree-ten square-growth
bound for the pole-free error on `1/2 <= Re(s) <= 4` into a degree-twenty
square-growth bound for its derivative on the fixed inner strip
`7/12 <= Re(s) <= 47/12` (the earlier `2/3`-left-edge statement is retained
as a corollary); this reaches the shifted contour line
`x_0=2/3-1/log U` once `log U >= 12` and is sufficient for the next Gaussian derivative
membership step.  The Gaussian section formed from this concrete derivative
has now been proved to belong to `L^2(R)` on that inner strip.  The companion
linear-times-error summand has now also been proved to belong to `L^2(R)`,
with its explicit degree-twelve polynomial majorant.  Their exact pointwise
sum identity has been formalized and the full displayed derivative function
has been proved to belong to `L^2(R)` on the inner strip.  The dominated
difference-quotient passage in `Lp` remains; hence this still does not by
itself prove `Lp`-valued analyticity.  A general functional-analytic bridge
has now been formalized: convergence to zero of the integral of the squared
pointwise slope error implies the corresponding `MemLp.toLp` family has the
expected complex derivative.  Thus the remaining analyticity gate is no
longer `Lp` algebra; it is precisely the dominated-convergence estimate for
that scalar squared slope error.  The filter-form dominated-convergence
step itself has also been formalized: eventual measurability, domination by
an explicit integrable scalar function, and the already proved pointwise
derivative imply the required integral limit.  Consequently the remaining
analyticity gate is now exactly the construction of a single neighborhood-
uniform polynomial-times-Gaussian majorant for the concrete slope errors.
The general complex mean-value reduction for this last step is now also
formalized: a closed-ball derivative-square bound `B(t)` implies the squared
slope error is at most `4*B(t)`.  Thus it is enough to produce an integrable
closed-ball-uniform majorant for the already defined concrete derivative
section.  The intended degree-twenty polynomial times half-rate Gaussian
majorant, with the exact vertical-center shift, has now been defined and
proved integrable for every positive Gaussian width.  The genuinely concrete
uniform inequality is now also formalized on every radius-`1/48` closed ball
whose center satisfies `29/48 <= Re(z) <= 187/48`: the exact derivative
section is bounded by one such center-shifted majorant throughout the ball.
The ball lies in the derivative-growth strip
`7/12 <= Re(s) <= 47/12`, and the imaginary displacement consumes only half
of the Gaussian decay.  What remains at this gate is to feed this bound into
the already formalized mean-value and dominated-convergence interfaces,
including the concrete measurability and pointwise derivative obligations;
the bound by itself is not recorded as `Lp` analyticity.
The paper proof
leaves the following concrete Lean lemmas, none of which may be replaced by
a final density axiom:

1. Conrey's Gaussian mean-square theorem in the `P(u)=u`, `Q=1`, `R=0`
   specialization, including its uniformity in the local center;
2. for the first unconditional formal target `delta=1/20`, the
   `Lp C 2 volume`-valued analyticity on the already controlled strip
   `1/2 <= Re(s) <= 4`, its boundary norm estimates, and the finite Gaussian
   covering argument; extending the same package to `R=1000` is an optional
   strengthening to `delta=5/64` rather than a gate to a power saving;
3. the dyadic assembly of those inputs into the unconditional
   `N(2/3,T)` certificate and its connection to the forcing chain.

Until all three remaining items are proved in Lean without new mathematical
axioms, the repository-level improved density certificate remains conditional even
though the paper proof above is unconditional modulo the cited published
Conrey theorem.

## 9. Primary sources

- J. B. Conrey, *More than two fifths of the zeros of the Riemann zeta
  function are on the critical line*, J. reine angew. Math. 399 (1989),
  1--26, DOI `10.1515/crll.1989.399.1`.  Theorem 2 and equation (50) are the
  exact mean-square statements used in Sections 3 and 5.
- J.-M. Deshouillers and H. Iwaniec, *Power mean-values for Dirichlet's
  polynomials and the Riemann zeta-function, II*, Acta Arith. 43 (1984),
  305--312, DOI `10.4064/aa-43-3-305-312`.  This is the spectral large-values
  input used inside Conrey's proof of the `theta<4/7` range.
