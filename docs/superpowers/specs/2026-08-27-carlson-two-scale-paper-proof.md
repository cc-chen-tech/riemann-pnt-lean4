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
is the following standard lemma.  If a finite Dirichlet polynomial `M` has
support at most `Y`, coefficient one at `n=1`, coefficients bounded by one,
and `|zeta(s)M(s)-1|<=1/3` on `Re s=4`, then the regularized detector
`(s-1)^2(1-(zeta(s)M(s)-1)^2)` has polynomial growth
`O(Y^2(|t|+3)^10)` in the fixed Jensen disks centered on `Re s=4`.
Jensen gives `O(log(Y(|t|+3)))` local divisor mass.  A radius-pigeonhole
argument selects a zero-free horizontal side, and the zero-removed analytic
factor plus its principal parts give `O((log(Y(|t|+3)))^2)` variation there.
This proof uses no special formula for the coefficients beyond the four
hypotheses just listed.  The quantitative `1/3` bound makes the detector
uniformly bounded away from zero at the Jensen center; mere nonvanishing
would not suffice for the stated logarithmic majorant.  The lemma is exactly
the proof already formalized for the
sharp Mobius mollifier in `CarlsonDetectorGrowth.lean`, with its sole
mollifier norm estimate replaced by `|M(s)|<=Y` on `Re s>=0` and its
far-right lower bound replaced by the assumed error bound.  The two-scale
mollifier satisfies all four hypotheses.

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
 \frac{467}{576}-q_*=rac{409373}{719640000}>0,
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

The paper proof reduces the remaining formal work to the following concrete
lemmas, none of which may be replaced by a final-density axiom:

1. a finite coefficient-family mollifier and detector, with the two-scale
   identity (2.1) and coefficient cancellation (4.1);
2. Conrey's Gaussian mean-square theorem in the `P(u)=u`, `Q=1`, `R=0`
   specialization, including its uniformity in the local center;
3. the pole-free `L^2(R)`-valued three-lines lemma (5.3) and the finite
   Gaussian covering argument;
4. the coefficient-generic fixed-right Carlson contour lemma stated in
   Section 6.

The arithmetic and exponent identities are already formalized.  Until all
four analytic items are proved in Lean without new mathematical axioms, the
repository-level improved density certificate remains conditional even
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
