# Full moving complementary-zero energy

## What this checkpoint closes

The dynamic packet extraction API previously accepted an arbitrary finite
bucket set `K`.  Consequently its "full moving energy" only meant the energy
inside those inspected buckets; it was not yet identified with every
finite-height zero outside the selected set `S`.

This checkpoint defines

\[
K_{S,T}
=
\left\{
\left\lfloor |\Im \rho| \right\rfloor:
\rho\in Z(T)\setminus S
\right\}.
\]

It proves that each dynamic unit packet is exactly one floor fiber of
`Z(T) \ S`.  Fiberwise summation then gives the exact identity

\[
P_{S,T,K_{S,T}}(y)
=
e^{-\beta y}
\sum_{\rho\in Z(T)\setminus S}
m(\rho)\frac{e^{\rho y}}{\rho}.
\]

There is therefore no uninspected finite-height zero term and no duplicated
zero term in the canonical full-bucket energy.

## Analytic transfer

Let `R` be the concrete no-jump normalized explicit-formula remainder.  It
splits exactly as

\[
R = Q + A + C,
\]

where `Q` is the complete complementary-zero contribution, `A` is the
finite-height approximation error, and `C` contains the closed elementary
terms.  On a forward logarithmic window, the module proves

\[
\int_0^L w_m(t)|R(a+t)|^2\,dt
\le
3\int_0^L w_m(t)|Q(a+t)|^2\,dt
+3\left(\eta^2+B_{\rm closed}(a)^2\right)
\]

whenever `A` is uniformly bounded by `eta`.  Equivalently, every lower bound
`R0` for the left side forces

\[
\frac{R_0}{3}
-\eta^2-B_{\rm closed}(a)^2
\le
\int_0^L w_m(t)|Q(a+t)|^2\,dt.
\]

The existing uniform good-height theorem supplies the approximation bound
for every sufficiently late fixed logarithmic window.  Thus the remaining
analytic input is now precisely a lower bound for the true normalized
remainder energy.

## Exact boundary

This does not prove that the true remainder energy is large.  It also does
not yet combine the transfer with maximal-layer absorption repeatedly.
The next mathematical steps are:

1. derive a quantitative lower bound for the concrete normalized remainder
   from an off-critical-line zero or from the already formalized local
   oscillation detector;
2. feed that lower bound into the canonical full-bucket transfer;
3. combine with maximal-layer absorption and a duplicate-free iteration;
4. compare the resulting distinct zero packets with a zero-density upper
   bound.

No zero-density contradiction, zero exclusion, RH, or unconditional
square-root PNT bound is claimed.
