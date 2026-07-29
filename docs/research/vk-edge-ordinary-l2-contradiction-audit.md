# VK-edge ordinary L2 contradiction audit

## New lower endpoint

For a hypothetical nontrivial zero

\[
\rho=\beta+i\gamma,\qquad \frac12<\beta<1,
\]

the formal endpoint

`exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt`

selects a missing odd harmonic `k` and an explicit constant

\[
c_{\varepsilon,\rho,k}>0
\]

such that, for every sufficiently large `Y`,

\[
\int_{\log Y}^{(1+\varepsilon)\log Y}
  |\rho|^2 e^{-2\beta y}
  \bigl(\psi(e^y)-e^y\bigr)^2\,dy
>
c_{\varepsilon,\rho,k}
\sqrt{m_\varepsilon(Y)} ,
\]

where

\[
m_\varepsilon(Y)=
\frac{\log Y}
 {q_\varepsilon-d_\varepsilon}.
\]

Thus the right side is an explicit positive constant times
`\sqrt{\log Y}`.

## Comparison with the current unconditional upper bound

The strongest unconditional Chebyshev-error theorem currently proved in the
repository is

\[
|\psi(x)-x|
\le Cx\exp(-c\sqrt{\log x})
\]

for sufficiently large `x`.

After `x = exp y` and normalization at a hypothetical zero of real part
`\beta`, this only gives

\[
|F_\rho(y)|
\le C|\rho|
\exp\!\left((1-\beta)y-c\sqrt y\right).
\]

For every fixed `\beta<1`, the positive linear term
`(1-\beta)y` eventually dominates `c sqrt y`. Squaring and integrating over
an epsilon window therefore gives an upper estimate that grows
exponentially in `log Y`. It is vastly larger than the new
`sqrt(log Y)` lower bound.

There is no contradiction.

The same exponent obstruction remains if the classical
de la Vallee Poussin remainder is replaced by a Vinogradov--Korobov
subexponential remainder. Any bound of the shape

\[
|\psi(x)-x|\le x\exp(-o(\log x))
\]

still leaves the normalized factor
`\exp((1-\beta)y-o(y))`, which grows exponentially for fixed
`\beta<1`.

## What would prove RH

A genuine contradiction argument would require an unconditional upper bound
on the same local moment that is smaller than the forced lower bound for
every `\beta>1/2`. For example, a theorem of the schematic form

\[
\int_{\log Y}^{(1+\varepsilon)\log Y}
 e^{-2\beta y}|\psi(e^y)-e^y|^2\,dy
=o(\sqrt{\log Y})
\]

for every fixed `\beta>1/2` would contradict the new endpoint. It would
exclude every zero to the right of the critical line; functional-equation
symmetry would then imply RH.

No such unconditional upper bound is available in the repository or in the
classical estimates used by this project. Producing it uniformly for all
`\beta>1/2` is already RH-strength information, not a routine consequence
of Carlson zero density.

## Next independent milestone

The ordinary L2 lower bound is enough to replace the previous qualitative
"positive measure" statement by a quantitative energy statement. It does
not by itself give a fixed proportion of the window on which the error is
large.

The next non-circular route is:

1. prove a compatible local fourth-moment upper bound;
2. apply a Paley--Zygmund argument to obtain an explicit lower bound for the
   logarithmic measure of the large-value set;
3. compare that quantitative abundance with any independently proved
   upper-density restriction.

The hard missing input is step 1. A crude pointwise PNT estimate is too large,
and Carlson counts zeros rather than directly bounding this fourth moment.
